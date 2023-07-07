From mathcomp Require Export ssreflect.
Require Export Ensembles Image.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Global Notation "[set  x | F ]" := (fun x => F)(at level 30).
Global Notation "x \in X" := (In _ X x)(at level 30) .
Global Notation "{set  T }" := (Ensemble T)(at level 10).

Class lattice := Lattice {
  base : Type;
  meet : base -> base -> base;
  join : base -> base -> base;
  meetC : forall a b, meet a b = meet b a;
  joinC : forall a b, join a b = join b a;
  meetA : forall a b c, meet a (meet b c) = meet (meet a b) c;
  joinA : forall a b c, join a (join b c) = join (join a b) c;
  joinK : forall a b, meet a (join a b) = a;
  meetK : forall a b, join a (meet a b) = a;
  le := fun a b => meet a b = a;
}.

Coercion lattice_type (L : lattice) :=
  let: Lattice T _ _ _ _ _ _ _ _  := L in T.

Infix "≺" := le(at level 40).

Section theorem.
  Variable L : lattice.

  Lemma refl a :
    a ≺ a.
  Proof.
    unfold le.
    move : (joinK a (meet a a)).
    rewrite meetK; auto.
  Qed.

  Lemma trans a b c :
    a ≺ b -> b ≺ c -> a ≺ c.
  Proof.
    unfold le => ab bc.
    have H : (meet a (meet b c) = a). {
      rewrite bc; auto.
    }
    rewrite meetA in H.
    rewrite ab in H; auto.
  Qed.

  Lemma antisym a b :
    a ≺ b -> b ≺ a -> a = b.
  Proof.
    unfold le => ab ba.
    rewrite <- ba.
    rewrite meetC; auto.
  Qed.

    Lemma meetI a :
    meet a a = a.
  Proof.
    move : (joinK a (meet a a)).
    rewrite meetK; auto.
  Qed.

  Lemma joinI a :
    join a a = a.
  Proof.
    move : (meetK a (join a a)).
    rewrite joinK; auto.
  Qed.

  Lemma lowb' a b :
    meet a b ≺ a /\ meet a b ≺ b.
  Proof.
    split; unfold le.
    - rewrite (meetC (meet a b) a).
      rewrite meetA.
      move : (refl a).
      move => -> //=.
    - rewrite <- meetA.
      move : (refl b).
      move => -> //=.
  Qed.

  Lemma inf' a b :
    forall c, c ≺ a -> c ≺ b -> c ≺ meet a b.
  Proof.
    unfold le => c Ha  Hb.
    rewrite meetA Ha Hb; auto.
  Qed.

  Lemma inf_uni a b c :
    c ≺ a -> c ≺ b -> (forall d, d ≺ a -> d ≺ b -> d ≺ c) -> meet a b = c.
  Proof.
    move => Ha Hb H.
    move : (lowb' a b) => [Ha' Hb'].
    move : (inf' Ha Hb) => H'.
    apply antisym; auto.
  Qed.

  Lemma upb' a b :
    a ≺ join a b /\ b ≺ join a b.
  Proof.
    split; unfold le.
    - apply  (joinK a b).
    - rewrite (joinC a b).
      apply (joinK b a).
  Qed.


  Lemma sup' a b :
    forall c, a ≺ c -> b ≺ c -> join a b ≺ c.
  Proof.
    unfold le => c Ha  Hb.
    move : (meetK c a).
    rewrite (meetC c a).
    rewrite Ha => Ha'.
    move : (meetK c b).
    rewrite (meetC c b).
    rewrite Hb => Hb'.
    have : join (join c a) (join c b) = c. {
      rewrite Ha' Hb' joinI; auto.
    }
    rewrite joinA.
    rewrite <- (joinA c a c).
    rewrite (joinC a c).
    rewrite joinA joinI.
    rewrite <- joinA.
    rewrite (joinC c _).
    move => <-.
    apply joinK.
  Qed.

  Lemma sup_uni a b c :
    a ≺ c -> b ≺ c -> (forall d, a ≺ d -> b ≺ d -> c ≺ d) -> join a b = c.
  Proof.
    move => Ha Hb H.
    move : (upb' a b) => [Ha' Hb'].
    move : (sup' Ha Hb) => H'.
    apply antisym; auto.
  Qed.


End theorem.



Class complat := CompLat {
  lat : lattice;
  sup : Ensemble lat -> lat;
  inf : Ensemble lat -> lat;
  is_upb : forall (A : Ensemble lat) a, a \in A -> a ≺ (sup A);
  is_sup : forall (A : Ensemble lat) a,
           (forall b, b \in A -> b ≺ a) -> (sup A) ≺ a;
  is_lowb : forall (A : Ensemble lat) a, a \in A -> (inf A) ≺ a;
  is_inf : forall (A : Ensemble lat) a,
           (forall b, b \in A -> a ≺ b) -> a ≺ (inf A);
  bot := inf (Full_set lat);
  top := sup (Full_set lat)
}.

Coercion complat_type (L : complat) :=
  let: CompLat L' _ _ _ _ _ _ := L in  L'.

Notation "⊥" := bot.
Notation "⊤" := top.



Section defs.



  Definition bigcup {T} (X : {set {set T}}) : {set T} :=
    fun x => exists I, I \in X /\ x \in I.

  Definition bigcap {T} (X : {set {set T}}) : {set T}:=
    fun x => forall I, I \in X -> x \in I.

  Definition mono {L1 L2 : lattice}(f : L1 -> L2) :=
    forall a b, a ≺ b -> f a ≺ f b.

  Definition directed  {L : lattice}(X : {set L}) :=
    forall x y, x \in X  -> y \in X -> exists z, z \in X /\ x ≺ z /\ y ≺ z.

  Definition directed'  {L : lattice}(X : {set L}) :=
    (forall (Y : {set L}), Included _ Y  X -> exists y, y \in X /\ (forall x, x \in Y -> x ≺ y)).


  Definition continuous  {L : complat}(f : L -> L) :=
      forall X : {set L}, directed X -> f (sup X) = sup (Im _ _ X f).


  Definition lfp  {L : lattice}(f : L -> L) a :=
    f a = a /\ forall b, f b = b -> a ≺ b.

  Definition gfp  {L : lattice}(f : L -> L) a :=
    f a = a /\ forall b, f b = b -> b ≺ a.



End defs.

Section proposition1_1_5.
  Variable L : complat.


  Variable X X' : {set L}.
  Hypotheses H : Included _ X X'.

  Theorem inf_antimono :
    inf X' ≺ inf X.
  Proof.
    apply is_inf => b Hb.
    apply is_lowb; auto.
  Qed.

  Theorem sup_mono :
    sup X ≺ sup X'.
  Proof.
    apply is_sup => b Hb.
    apply is_upb; auto.
  Qed.

  Theorem inf_le_sup :
    X <> (Empty_set _) -> inf X ≺ sup X.
  Proof.
    move /not_empty_Inhabited => HX.
    inversion HX.
    eapply trans with x.
    - apply is_lowb; auto.
    - apply is_upb; auto.
  Qed.

End proposition1_1_5.




Section fixpoint.
  Variable L : complat.


  Lemma tarski_lfp (f : L -> L) (Hf : mono f):
    lfp f (inf (fun x => f x ≺ x)).
  Proof.
    remember (fun x => f x ≺ x) as G.
    remember (inf G) as g.
    have HG : inf G \in G. {
      subst.
      apply is_inf => y Hy.
      apply trans with (f y); auto.
      apply Hf.
      apply is_lowb; auto.
    }
    have Hg : f g ≺ g by subst.
    split.
    - subst g G; apply antisym; auto.
      apply is_lowb; simpl.
      apply Hf; auto.
    - move => b Hb.
      subst g G.
      apply is_lowb.
      unfold In.
      rewrite Hb.
      apply refl.
  Qed.


  Lemma tarski_lfp_gg f (Hf : mono f) :
    inf (fun x => f x ≺ x) = inf (fun x => f x = x).
  Proof.
    remember ([set x | f x ≺ x]) as G.
    remember (inf G) as g.
    have : f g = g /\ forall b : L, f b = b -> g ≺ b. {
      move : (tarski_lfp Hf); case; subst G g; auto.
    }
    move => [H1 H2].
    apply antisym.
    - apply is_inf => b; auto.
    - apply is_lowb; auto.
  Qed.

  Lemma tarski_gfp (f : L -> L) (Hf : mono f):
    gfp f (sup (fun x => x ≺ f x)).
  Proof.
    remember (fun x => x ≺ f x) as G.
    remember (sup G) as g.
    have HG : g \in G. {
      subst.
      unfold In.
      apply is_sup => b Hb.
      apply trans with (f b); auto.
      apply Hf.
      apply is_upb; auto.
    }
    have Hg : g ≺ f g by subst.
    split.
    - subst g G; apply antisym; auto.
      apply is_upb.
      apply Hf; auto.
    - move => b Hb.
      subst g.
      apply is_upb.
      subst G.
      unfold In.
      rewrite  Hb.
      apply refl.
  Qed.

  Lemma tarski_gfp_gg f (Hf : mono f) :
    sup (fun x => x ≺ f x) = sup (fun x => x = f x).
  Proof.
    move : (tarski_gfp Hf) => [H1 H2].
    remember (fun x => x ≺ f x) as G.
    remember (sup G) as g.
    apply antisym.
    - subst G g.
      apply is_upb.
      unfold In; auto.
    - apply is_sup => x; auto.
  Qed.

  Lemma sup_join x y :
    sup (Couple _ x y) = join x y.
  Proof.
    apply antisym.
    - move : (upb' x y) => [Hx Hy].
      apply is_sup => z.
      case; auto.
    - apply sup'; apply is_upb; constructor.
  Qed.

  Lemma counti_mono f :
    continuous f -> mono f.
  Proof.
    unfold continuous, mono => H a b Hab.
    pose AB := (Couple _ a b).
    have HAB : directed AB. {
      move => x y Hx Hy.
      move : (upb' x y) => [H1 H2].
      exists (join x y); repeat split; auto.

      inversion Hx; inversion Hy; subst x y; unfold AB.
      - rewrite joinI.
        apply Couple_l.
      - rewrite <- Hab.
        rewrite joinC meetC meetK.
        constructor.
      - rewrite <- Hab, meetC, meetK; constructor.
      - rewrite joinI; constructor.
    }
    move /H : HAB.
    simpl.
    have : Im L L AB f = (Couple _ (f a) (f b)) . {
      apply Extensionality_Ensembles; split => x.
      - move => H0.
        inversion H0; subst.
        inversion H1; subst; constructor.
      - case; econstructor; auto; constructor.
    }
    move => ->.
    repeat rewrite sup_join.
    have : join a b = b. {
      rewrite <- Hab.
      rewrite meetC joinC meetK; auto.
    }
    repeat move => ->.
    move : (upb' (f a) (f b)); case; auto.
  Qed.

  Lemma bot_min (X : L) : ⊥ ≺ X.
  Proof.
    apply is_lowb; constructor.

  Qed.

  Lemma top_max (X : L) : X ≺ ⊤.
  Proof.
    apply is_upb; constructor.
  Qed.


End fixpoint.

Section kleene.

  Variable L : complat.


  Fixpoint pow (f : L -> L) (n : nat) : L -> L :=
    fun X => match n with
    | 0 => X
    | S n' => f (pow f (n') X)
    end.

  Definition chain (f : L -> L) : {set L} :=
    fun X => exists n, X = pow f n ⊥.

  Definition klfp f := sup (chain f).

  Lemma powS f (Hf : mono f) n :
    pow f n ⊥ ≺ pow f (n + 1) ⊥.
  Proof.
    induction n.
    - apply /bot_min.
    - apply Hf; auto.
  Qed.

  Lemma powLe f (Hf : mono f) n m :
    pow f n ⊥ ≺ pow f (n + m) ⊥.
  Proof.
    induction m.
    - rewrite PeanoNat.Nat.add_0_r.
      apply refl.
    - apply trans with (pow f (n + m) ⊥); auto.
      rewrite PeanoNat.Nat.add_succ_r.
      rewrite <- PeanoNat.Nat.add_1_r.
      apply powS; auto.
    Qed.

  Lemma dir_chain f (Hf : mono f) :
    directed (chain f).
  Proof.
    move => x y.
    move  => [n ->] [m ->].
    exists (pow f (n + m) ⊥); repeat split.
    - exists (n + m); auto.
    - apply powLe; auto.
    - rewrite PeanoNat.Nat.add_comm.
      apply powLe; auto.
  Qed.


  Theorem kleene  (f : L -> L):
    continuous f -> lfp f (klfp f).
  Proof.
    unfold continuous.
    move => Hc.
    move : (counti_mono Hc) => Hf.
    move : (Hc _ (dir_chain Hf)) => Hd; clear Hc.
    split.
    { unfold klfp.
      apply antisym.
      - rewrite Hd.
        apply is_sup.
        move => x H.
        inversion H; subst.
        (* move => x [y [m ->]  ]. *)
        apply is_upb.
        inversion H0; subst.
        exists (1 + x); auto.
      - apply is_sup => x [n ->].
        apply trans with (f (pow f n ⊥)).
        - move : (powS Hf n).
          rewrite PeanoNat.Nat.add_comm; auto.
        - apply Hf.
          apply is_upb.
          exists n; auto.
    }
    {
      move => x Hx.
      unfold klfp.
      apply is_sup => y [n Hn].
      subst y.
      induction n.
      - apply bot_min.
      - rewrite <- Hx.
        apply Hf; auto.
    }
  Qed.

End kleene.


Arguments Union {U}.
Arguments Intersection {U}.

Section powlat.




  Instance powlat (T : Type): lattice.
  Proof.
    eapply (@Lattice
      ( (Ensemble T))
      Intersection
      Union
      (Intersection_commutative _)
      (Union_commutative _)
    ); intros.
    - apply Extensionality_Ensembles; split => x;
        inversion 1; subst.
        inversion H1; subst; repeat constructor; auto.
        inversion H0; subst; repeat constructor; auto.
    - rewrite Union_associative; auto.
    - apply Extensionality_Ensembles; split => x.
      inversion 1; subst; auto.
      move => Ha; repeat constructor; auto.
    - apply Extensionality_Ensembles; split => x.
      inversion 1; subst; auto.
      inversion H0; auto.
      move => Ha; constructor; auto.
  Defined.

  Canonical  powlat.

  Lemma le_subset {T : Type} (A B : powlat T) :
    A ≺ B <-> Included _ A B.
  Proof.
    unfold le, meet, powlat.
    split.
    - move => <- x.
      inversion 1; auto.
    - move => H.
      apply Extensionality_Ensembles; split => x.
      inversion 1; auto.
      move => Hx; constructor; auto.
  Qed.


  Instance powcomplat (T : Type) : complat.
  Proof.
    pose L := powlat T.
    pose sup_ := fun A : {set L} => bigcup A.
    pose inf_ := fun A : {set L} => bigcap A.
    eapply (@CompLat L sup_ inf_).
    - move => A a Ha.
      apply le_subset => i Hi.
      unfold sup_.
      exists a; auto.
    - move => A a H.
      apply le_subset => x [i [Ai xi]].
      move /H : Ai.
      move /le_subset; apply; auto.
    - move => A a Ha.
      apply le_subset => i; auto.
    - move => A a H.
      apply le_subset => x xa i iA.
      move /H : iA.
      move /le_subset; apply; auto.
  Defined.

  Canonical powcomplat.

End powlat.

Section prdlat.

  Instance prodlat (T T': complat)  : lattice.
  Proof.
    pose meet_ := fun (X1 X2 : T * T') => match X1, X2 with
      | (x1,y1), (x2,y2) => ((meet x1 x2), (meet y1 y2))
      end.
    pose join_ := fun (X1 X2 : T * T') => match X1, X2 with
      | (x1,y1), (x2,y2) => ((join x1 x2), (join y1 y2))
      end.
    eapply (Lattice (meet := meet_) (join := join_));
    intros; destruct a, b; try destruct c ; simpl; auto.
    - rewrite (meetC l1 l) (meetC l0 l2); auto.
    - rewrite (joinC l1 l) (joinC l0 l2); auto.
    - rewrite (meetA l l1 l3) (meetA l0 l2 l4); auto.
    - rewrite (joinA l l1 l3) (joinA l0 l2 l4); auto.
    - rewrite (joinK l l1) (joinK l0 l2); auto.
    - rewrite (meetK l l1) (meetK l0 l2); auto.
  Defined.

  Instance prodcomplat (T T': complat)  : complat.
  Proof.
    pose fst  : {set (T * T')} -> {set T} :=
      fun X => [set x1 | exists x2, (x1,x2) \in X].
    pose snd : {set (T * T')} -> {set T'} :=
      fun X => [set x2 | exists x1, (x1,x2) \in X].
    pose sup_ : {set (T * T')} -> T * T':=
      fun A => (sup (fst A), sup (snd A)).
    pose inf_ : {set (T * T')} -> T * T':=
      fun A => (inf (fst A), inf (snd A)).
    eapply (@CompLat (prodlat T T')%type sup_ inf_).
    - move => A a Ha; destruct a.
      unfold le, meet, prodlat; simpl.
      congr pair; apply is_upb;
      unfold fst, snd, In.
      - exists l0; auto.
      - exists l; auto.
    - move => A [l1 l2] H.
      unfold sup_, le, meet, prodlat.
      suff : (sup (fst A) ≺ l1) /\ sup (snd A) ≺ l2. {
        case => -> ->; auto.
      }
      split; apply is_sup => a;
      unfold fst, snd, In => [[b ab]];
      apply H in ab; inversion ab; auto.
      - rewrite H1; unfold le; auto.
      - rewrite H2; unfold le; auto.
    - move => A [l1 l2] Ha.
      unfold inf_.
      congr pair; apply is_lowb; unfold fst, snd, In.
      - exists l2; auto.
      - exists l1; auto.
    - move => A [l1 l2] H.
      unfold inf_.
      congr pair; apply is_inf; unfold fst, snd, In;
      move => a [b ab]; apply H in ab; inversion ab.
      - rewrite H1; unfold le; auto.
      - rewrite H2; unfold le; auto.
  Defined.

  Canonical prodlat.
  Canonical prodcomplat.

End prdlat.

Section funclat.

Require Import FunctionalExtensionality.

Instance funclat (T : Type) (L : lattice)  : lattice.
Proof.
  pose meet_ := fun (f g : T -> L) => fun x => meet (f x) (g x).
  pose join_ := fun (f g : T -> L) => fun x => join (f x) (g x).
  eapply (Lattice (meet := meet_) (join := join_)) => a b; try (move => c);
  unfold meet_, join_; apply functional_extensionality => x.
  - apply meetC.
  - apply joinC.
  - apply meetA.
  - apply joinA.
  - apply joinK.
  - apply meetK.
Defined.

Canonical funclat.

Theorem funclat_le {T L} (f g : funclat T L) :
  (forall x, f x ≺ g x) <-> f ≺ g.
Proof.
  split => H.
  - unfold le, meet => /=.
    apply functional_extensionality => x.
    apply H; auto.
  - unfold le.
    unfold le, meet in H.
    simpl in H.
    apply equal_f; auto.
Qed.


Instance funccomplat (T : Type) (L : complat) : complat.
Proof.
  pose sup_ := fun (G : {set (funclat T L)}) x =>
    sup (Im _ _ G ((fun f   =>  f x)) ).
  pose inf_ := fun (G : {set (funclat T L)}) x =>
    inf (Im _ _ G ((fun f   =>  f x)) ).
  eapply (@CompLat (funclat T L) sup_ inf_) => A a H;
  unfold sup_, inf_ => /=; apply funclat_le => x.
  - apply is_upb. econstructor; auto; auto.
  - apply is_sup => y Hy.
    inversion_clear Hy; subst.
    apply funclat_le; auto.
  - apply is_lowb. econstructor; auto; auto.
  - apply is_inf => y Hy.
    inversion Hy; subst.
    apply funclat_le; auto.
Defined.


End funclat.

Module  monofunc.

Record monofunc (T : lattice) (L : lattice):= MonoFunc {
  carrier :> T -> L;
  axiom : mono carrier
}.

Instance monofunclat (T : lattice) (L : lattice) : lattice.
  pose base_ := monofunc T L.
  pose f := funclat T L.
  pose meet_ := fun x y : base_=> (@meet f) x y.
  Check (@meet f).
  eapply (@Lattice base_ (@meet f)).
  apply

Canonical funccomplat.













