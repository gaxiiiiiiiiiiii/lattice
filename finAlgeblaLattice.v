From mathcomp Require Import all_ssreflect.
Require Import Bool Nat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Class lattice := Lattice {
  base : finType;
  meet : base -> base -> base;
  join : base -> base -> base;
  meetC : forall a b, meet a b = meet b a;
  joinC : forall a b, join a b = join b a;
  meetA : forall a b c, meet a (meet b c) = meet (meet a b) c;
  joinA : forall a b c, join a (join b c) = join (join a b) c;
  joinK : forall a b, meet a (join a b) = a;
  meetK : forall a b, join a (meet a b) = a;
  le := fun a b => meet a b == a;
}.

Coercion lattice_fintype (L : lattice) :=
  let: Lattice T _ _ _ _ _ _ _ _  := L in T.

Infix "≺" := le(at level 40).

Section theorem.
  Variable L : lattice.

  Lemma refl a :
    a ≺ a.
  Proof.
    unfold le.
    move : (joinK a (meet a a)).
    rewrite meetK.
    move /eqP; auto.
  Qed.

  Lemma trans a b c :
    a ≺ b -> b ≺ c -> a ≺ c.
  Proof.
    unfold le => /eqP ab /eqP bc.
    have H : (meet a (meet b c) = a). {
      rewrite bc; auto.
    }
    rewrite meetA in H.
    rewrite ab in H.
    apply /eqP; auto.
  Qed.

  Lemma antisym a b :
    a ≺ b -> b ≺ a -> a = b.
  Proof.
    unfold le => /eqP ab /eqP ba.
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
      move /eqP => -> //=.
    - rewrite <- meetA.
      move : (refl b).
      move /eqP => -> //=.
  Qed.

  Lemma inf' a b :
    forall c, c ≺ a -> c ≺ b -> c ≺ meet a b.
  Proof.
    unfold le => c /eqP Ha /eqP Hb.
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
    - apply /eqP.
      apply  (joinK a b).
    - rewrite (joinC a b).
      apply /eqP.
      apply (joinK b a).
  Qed.


  Lemma sup' a b :
    forall c, a ≺ c -> b ≺ c -> join a b ≺ c.
  Proof.
    unfold le => c /eqP Ha /eqP Hb.
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
    apply /eqP.
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
  sup : {set lat} -> lat;
  inf : {set lat} -> lat;
  is_upb : forall (A : {set lat}) a, a \in A -> a ≺ (sup A);
  is_sup : forall (A : {set lat}) a,
           (forall b, b \in A -> b ≺ a) -> (sup A) ≺ a;
  is_lowb : forall (A : {set lat}) a, a \in A -> (inf A) ≺ a;
  is_inf : forall (A : {set lat}) a,
           (forall b, b \in A -> a ≺ b) -> a ≺ (inf A);
  bot := inf [set : lat];
  top := sup [set : lat];
}.

Coercion complat_fintype (L : complat) :=
  let: CompLat L' _ _ _ _ _ _ := L in  L'.

Notation "⊥" := bot.
Notation "⊤" := top.


Section bigop.

  Definition ups (L : complat)(X : {set L}) := [set x | [forall y, (y \in X) ==> y ≺ x]].

  Theorem ups_eq (L : complat)(F : {set {set L}}) :
    ups (\bigcup_(X in F) ([set sup X])) = ups (\bigcup_(X in F) X).
  Proof.
    apply /setP /subset_eqP /andP; split;
      apply /subsetP => x; (repeat rewrite in_set) => /forallP H;
      apply /forallP => y; apply /implyP => Hy;
      move /bigcupP : Hy => [X HX Hx]; subst.
    - apply trans with (sup X).
      * apply (is_upb Hx).
      * move : (H (sup X)); move /implyP; apply.
        apply /bigcupP.
        exists X; auto.
        apply /set1P; auto.
    - move /set1P in Hx; subst.
      apply is_sup => y Hy.
      move : (H y); move /implyP; apply.
      apply /bigcupP; exists X; auto.
  Qed.

  Theorem ups_sup (L : complat)(A : {set L}) :
    forall a, a \in ups A -> sup A ≺ a.
  Proof.
    move => a.
    rewrite in_set.
    move /forallP => H.
    apply is_sup => y Hy.
    move : (H y).
    move /implyP; apply; auto.
  Qed.



  Theorem big_assoc (L : complat)(F : {set {set L}}) :
    sup (\bigcup_(X in F) ([set sup X])) = sup (\bigcup_(X in F) X).
  Proof.
    apply antisym.
    - apply is_sup => b.
      move /bigcupP => [X HX /set1P H]; subst.
      apply is_sup => c Hc.
      apply is_upb.
      apply /bigcupP. exists X; auto.
    - apply ups_sup.
      rewrite <- (ups_eq).
      rewrite in_set.
      apply /forallP => x.
      apply /implyP => H.
      apply is_upb; auto.
  Qed.


  Definition big_join {L : complat}(A : {set L})  :=
    \big[join/⊤]_(i in A) i.

  Definition big_meet {L : complat} (A : {set L}) :=
    \big[meet/⊥]_(i in A) i.


  Axiom gen_joinA : forall {L : complat} (A : {set L}),
    big_join A = sup A.


  Axiom gen_meetA : forall {L : complat} (A : {set L}),
    big_meet A = inf A.


End bigop.

Section fixpoint.
  Variable L : complat.

  Definition mono (f : L -> L) :=
    forall a b, a ≺ b -> f a ≺ f b.

  Definition directed (X : {set L}) :=
    forall x y, x \in X  -> y \in X -> exists z, z \in X /\ x ≺ z /\ y ≺ z.

  Definition directed' (X : {set L}) :=
    (forall (Y : {set L}), Y \subset X -> exists y, y \in X /\ (forall x, x \in Y -> x ≺ y)).


  Definition countinuous (f : L -> L) :=
      forall X : {set L}, directed X -> f (sup X) = sup (\bigcup_(x in X) [set (f x)]).


  Definition lfp (f : L -> L) a :=
    f a = a /\ forall b, f b = b -> a ≺ b.

  Definition gfp (f : L -> L) a :=
    f a = a /\ forall b, f b = b -> b ≺ a.

  Lemma tarski_lfp (f : L -> L) (Hf : mono f):
    lfp f (inf [set x | f x ≺ x]).
  Proof.
    remember [set x | f x ≺ x] as G.
    remember (inf G) as g.
    have HG : inf G \in G. {
      subst.
      rewrite in_set.
      apply is_inf => y.
      rewrite in_set => Hy.
      apply trans with (f y); auto.
      apply Hf.
      apply is_lowb.
      rewrite in_set; auto.
    }
    have Hg : f g ≺ g. {
      subst.
      rewrite in_set in HG; auto.
    }
    split.
    - apply antisym; auto.
      subst g.
      apply is_lowb.
      subst G.
      rewrite in_set.
      apply Hf; auto.
    - move => b Hb.
      subst g.
      apply is_lowb.
      subst G.
      rewrite in_set Hb.
      apply refl.
  Qed.

  Lemma tarski_lfp_gg f (Hf : mono f) :
    inf [set x | f x ≺ x] = inf [set x | f x == x].
  Proof.
    move : (tarski_lfp Hf) => [H1 H2].
    remember ([set x | f x ≺ x]) as G.
    remember (inf G) as g.
    apply antisym.
    - apply is_inf => x.
      rewrite in_set => /eqP; auto.
    - apply is_lowb.
      rewrite in_set.
      apply /eqP; auto.
  Qed.

  Lemma tarski_gfp (f : L -> L) (Hf : mono f):
    gfp f (sup [set x | x ≺ f x]).
  Proof.
    remember [set x | x ≺ f x] as G.
    remember (sup G) as g.
    have HG : g \in G. {
      subst.
      rewrite in_set.
      apply is_sup => y.
      rewrite in_set => Hy.
      apply trans with (f y); auto.
      apply Hf.
      apply is_upb.
      rewrite in_set; auto.
    }
    have Hg : g ≺ f g. {
      subst.
      rewrite in_set in HG; auto.
    }
    split.
    - apply antisym; auto.
      subst g.
      apply is_upb.
      subst G.
      rewrite in_set.
      apply Hf; auto.
    - move => b Hb.
      subst g.
      apply is_upb.
      subst G.
      rewrite in_set Hb.
      apply refl.
  Qed.

  Lemma tarski_gfp_gg f (Hf : mono f) :
    sup [set x | x ≺ f x] = sup [set x | x == f x].
  Proof.
    move : (tarski_gfp Hf) => [H1 H2].
    remember ([set x | x ≺ f x]) as G.
    remember (sup G) as g.
    apply antisym.
    - subst g.
      apply is_upb.
      rewrite in_set.
      apply /eqP; auto.
    - apply is_sup => x.
      rewrite in_set => /eqP; auto.
  Qed.

  Lemma sup_join x y :
    sup [set x; y] = join x y.
  Proof.
    apply antisym.
    - move : (upb' x y) => [Hx Hy].
      apply is_sup => z.
      move /set2P; case => ->; auto.
    - apply sup'; apply is_upb; apply /set2P; auto.
  Qed.

  Lemma counti_mono f :
    countinuous f -> mono f.
  Proof.
    unfold countinuous, mono => H a b Hab.
    pose AB := [set a; b].
    have HAB : directed AB. {
      move => x y Hx Hy.
      move : (upb' x y) => [H1 H2].
      exists (join x y); repeat split; auto.
      apply /set2P.
      unfold le in Hab.
      move /set2P : Hx; case => ->;
      move /set2P : Hy; case => ->;
      [left|right|right|right];
      try (rewrite joinI; auto);
      move /eqP : Hab <-.
      - rewrite joinC meetC meetK; auto.
      - rewrite meetC meetK; auto.
    }
    move /H : HAB.
    have : \bigcup_(x in [set a; b]) [set f x] = [set (f a); (f b)]. {
      apply /setP /subset_eqP /andP; split; apply /subsetP => x.
      - move /bigcupP => [I].
        move /set2P; case => -> /set1P ->;
        apply /set2P; [left|right]; auto.
      - move /set2P; case => ->; apply /bigcupP; [exists a|exists b];
        try (apply /set2P; auto);
        apply /set1P; auto.
    }
    move => ->.
    repeat rewrite sup_join.
    have : join a b = b. {
      move /eqP : Hab <-.
      rewrite meetC joinC meetK; auto.
    }
    repeat move => ->.
    move : (upb' (f a) (f b)); case; auto.
  Qed.

  Lemma bot_min (X : L) : ⊥ ≺ X.
  Proof.
    apply is_lowb; auto.
  Qed.

  Lemma top_max (X : L) : X ≺ ⊤.
  Proof.
    apply is_upb; auto.
  Qed.


End fixpoint.

Section kleene.

  Variable L : complat.


  Fixpoint pow (f : L -> L) (n : nat) : L -> L :=
    fun X => match n with
    | 0 => X
    | S n' => f (pow f (n') X)
    end.

  Definition chain' (f : L -> L) : L -> Prop :=
    fun X => exists n, X = pow f n ⊥.

  Axiom chain : (L -> L) -> {set L}.
  Axiom chainP : forall f X, reflect (chain' f X) (X \in chain f).

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
    move /chainP => [n ->].
    move /chainP => [m ->].
    exists (pow f (n + m) ⊥); repeat split.
    - apply /chainP; exists (n + m); auto.
    - apply powLe; auto.
    - rewrite PeanoNat.Nat.add_comm.
      apply powLe; auto.
  Qed.


  Theorem kleene  (f : L -> L):
    countinuous f -> lfp f (klfp f).
  Proof.
    unfold countinuous.
    move => Hc.
    move : (counti_mono Hc) => Hf.
    move : (Hc _ (dir_chain Hf)) => Hd; clear Hc.
    split.
    { unfold klfp.
      apply antisym.
      - rewrite Hd.
        apply is_sup.
        move => x /bigcupP [y /chainP [m ->] /set1P ->].
        apply is_upb.
        apply /chainP; exists (1 + m); auto.
      - apply is_sup => x.
        move /chainP => [n ->].
        apply trans with (f (pow f n ⊥)).
        - move : (powS Hf n).
          rewrite PeanoNat.Nat.add_comm; auto.
        - apply Hf.
          apply is_upb.
          apply /chainP; exists n; auto.
    }
    {
      move => x Hx.
      unfold klfp.
      apply is_sup => y /chainP => [[n Hn]].
      subst y.
      induction n.
      - apply bot_min.
      - rewrite <- Hx.
        apply Hf; auto.
    }
  Qed.

End kleene.




Section powlat.

  Lemma setKU' {T : finType} (A B : {set T}) :
    A :&: (A :|: B) = A.
  Proof.
    rewrite setUC setKU; auto.
  Qed.

  Lemma setKI' {T : finType} (A B : {set T}) :
    A :|: (A :&: B) = A.
  Proof.
    rewrite setIC setKI; auto.
  Qed.


  Instance powlat (T : finType): lattice := {
    base := _;
    meet := @setI T;
    join := @setU T;
    meetC := @setIC T;
    joinC := @setUC T;
    meetA := @setIA T;
    joinA := @setUA T;
    joinK := @setKU' T;
    meetK := @setKI' T;
  }.

  Canonical  powlat.

  Lemma le_subset {T : finType} (A B : powlat T) :
    A ≺ B <-> A \subset B.
  Proof.
    unfold le, meet, powlat.
    split.
    - move /eqP /setIidPl; auto.
    - move /setIidPl /eqP; auto.
  Qed.


  Instance powcomplat (T : finType) : complat.
  Proof.
    pose L := powlat T.
    pose sup_ := fun A : {set {set T}} => \bigcup_(i in A) i.
    pose inf_ := fun A : {set {set T} }=> \bigcap_(i in A) i.
    eapply (@CompLat L sup_ inf_).
    - move => A a Ha.
      apply le_subset.
      apply /subsetP => i Hi.
      unfold sup_.
      apply /bigcupP.
      exists a; auto.
    - move => A a H.
      apply le_subset.
      apply /subsetP => x.
      move /bigcupP => [i Ai xi].
      move /H : Ai.
      move /le_subset /subsetP; apply; auto.
    - move => A a Ha.
      apply le_subset.
      apply /subsetP => i.
      move /bigcapP; apply; auto.
    - move => A a H.
      apply le_subset.
      apply /subsetP => x xa.
      apply /bigcapP => i iA.
      move /H : iA.
      move /le_subset /subsetP; apply; auto.
  Defined.

  Canonical powcomplat.

End powlat.

Section prolog.

  Variable T : finType.
  Notation setT := (powcomplat T).



  Lemma subset_le  (A B : {set setT}) :
    A \subset B -> sup A ≺ sup B.
  Proof.
    move /subsetP => H.
    apply is_sup => a.
    move /H => Ha.
    apply is_upb; auto.
  Qed.




  Axiom dd : forall X,
    directed X -> forall (Y : {set setT}), Y \subset X ->
    exists y, y \in X /\ (forall x, x \in Y -> x ≺ y).


  Lemma sup_mono (X Y : {set setT}) :
    X \subset Y -> sup X \subset sup Y.
  Proof.
    move => /subsetP H.
    apply /subsetP => x  /bigcupP [I HI xI].
    apply /bigcupP.
    exists I; auto.
  Qed.

  Theorem dd'(X : {set setT}) :
    (forall (Y : {set setT}), Y \subset X -> exists y, y \in X /\ (forall x, x \in Y -> x ≺ y))
    -> directed X.
  Proof.
    move => H x y Hx Hy.
    have : [set x; y] \subset X. {
      apply /subsetP => a.
      move /set2P; case => ->; auto.
    }
    move /H => [z [Hz H0]].
    exists z; repeat split; auto; apply H0; apply /set2P; [left|right]; auto.
  Qed.



  Lemma dir_sup (X : {set setT }) (HX : directed X) (A : setT) :
    A ≺ sup X <-> exists I, I \in X /\ A ≺ I.
  Proof.
    split => H; first last.
    - move : H => [I [HI HA]].
      apply /le_subset /subsetP => x Hx.
      move /le_subset /subsetP : HA => HA.
      apply HA in Hx.
      unfold sup, powcomplat.
      apply /bigcupP.
      exists I; auto.
    - unfold sup, setT in H.
      rewrite le_subset in H.
      pose  XA := [set I in X | [exists a, (a \in A) && (a \in I)]].
      have XAX : XA \subset X. { apply /subsetP => x; rewrite in_set => /andP; case; auto. }
      move : (dd HX XAX) => [I [HI AI]].
      exists I; split; auto.
      apply trans with (sup XA).
      - apply /le_subset /subsetP => a Ha.
        apply /bigcupP.
        move /subsetP /(_ a Ha) /bigcupP : H => [i Hi ai].
        exists i; auto.
        rewrite in_set.
        apply /andP; split; auto.
        apply /existsP; exists a.
        apply /andP; split; auto.
      - apply /le_subset /subsetP => a.
        move /bigcupP => [J HJ aJ].
        apply AI in HJ.
        move /le_subset /subsetP : HJ; apply; auto.
  Qed.



