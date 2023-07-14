From mathcomp Require Export ssreflect.
Require Export Ensembles Image.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation "x \in X" := (In _ X x)(at level 30) .
Notation "{set  T }" := (Ensemble T)(at level 10).
Notation "f ∘ g" := (fun x => f (g x))(at level 40).

Module lattice.

  Record ops T := Ops {
    meet_ : T -> T -> T;
    join_ : T -> T -> T;    
  }.

  Record mixin_of T (ops_ : ops T ):= Mixin {    
    meet := meet_ ops_;
    join := join_ ops_;
    meetC : forall a b, meet a b = meet b a;
    joinC : forall a b, join a b = join b a;
    meetA : forall a b c, meet a (meet b c) = meet (meet a b) c;
    joinA : forall a b c , join a (join b c) = join (join a b) c;
    joinK : forall a b, meet a (join a b) = a;
    meetK : forall a b, join a (meet a b) = a;
  }.
  Notation class_of := mixin_of (only parsing).

  Section ClassDef.

    Structure type := Pack {
      sort : Type; 
      ops_ : ops sort;  
      _ : class_of ops_
    }.

    Variables (cT : type).    
    Definition class := let: Pack _ _ c := cT return class_of (ops_ cT) in c.
    Definition opsOf := let: Pack _ p _ := cT return ops (sort cT) in p.

  
  End ClassDef.

  Module Exports.
    Coercion sort : type >-> Sortclass.
    Notation lattice := type.
    Notation latticeMixin := Mixin.
    
    Definition meet T := meet (class T).
    Definition join T := join (class T).
    Definition le (T : lattice) (x y : T) := meet x y = x.

    Lemma meetC (T : lattice) : forall (a b : T), meet a b = meet b a.
    Proof. apply meetC. Qed.
    Lemma joinC (T : lattice) : forall (a b : T), join a b = join b a.
    Proof. apply joinC. Qed.
    Lemma meetA (T : lattice) : forall (a b c : T), meet a (meet b c) = meet (meet a b) c.
    Proof. apply meetA. Qed.
    Lemma joinA (T : lattice) : forall (a b c : T), join a (join b c) = join (join a b) c.
    Proof. apply joinA. Qed.
    Lemma joinK (T : lattice) : forall (a b : T), meet a (join a b) = a.
    Proof. apply joinK. Qed.
    Lemma meetK (T : lattice) : forall (a b : T), join a (meet a b) = a.
    Proof. apply meetK. Qed.


    Notation "x ∧ y" := (meet x y)(at level 30).
    Notation "x ∨ y" := (join x y)(at level 30).   
    Notation "x ≺ y" := (le x y)(at level 40). 
   
  End Exports.

End lattice.

Export lattice.Exports.

Section latticeTheory.

 Definition mono {L1 L2 : lattice}(f : L1 -> L2) :=
    forall a b, a ≺ b -> f a ≺ f b.

  Definition antimono {L1 L2 : lattice}(f : L1 -> L2) :=
    forall a b, a ≺ b -> f b ≺ f a.  

  Definition directed  {L : lattice}(X : {set L}) :=
    forall x y, x \in X  -> y \in X -> exists z, z \in X /\ x ≺ z /\ y ≺ z.
  
  Variable L : lattice.

  Lemma refl (a : L) :
    a ≺ a.
  Proof.
    move : (joinK a (meet a a)).
    rewrite meetK; auto.
  Qed.
  

  Lemma trans (a b c : L) :
    a ≺ b -> b ≺ c -> a ≺ c.
  Proof.
    move => ab bc.
    have H : (meet a (meet b c) = a). {

      rewrite bc; auto.
    }
    rewrite meetA in H.
    rewrite ab in H; auto.
  Qed.

  Lemma antisym (a b : L) :
    a ≺ b -> b ≺ a -> a = b.
  Proof.
    move => ab ba.
    rewrite <- ba.
    rewrite meetC; auto.
  Qed.

    Lemma meetI (a : L) :
    meet a a = a.
  Proof.
    move : (joinK a (meet a a)).
    rewrite meetK; auto.
  Qed.

  Lemma joinI (a : L) :
    join a a = a.
  Proof.
    move : (meetK a (join a a)).
    rewrite joinK; auto.
  Qed.

  Lemma meet_lowb (a b : L) :
    meet a b ≺ a /\ meet a b ≺ b.
  Proof.
    split; move.
    - rewrite (meetC (meet a b) a).
      rewrite meetA.
      move : (refl a).
      move => -> //=.
    - rewrite <- meetA.
      move : (refl b).
      move => -> //=.
  Qed.

  Lemma meet_lowb_l (a b : L) :
    meet a b ≺ a.
  Proof.
    move : (meet_lowb a b) => [H _]; auto.
  Qed.

  Lemma meet_lowb_r (a b : L) :
    meet a b ≺ b.
  Proof.
    move : (meet_lowb a b) => [_ H]; auto.
  Qed.

  Lemma meet_inf (a b : L) :
    forall c, c ≺ a -> c ≺ b -> c ≺ meet a b.
  Proof.
    move => c Ha  Hb.
    unfold le.
    rewrite meetA Ha Hb; auto.
  Qed.

  Lemma inf_uni (a b c : L) :
    c ≺ a -> c ≺ b -> (forall d, d ≺ a -> d ≺ b -> d ≺ c) -> meet a b = c.
  Proof.
    move => Ha Hb H.
    move : (meet_lowb a b) => [Ha' Hb'].
    move : (meet_inf Ha Hb) => H'.
    apply antisym; auto.
  Qed.

  Lemma join_upb (a b : L) :
    a ≺ join a b /\ b ≺ join a b.
  Proof.
    split; move.
    - apply  (joinK a b).
    - rewrite (joinC a b).
      apply (joinK b a).
  Qed.

  Lemma join_upb_l (a b : L) :
    a ≺ join a b.
  Proof.
    move : (join_upb a b) => [H _]; auto.
  Qed.

  Lemma join_upb_r (a b : L) :
    b ≺ join a b.
  Proof.
    move : (join_upb a b) => [_ H]; auto.
  Qed.


  Lemma join_sup (a b : L) :
    forall c, a ≺ c -> b ≺ c -> join a b ≺ c.
  Proof.
    move => c Ha  Hb.
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

  Lemma sup_uni (a b c : L) :
    a ≺ c -> b ≺ c -> (forall d, a ≺ d -> b ≺ d -> c ≺ d) -> join a b = c.
  Proof.
    move => Ha Hb H.
    move : (join_upb a b) => [Ha' Hb'].
    move : (join_sup Ha Hb) => H'.
    apply antisym; auto.
  Qed.

  Lemma join_meet (a b : L) :
    a ≺ b <-> join a b = b.
  Proof.
    split.
    - move => <-.
      rewrite joinC.
      rewrite meetC.
      rewrite meetK; auto.
    - move => <- .
      move : (join_upb a b); case; auto.
  Qed.


  (* about operator *)

  Lemma antimono_compose_mono {L1 L2 L3 : lattice}(f : L1 -> L2)(g : L2 -> L3) :
    antimono f -> antimono g -> mono (g ∘ f).
  Proof. 
    move => Hf Hg x y H; eauto.
  Qed.

  Lemma mono_antimono_constant (f : L -> L) :
    mono f -> antimono f -> forall x y, f x = f y.
  Proof.
    move => Hm Ha x y.
    apply antisym.
    - move : (meet_lowb x y) => [low_x low_y].
      apply trans with (f (meet x y)).      
      - apply Ha; auto.
      - apply Hm; auto.      
    - move : (join_upb x y) => [up_x up_y].
      apply trans with (f (join x y)).
      - apply Hm; auto.
      - apply Ha; auto.
  Qed.


End latticeTheory.


Module distlat.

  Section ClassDef.

    Record mixin_of T (ops_ : lattice.ops T) := Mixin {
      meet_ := lattice.meet_ ops_;
      join_ := lattice.join_ ops_;      
      dist_meet_join : forall a b c, meet_ a (join_ b c) = join_ (meet_ a b) (meet_ a c);
      dist_join_meet : forall a b c, join_ a (meet_ b c) = meet_ (join_ a b) (join_ a c);
    }.

    Record class_of T (ops_ : lattice.ops T) := Class {
      base : lattice.class_of ops_;
      mixin : mixin_of ops_;
    }.

    Structure type := Pack {
      sort : Type;
      ops_ : lattice.ops sort;
      _ : class_of ops_;
    }.

    Variable (cT : type).

    Definition class := let: Pack _ _ c := cT  return class_of (ops_ cT) in c.
    Definition lattice := @lattice.Pack (sort cT) (ops_ cT) (base class).

  End ClassDef.

  Module Exports.

    Coercion base : class_of >-> lattice.class_of.
    Coercion mixin : class_of >-> mixin_of.
    Coercion sort : type >-> Sortclass.
    Coercion lattice : type >-> lattice.type.
    Canonical lattice.
    Notation distlat := type.
    Notation distlatMixin := mixin_of.    

    Definition dist_meet_join (T : distlat): forall (a b c : T), 
      a ∧ (b ∨ c) = (a ∧ b) ∨ (a ∧ c).
    Proof.  apply (dist_meet_join  (class T)). Qed.

    
    Lemma dist_join_meet (T : distlat) : forall (a b c : T),
      a ∨ (b ∧ c) = (a ∨ b) ∧ (a ∨ c).
    Proof. apply (dist_join_meet (class T)). Qed.    
  
  End Exports.

End distlat.

Export distlat.Exports.

(*************)
Module tblattice.

  Section ClassDef.

    Record mixin_of T (ops_ : lattice.ops T) := Mixin {
      top : T;
      bot : T;
      le_ := fun a b =>  lattice.meet_ ops_ a b = a;
      topP : forall a, le_ a top;
      botP : forall a, le_ bot a;
    }.

    Record class_of T (ops_ : lattice.ops T) := Class {
      base : lattice.class_of ops_;
      mixin : mixin_of ops_;
    }.

    Structure type := Pack {
      sort : Type;
      ops_ : lattice.ops sort;
      _ : class_of ops_;
    }.

    Variable (cT : type).

    Definition class := let: Pack _ _ c := cT  return class_of (ops_ cT) in c.
    Definition lattice := @lattice.Pack (sort cT) (ops_ cT) (base class).

  End ClassDef.

  Module Exports.

    Coercion base : class_of >-> lattice.class_of.
    Coercion mixin : class_of >-> mixin_of.
    Coercion sort : type >-> Sortclass.
    Coercion lattice : type >-> lattice.type.
    Canonical lattice.
    Notation tblattice := type.
    Notation tblatticeMixin := mixin_of.    
   
    Definition TOP {T} := top (class T).
    Definition BOT {T} := bot (class T).
    Notation "⊤" := TOP.
    Notation "⊥" := BOT.  

    Lemma topP (T : tblattice) (x : T) : x ≺ ⊤.
    Proof. apply topP. Qed.
    Lemma botP (T : tblattice) (x : T) : ⊥ ≺ x.
    Proof. apply botP. Qed.
  
  End Exports.

End tblattice.

Export tblattice.Exports.
(***********)

Module complat.
  Section ClassDef.

    Record mixin_of T (ops_ : lattice.ops T ):= Mixin {   
      meetc := lattice.meet_ ops_;
      joinc := lattice.join_ ops_;
      lec := fun a b => meetc a b = a;

      sup : Ensemble T -> T;
      inf : Ensemble T -> T;
      
      is_upb : forall (A : Ensemble T) a, a \in A -> lec a (sup A);
      is_sup : forall (A : Ensemble T) a,
              (forall b, b \in A -> lec b a) -> lec (sup A) a;
      is_lowb : forall (A : Ensemble T) a, a \in A -> lec (inf A)a;
      is_inf : forall (A : Ensemble T) a,
              (forall b, b \in A -> lec a b) -> lec a (inf A);    
    }.


    Record class_of T (ops_ : lattice.ops T) := Class {
      base : lattice.class_of ops_;
      mixin : mixin_of ops_
    }.

    Structure type := Pack {
      sort : Type; 
      ops_ : lattice.ops sort;  
      _ : class_of ops_
    }.

    Variables  (cT : type).
    Definition class := let: Pack _ _ c := cT return class_of (ops_ cT) in c.
    Definition lattice := @lattice.Pack (sort cT) (ops_ cT) (base class). 
    Definition tblattice : tblattice.
    Proof.
      apply  (@tblattice.Pack (sort cT) (ops_ cT)).
      constructor.
      - apply (base class).
      - pose top := @sup (sort cT)(ops_ cT) (mixin class) (Full_set (sort cT)).
        pose bot := @inf (sort cT)(ops_ cT) (mixin class) (Full_set (sort cT)).
        eapply (tblattice.Mixin (top := top) (bot := bot)) => x.
        * apply is_upb; constructor.
        * apply is_lowb; constructor.
    Defined.

  End ClassDef.  

  Module  Exports.
    Coercion base : class_of >-> lattice.class_of.
    Coercion mixin : class_of >-> mixin_of.
    Coercion sort : type >-> Sortclass.
    Coercion lattice : type >-> lattice.type.
    Coercion tblattice : type >-> tblattice.type.
    Canonical lattice.
    Canonical tblattice.
    Notation complat := type.
    Notation complatMixin := mixin_of.    

    Definition sup T := sup (class T).
    Definition inf T := inf (class T).
    Definition lec T := lec (class T).
    Definition bot {T} := @inf T (Full_set T).
    Definition top {T} := @sup T (Full_set T).    
    Notation "⊤" := top.
    Notation "⊥" := bot.    

    Lemma is_upb (T : complat) : forall (A : Ensemble T) a, a \in A -> a ≺ (sup A).
    Proof. apply is_upb. Qed.
    Lemma is_sup ( T : complat) : forall (A : Ensemble T) a,
            (forall b, b \in A -> b ≺ a) -> (sup A) ≺ a.
    Proof. apply is_sup. Qed.
    Lemma is_lowb (T : complat) : forall (A : Ensemble T) a, a \in A -> (inf A) ≺ a.
    Proof. apply is_lowb. Qed.
    Lemma is_inf (T : complat) : forall (A : Ensemble T) a,
            (forall b, b \in A -> a ≺ b) -> a ≺ (inf A).
    Proof. apply is_inf. Qed.

  End Exports.
End complat.

Export complat.Exports.

Section complatTheory.

  Definition continuous  {L : complat}(f : L -> L) :=
      forall X : {set L}, directed X -> f (sup X) = sup (Im _ _ X f).

  Definition is_lfp  {L : lattice}(f : L -> L) a :=
    f a = a /\ forall b, f b = b -> a ≺ b.

  Definition is_gfp  {L : lattice}(f : L -> L) a :=
    f a = a /\ forall b, f b = b -> b ≺ a.

  Definition lfp {L : complat}(f : L -> L) (Hf : mono f) :=
    (inf (fun x => f x ≺ x)).

  Definition gfp {L : complat}(f : L -> L) (Hf : mono f) :=
    (sup (fun x => x ≺ f x)).

  Fixpoint pow {L : complat}(f : L -> L) (n : nat) : L -> L :=
    fun X => match n with
    | 0 => X
    | S n' => f (pow f (n') X)
    end.

  Definition chain {L : complat }(f : L -> L) : {set L} :=
    fun X => exists n, X = pow f n ⊥.

  Definition klfp {L : complat}(f : L -> L) := sup (chain f).

  Variable L : complat.
  Section misc.
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
  End misc.

  (* tarski's fixpoint theorem *)

  Lemma tarski_lfp (f : L -> L) (Hf : mono f):
    is_lfp f (lfp Hf).
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


  Lemma tarski_lfp_gg (f : L -> L) (Hf : mono f) :
    inf (fun x => f x ≺ x) = inf (fun x => f x = x).
  Proof.
    remember (fun x => f x ≺ x) as G.
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
    is_gfp f (gfp Hf).
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

  Lemma tarski_gfp_gg (f : L -> L) (Hf : mono f) :
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

  Lemma sup_join (x y : L) :
    sup (Couple _ x y) = join x y.
  Proof.
    apply antisym.
    - move : (join_upb x y) => [Hx Hy].
      apply is_sup => z.
      case; auto.
    - apply join_sup; apply is_upb; constructor.
  Qed.

  Lemma counti_mono (f : L -> L) :
    continuous f -> mono f.
  Proof.
    unfold continuous, mono => H a b Hab.
    pose AB := (Couple _ a b).
    have HAB : directed AB. {
      move => x y Hx Hy.
      move : (join_upb x y) => [H1 H2].
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
    move : (join_upb (f a) (f b)); case; auto.
  Qed.

  Lemma bot_min (X : L) : ⊥ ≺ X.
  Proof.
    apply is_lowb; constructor.

  Qed.

  Lemma top_max (X : L) : X ≺ ⊤.
  Proof.
    apply is_upb; constructor.
  Qed.

  (* kleene's fixpoint theorem *)

  Lemma powS (f : L -> L) (Hf : mono f) n :
    pow f n ⊥ ≺ pow f (n + 1) ⊥.
  Proof.
    induction n.
    - apply /bot_min.
    - apply Hf; auto.
  Qed.

  Lemma powLe (f : L -> L) (Hf : mono f) n m :
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
    
  Lemma dir_chain (f : L -> L) (Hf : mono f) :
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
    continuous f -> is_lfp f (klfp f).
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

End complatTheory.  


Module bilattice.
  Section ClassDef.

    Record mixin_of T (opst opsk : lattice.ops T ):= Mixin {   
      meett := lattice.meet_ opst;
      joint := lattice.join_ opst;
      let_ := fun a b => meett a b = a;
      meetk := lattice.meet_ opsk;
      joink := lattice.join_ opsk;
      lek := fun a b => meetk a b = a;
      neg : T -> T;
      letN : forall x y, let_ x y -> let_ (neg y) (neg x);
      lekN : forall x y, lek x y -> lek (neg x) (neg y);
      NN : forall x, neg (neg x) = x;
    }.


    Record class_of T (opst opsk : lattice.ops T) := Class {
      baset : complat.class_of opst;
      basek : complat.class_of opsk;
      mixin : mixin_of opst opsk
    }.

    Structure type := Pack {
      sort : Type; 
      opst : lattice.ops sort;  
      opsk : lattice.ops sort;
      _ : class_of opst opsk
    }.

    Variables  (cT : type).
    Definition class := let: Pack _ _ _ c := cT return class_of (opst cT) (opsk cT) in c.    

    Definition complatt := @complat.Pack (sort cT) (opst cT) (baset class).
    Definition latticet := @lattice.Pack (sort cT) (opst cT) (baset class).
    Definition complatk := @complat.Pack (sort cT) (opsk cT) (basek class).
    Definition latticek := @lattice.Pack (sort cT) (opsk cT) (basek class).


    End ClassDef.
  

  Module  Exports.    
    Coercion baset : class_of >-> complat.class_of.
    Coercion mixin : class_of >-> mixin_of.
    Coercion sort : type >-> Sortclass.
    Coercion complatt : type >-> complat.type.
    Coercion latticet : type >-> lattice.type.
    Coercion complatk : type >-> complat.type.
    Coercion latticek : type >-> lattice.type.
    Canonical complatt.
    Canonical latticet.
    Canonical complatk.
    Canonical latticek.
    Notation bilattice := type.
    Notation bilatticeMixin := mixin_of.    

    Definition neg T := neg (class T).
    Definition meetk T := meetk (class T).
    Definition joink T := joink (class T).
    Definition lek T := lek (class T).
    Definition bott {T} := @bot (complatt T).
    Definition topt {T} := @top (complatt T).
    Definition botk {T} := @bot (complatk T).
    Definition topk {T} := @top (complatk T).

    Notation "x <*> y" := (meetk x y)(at level 30).
    Notation "x <+> y" := (joink x y)(at level 30).
    Notation "x ≺_k y" := (lek x y)(at level 40).
    Notation "¬ x" := (neg x)(at level 10).
    Notation TRUE := topt.
    Notation FALSE := bott.
    Notation "⊤" := topk.
    Notation "⊥" := botk.
    
    
    Lemma letN (T : bilattice) : forall (x y : T),  x ≺ y ->   (neg y) ≺ (neg x).
    Proof. apply letN. Qed.
    Lemma lekN (T : bilattice): forall (x y : T),  x ≺_k y -> (neg x) ≺_k (neg y).
    Proof. apply lekN. Qed.    
    Lemma NN (T : bilattice) : forall x : T , neg (neg x) = x.
    Proof. apply NN. Qed.


  End Exports.
End bilattice.

Export bilattice.Exports.

Section bilatticeTheory.

  Variable L : bilattice.


  Lemma neg_TRUE :  
    ¬ TRUE  = (FALSE : L) .
  Proof.
    apply antisym.
    - rewrite <- (NN (FALSE )).
      apply letN.
      unfold TRUE,top.
      apply is_upb.
      constructor.
    - unfold FALSE, bot.
      apply is_lowb.
      constructor.
  Qed.

  Lemma neg_FALSE :  
    ¬ (FALSE :  L) = TRUE.
  Proof.
    apply antisym; first last.
    - rewrite <- (NN (TRUE )).
      apply letN.
      unfold FALSE,bot.
      apply is_lowb.
      constructor.
    - unfold TRUE, top.
      apply is_upb.
      constructor.  
  Qed.

  Lemma neg_and (x y : L) :
    ¬ (x ∧ y) = ¬ x ∨ ¬ y.
  Proof.
    apply antisym.
    - rewrite <- (NN (¬ x ∨ ¬ y)).
      apply letN.
      apply meet_inf.
      * rewrite  <- (NN x). 
        apply letN.
        rewrite NN.
        move : (join_upb (¬ x) (¬ y)); case; auto.
      * rewrite <- (NN y).
        apply letN.
        rewrite NN.
        move : (join_upb (¬ x) (¬ y)); case; auto.
    - move : (meet_lowb x y) => [H1 H2].
      apply join_sup; apply letN; auto.
  Qed.

  Lemma neg_or (x y : L) :
    ¬ (x ∨ y) = ¬ x ∧ ¬ y.
  Proof.
    apply antisym.
    - rewrite <- (NN (¬ x ∧ ¬ y)).
      apply letN.
      rewrite neg_and.
      repeat rewrite NN.
      apply meetI.
    - rewrite <- (NN (¬ x ∧ ¬ y)).
      apply letN.
      rewrite neg_and.
      repeat rewrite NN.
      apply meetI.
  Qed.    

End bilatticeTheory.


Module interlaced.

  Section ClassDef.

    Record mixin_of T (opst opsk : lattice.ops T ):= Mixin {   
      meett := lattice.meet_ opst;
      joint := lattice.join_ opst;
      let_ := fun a b => meett a b = a;
      meetk := lattice.meet_ opsk;
      joink := lattice.join_ opsk;
      lek := fun a b => meetk a b = a;
      monot_meet : forall x y z, let_ x y -> let_ (meetk x z) (meetk y z);
      monot_join : forall x y z, let_ x y -> let_ (joink x z) (joink y z);
      monok_meet : forall x y z, lek x y -> lek (meett x z) (meett y z);
      monok_join : forall x y z, lek x y -> lek (joint x z) (joint y z);
    }.


    Record class_of T (opst opsk : lattice.ops T) := Class {
      baset : tblattice.class_of opst;
      basek : tblattice.class_of opsk;
      mixin : mixin_of opst opsk
    }.

    Structure type := Pack {
      sort : Type; 
      opst : lattice.ops sort;  
      opsk : lattice.ops sort;
      _ : class_of opst opsk
    }.

    Variables  (cT : type).
    Definition class := let: Pack _ _ _ c := cT return class_of (opst cT) (opsk cT) in c.    


    Definition latticet := @lattice.Pack (sort cT) (opst cT) (baset class).
    Definition latticek := @lattice.Pack (sort cT) (opsk cT) (basek class).
    Definition tblatticet := @tblattice.Pack (sort cT) (opst cT) (baset class).
    Definition tblatticek := @tblattice.Pack (sort cT) (opsk cT) (basek class).
  
  End ClassDef.

  Module  Exports.    
    Coercion baset : class_of >-> tblattice.class_of.
    Coercion mixin : class_of >-> mixin_of.
    Coercion sort : type >-> Sortclass.
    Coercion latticet : type >-> lattice.type.
    Coercion tblatticet : type >-> tblattice.type.
    Canonical latticet.
    Canonical tblatticet.
    Canonical latticek.
    Canonical tblatticek.
    Notation interlaced := type.
    Notation interlacedMixin := mixin_of.    

    Definition meetk T := meetk (mixin (class T)).
    Definition joink T := joink (mixin (class T)).
    Definition lek T := lek (class T).
    Definition bott {T} := @tblattice.bot (tblatticet T).
    Definition topt {T} := @tblattice.top (tblatticet T).
    Definition botk {T} := @tblattice.bot (tblatticek T).
    Definition topk {T} := @tblattice.top (tblatticek T).

    Notation "x <*> y" := (meetk x y)(at level 30).
    Notation "x <+> y" := (joink x y)(at level 30).
    Notation "x ≺_k y" := (lek x y)(at level 40).
    Notation TRUE := topt.
    Notation FALSE := bott.
    Notation "⊤" := topk.
    Notation "⊥" := botk.
    
    
    
    Lemma monot_meet (T : interlaced) : forall (x y z : T), x ≺ y -> x <*> z ≺ y <*> z.
    Proof. apply monot_meet. Qed.
    Lemma monot_join (T : interlaced) : forall (x y z : T), x ≺ y -> x <+> z ≺ y <+> z.
    Proof. apply monot_join. Qed.
    Lemma monok_meet (T : interlaced) : forall (x y z : T), x ≺_k y -> x ∧ z ≺_k y ∧ z.
    Proof. apply monok_meet. Qed.
    Lemma monok_join (T : interlaced) : forall (x y z : T), x ≺_k y -> x ∨ z ≺_k y ∨ z.
    Proof. apply monok_join. Qed.

  End Exports.
End interlaced.

Export interlaced.Exports.

Module prodinter.
  Section def.
  
  Variable (L1 L2 : tblattice).

  Definition opst : lattice.ops (L1 * L2) := {|
    lattice.meet_ := fun x y => ((fst x) ∧ (fst y), (snd x) ∨ (snd y));
    lattice.join_ := fun x y => ((fst x) ∨ (fst y), (snd x) ∧ (snd y));
  |}.

  Definition opsk : lattice.ops (L1 * L2) := {|
    lattice.meet_ := fun x y => ((fst x) ∧ (fst y), (snd x) ∧ (snd y));
    lattice.join_ := fun x y => ((fst x) ∨ (fst y), (snd x) ∨ (snd y));
  |}.

  Local Notation meett := (lattice.meet_ opst).
  Local Notation joint := (lattice.join_ opst).
  Local Notation meetk := (lattice.meet_ opsk).
  Local Notation joink := (lattice.join_ opsk).
  Local Notation let_ := (fun a b => meett a b = a).
  Local Notation lek := (fun a b => meetk a b = a).
  Local Notation top1 := (@TOP L1).
  Local Notation bot1 := (@BOT L1).
  Local Notation top2 := (@TOP L2).
  Local Notation bot2 := (@BOT L2).

  Lemma opst_spec (x1 y1 : L1) (x2 y2 : L2) :
    let_ (x1, x2) (y1, y2) <-> x1 ≺ y1 /\ y2 ≺ x2.
  Proof.
    split => [H | [H1 H2]].
    - unfold meett, opst in H.
      inversion_clear H.
      split.
      * move : (meet_lowb x1 y1); case; auto.
      * move : (join_upb x2 y2); case; auto.
    - unfold meett, opst => /=.
      congr pair; auto.
      rewrite joinC.
      apply join_meet; auto.
  Qed.

  Lemma opsk_spec (x1 y1 : L1) (x2 y2 : L2) :
    lek (x1, x2) (y1, y2) <-> x1 ≺ y1 /\ x2 ≺ y2.
  Proof.
    split => [H | [H1 H2]].
    - unfold meett, opsk in H.
      inversion_clear H.
      split.
      * move : (meet_lowb x1 y1); case; auto.
      * move : (meet_lowb x2 y2); case; auto.
    - unfold meett, opsk => /=.
      congr pair; auto.
  Qed.


  Definition type :  interlaced.
  Proof.
    eapply (interlaced.Pack (opst := opst) (opsk := opsk)).
    constructor.
    - split.
      {
        split; intros;
        unfold meett,joint, opst => /=;
        try congr pair.
        - apply meetC.
        - apply joinC.
        - apply joinC.
        - apply meetC.
        - apply meetA.
        - apply joinA.
        - apply joinA.
        - apply meetA.
        - rewrite joinK meetK.
          symmetry.
          apply surjective_pairing.
        - rewrite meetK joinK.
          symmetry.
          apply surjective_pairing.
      }
      {
        eapply (tblattice.Mixin (top := (top1,bot2)) (bot := (bot1,top2)));
        move => [x1 x2];
        unfold meett, opst => /=;
        congr pair.
        * apply topP.
        * rewrite joinC.
          apply join_meet.
          apply botP.
        * apply botP.
        * rewrite joinC.
          apply join_meet.
          apply topP.
      }
    - split.
      {
        split; intros;
        unfold meetk,joink, opsk => /=;
        try congr pair.
        - apply meetC.
        - apply meetC.
        - apply joinC.
        - apply joinC.
        - apply meetA.
        - apply meetA.
        - apply joinA.
        - apply joinA.
        - repeat rewrite joinK.
          symmetry.
          apply surjective_pairing.
        - repeat rewrite meetK.
          symmetry.
          apply surjective_pairing.
      }
      {
        eapply (tblattice.Mixin (top := (top1,top2)) (bot := (bot1,bot2)));
        move => [x1 x2];
        unfold meetk, opsk => /=;
        congr pair.
        * apply topP.
        * apply topP.
        * apply botP.
        * apply botP.      
      }
    - constructor; intros [x X] [y Y] [z Z];
      unfold meett, joint, opst, opsk => <- /=;
      congr pair.
      * rewrite <- (meetA x y z).
        move : (meet_lowb x (y ∧ z)).
        case; auto.
      * rewrite joinC.
        apply join_meet.
        apply meet_inf.
        - apply trans with Y.
          + move : (meet_lowb Y Z); case; auto.
          + move : (join_upb X Y); case; auto.
        - move:  (meet_lowb Y Z); case; auto.
      * apply join_sup.
        - apply trans with y.
          + apply meet_lowb.
          + apply join_upb.
        - apply join_upb.
      * rewrite joinC. apply join_meet. rewrite <- (joinA X Y Z).
        apply join_upb.
      * rewrite <- (meetA x y z).
        apply meet_lowb.
      * apply join_sup.
        - apply trans with Y.
          + apply meet_lowb.
          + apply join_upb.
        - apply join_upb.
      * apply join_sup.
        - apply trans with y.
          + apply meet_lowb.
          + apply join_upb.
        - apply join_upb.
      * rewrite <- (meetA X Y Z).
        apply meet_lowb.
  Defined.

  End def.

  Module Exports.
    Notation prodinter := type.
    Canonical prodinter.
    Notation "L1 ⊙ L2" := (prodinter L1 L2) (at level 40, left associativity).
    Notation let_spec := opst_spec.
    Notation lek_spec := opsk_spec.

    Definition neg (L : tblattice) (p : L ⊙ L) : L ⊙ L :=
      match p with
      | (x,y) => (y,x)
      end.
        
  End Exports.

End prodinter.

Export prodinter.Exports.

Section prodinterTheory.
  Variable (L : tblattice).
  Notation LL := (L ⊙ L).

  Variable (x y z : LL).

  Lemma letN :
    x ≺ y -> (neg y) ≺ (neg x).
  Proof.
    destruct x as [x1 x2], y as [y1 y2].
    move /let_spec => H => /=.
    apply /let_spec; split; apply H.
  Qed.

  Lemma lekN :
    x ≺_k y -> (neg x) ≺_k (neg y).
  Proof.
    destruct x as [x1 x2], y as [y1 y2].
    move /lek_spec => H => /=.
    apply /lek_spec; split; apply H.
  Qed.

  Lemma NN : neg (neg x) = x.
  Proof. destruct x => //=. Qed.

End prodinterTheory.


Module compbilat.
  Section def.
  Variable (L : complat).
  
  Definition LL := L ⊙ L.
  
  Definition neg (x : LL) :=
    match x with
    | (x,y) => (y,x)
    end.

  Local Notation opst := (interlaced.opst  LL).
  Local Notation opsk := (interlaced.opsk  LL).

  Definition fsts {T} {X : {set T * T}} : {set T}:=
    fun x => exists y, (x,y) \in X.
  
  Definition snds {T} {X : {set T * T}} : {set T}:=
    fun y => exists x, (x,y) \in X.

  (*
    inf := ∧ [a, b, ... ,n]
    のようにしたいが、集合を有限集合Ensembleで表現しているので難しい。
    finsetで表現しているなら、bigopを使って表現できそうではある。
    しかしそれだと、kleeneの不動点定理が証明できなくなる。
    インフォーマルには存在は主張できそうだから、axiomとしておく。    
  *)

  Axiom inft : {set LL} -> LL.
  Axiom supt : {set LL } -> LL.
  Axiom is_upbt : forall A a, a \in A -> a ≺ (supt A).
  Axiom is_supt : forall A a, (forall b, b \in A -> b ≺ a) -> (supt A) ≺ a.
  Axiom is_lowbt : forall A a, a \in A -> (inft A) ≺ a.
  Axiom is_inft : forall A a,(forall b, b \in A -> a ≺ b) -> a ≺ (inft A).

  Axiom infk : {set LL} -> LL.
  Axiom supk : {set LL } -> LL.
  Axiom is_upbk : forall A a, a \in A -> a ≺_k (supk A).
  Axiom is_supk : forall A a, (forall b, b \in A -> b ≺_k a) -> (supk A) ≺_k a.
  Axiom is_lowbk : forall A a, a \in A -> (infk A) ≺_k a.
  Axiom is_infk : forall A a,(forall b, b \in A -> a ≺_k b) -> a ≺_k (infk A).
  
  Definition type : bilattice.
  Proof.
    apply bilattice.Pack with (opst := opst) (opsk := opsk).
    constructor.
    - constructor. 
      * apply (lattice.class (interlaced.latticet LL)) .
      * eapply complat.Mixin with (sup := supt) (inf := inft).
        + apply is_upbt.
        + apply is_supt.
        + apply is_lowbt.
        + apply is_inft.
    -  constructor.
      * apply (lattice.class (interlaced.latticek LL)).
      * eapply complat.Mixin with (sup := supk) (inf := infk).
        + apply is_upbk.
        + apply is_supk.
        + apply is_lowbk.
        + apply is_infk.
    - eapply (bilattice.Mixin (neg := neg)) => 
      [[x1 x2] [y1 y2]|[x1 x2] [y1 y2]| [x1 x2]];
      unfold opst => //=; case => H1 H2;
      congr pair; auto.
      - apply join_meet; auto.
        rewrite joinC; auto.
      - rewrite joinC.
        apply join_meet; auto.
  Defined.  
  End def.
  Module Exports.
    Notation compbilat := type.
    Canonical compbilat.
  End Exports.
End compbilat.

Export compbilat.Exports.




Module distbilattice.
  
  Section ClassDef.

    Record mixin_of T (opst opsk : lattice.ops T) := Mixin {
      meett := lattice.meet_ opst;
      joint := lattice.join_ opst;
      meetk := lattice.meet_ opsk;
      joink := lattice.join_ opsk;

      meett_joint : forall x y z, meett x (joint y z) = joint (meett x y) (meett x z);
      meett_meetk : forall x y z, meett x (meetk y z) = meetk (meett x y) (meett x z);
      meett_joink : forall x y z, meett x (joink y z) = joink (meett x y) (meett x z);

      joint_meett : forall x y z, joint x (meett y z) = meett (joint x y) (joint x z);
      joint_meetk : forall x y z, joint x (meetk y z) = meetk (joint x y) (joint x z);
      joint_joink : forall x y z, joint x (joink y z) = joink (joint x y) (joint x z);

      meetk_meett : forall x y z, meetk x (meett y z) = meett (meetk x y) (meetk x z);
      meetk_joint : forall x y z, meetk x (joint y z) = joint (meetk x y) (meetk x z);
      meetk_joink : forall x y z, meetk x (joink y z) = joink (meetk x y) (meetk x z);

      joink_meett : forall x y z, joink x (meett y z) = meett (joink x y) (joink x z);
      joink_joint : forall x y z, joink x (joint y z) = joint (joink x y) (joink x z);
      joink_meetk : forall x y z, joink x (meetk y z) = meetk (joink x y) (joink x z);
    }.

    Record class_of T (opst opsk : lattice.ops T):= Class {
      base : bilattice.class_of opst opsk;
      mixin : mixin_of opst opsk;
    }.

    Structure type := Pack {
      sort : Type; 
      opst : lattice.ops sort;  
      opsk : lattice.ops sort;
      _ : class_of opst opsk
    }.

    Variables  (cT : type).
    Definition class := let: Pack _ _ _ c := cT return class_of (opst cT) (opsk cT) in c.    

    Definition bilattice := @bilattice.Pack (sort cT) (opst cT) (opsk cT) (base class).
    Definition complatt := @complat.Pack (sort cT) (opst cT) (base class).
    Definition latticet := @lattice.Pack (sort cT) (opst cT) (base class).
    Definition complatk := @complat.Pack (sort cT) (opsk cT) (bilattice.basek (base class)).
    Definition latticek := @lattice.Pack (sort cT) (opsk cT) (bilattice.basek (base class)).
   
  
  End ClassDef.

  Module  Exports.    
    Coercion base : class_of >-> bilattice.class_of.
    Coercion mixin : class_of >-> mixin_of.
    Coercion sort : type >-> Sortclass.
    Coercion bilattice : type >-> bilattice.type.
    Coercion complatt : type >-> complat.type.
    Coercion latticet : type >-> lattice.type.
    Coercion complatk : type >-> complat.type.
    Coercion latticek : type >-> lattice.type.
    Canonical bilattice.
    Canonical complatt.
    Canonical latticet.
    Canonical complatk.
    Canonical latticek.
    Notation distbilat := type.
    Notation distbilatMixin := mixin_of.  


    (* Section interface.
      Variable (T : distbilat).
      Variable (x y z : T).
      Locate "<*>".

        
      Lemma meett_joint : x ∧ (y ∨ z) = (x ∧ y) ∨ (x ∧ z).
      Proof. eapply (meett_joint (class T)). Qed.
      Lemma meett_meetk : x ∧ (y <*> z) = (x ∧ y) <*> (x ∧ z).
      Proof. apply (meett_meetk (class T)). Qed.
      Lemma meett_joink : x ∧ (y <+> z) = (x ∧ y) <+> ( x ∧ z).
      Proof. apply (meett_joink (class T)). Qed.

      Lemma joint_meett :  ∨ (y ∧ z) = (x ∨ y) ∧ (x ∨ z).
      Proof. apply (joint_meett (class T)). Qed.
      Lemma joint_meetk :  ∨ (y <*> z) = (x ∨ y) <*> (x ∨ z).
      Proof. apply (joint_meetk (class T)). Qed.
      Lemma joint_joink :  ∨ (y <+> z) = (x ∨ y) <+> (x ∨ z).
      Proof. apply (joint_joink (class T)). Qed.

      Lemma meetk_meett :  <*> (y ∧ z) = (x <*> y) ∧ (x <*> z).
      Proof. apply (meetk_meett (class T)). Qed.
      Lemma meetk_joint :  <*> (y ∨ z) = (x <*> y) ∨ (x <*> z).
      Proof. apply (meetk_joint (class T)). Qed.
      Lemma meetk_joink :  <*> (y <+> z) = (x <*> y) <+> (x <*> z).
      Proof. apply (meetk_joink (class T)). Qed.

      Lemma joink_meett :  <+> (y ∧ z) = (x <+> y) ∧ (x <+> z).
      Proof. apply (joink_meett (class T)). Qed.
      Lemma joink_joint :  <+> (y ∨ z) = (x <+> y) ∨ (x <+> z).
      Proof. apply (joink_joint (class T)). Qed.
      Lemma joink_meetk :  <+> (y <*> z) = (x <+> y) <*> (x <+> z).
      Proof. apply (joink_meetk (class T)). Qed. *)


  End Exports.











      
  


 
  
      

  

  

    
