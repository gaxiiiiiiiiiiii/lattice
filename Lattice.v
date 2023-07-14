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