From mathcomp Require Export ssreflect.
Require Export Ensembles Image.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Module lattice.

  Record mixin_of T := Mixin {
    meet : T -> T -> T;
    join : T -> T -> T;
    meetC : forall a b, meet a b = meet b a;
    joinC : forall a b, join a b = join b a;
    meetA : forall a b c, meet a (meet b c) = meet (meet a b) c;
    joinA : forall a b c , join a (join b c) = join (join a b) c;
    joinK : forall a b, meet a (join a b) = a;
    meetK : forall a b, join a (meet a b) = a;
  }.
  Notation class_of := mixin_of (only parsing).

  Section ClassDef.

    Structure type := Pack {sort : Type ; _ : class_of sort}.
    Variables (cT : type).    
    Definition class := let: Pack _ c := cT return class_of (sort cT) in c.

  
  End ClassDef.

  Module Exports.
    Coercion sort : type >-> Sortclass.
    Notation lattice := type.
    Notation latticeMixin := Mixin.

    
    Definition meet T := meet (class T).
    Definition join T := join (class T).

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
    Notation "x ≺ y" := (meet x y = x)(at level 40). 

    Global Notation "x \in X" := (In _ X x)(at level 30) .
    Global Notation "{set  T }" := (Ensemble T)(at level 10).
    Global Notation "f ∘ g" := (fun x => f (g x))(at level 40).

   
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

  Lemma lowb' (a b : L) :
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

  Lemma inf' (a b : L) :
    forall c, c ≺ a -> c ≺ b -> c ≺ meet a b.
  Proof.
    move => c Ha  Hb.
    rewrite meetA Ha Hb; auto.
  Qed.

  Lemma inf_uni (a b c : L) :
    c ≺ a -> c ≺ b -> (forall d, d ≺ a -> d ≺ b -> d ≺ c) -> meet a b = c.
  Proof.
    move => Ha Hb H.
    move : (lowb' a b) => [Ha' Hb'].
    move : (inf' Ha Hb) => H'.
    apply antisym; auto.
  Qed.

  Lemma upb' (a b : L) :
    a ≺ join a b /\ b ≺ join a b.
  Proof.
    split; move.
    - apply  (joinK a b).
    - rewrite (joinC a b).
      apply (joinK b a).
  Qed.


  Lemma sup' (a b : L) :
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
    move : (upb' a b) => [Ha' Hb'].
    move : (sup' Ha Hb) => H'.
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
      move : (upb' a b); case; auto.
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
    - move : (lowb' x y) => [low_x low_y].
      apply trans with (f (meet x y)).      
      - apply Ha; auto.
      - apply Hm; auto.      
    - move : (upb' x y) => [up_x up_y].
      apply trans with (f (join x y)).
      - apply Hm; auto.
      - apply Ha; auto.
  Qed.


End latticeTheory.

