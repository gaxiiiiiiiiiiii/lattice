From UniMath Require Export MoreFoundations.All Algebra.Monoids.
From mathcomp Require Export ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(***********)
(* Lattice *)
(***********)

Definition isLatticeOp {X : hSet} (meet join : binop X) :=
  (iscomm meet × iscomm join) ×
  (isassoc meet × isassoc join) ×
  (isabsorb meet join × isabsorb join meet).

Lemma isaprop_isLatticeOp {X : hSet} (meet join : binop X) :
  isaprop (isLatticeOp meet join).
Proof.
  repeat apply isapropdirprod;
  try apply isapropiscomm;
  try apply isapropisassoc;
  try apply isapropisabsorb.
Defined.  


Definition lattice (X : hSet) :=
  ∑ meet join : binop X, isLatticeOp meet join.

Definition make_lattice {X : hSet} {meet join : binop X} :
  isLatticeOp meet join -> lattice X := fun H => meet,, join,, H.

Definition latticeToSet {X : hSet}(l : lattice X) := X.
Coercion latticeToSet : lattice >-> hSet.

Definition meet {X : hSet} {l : lattice X} (x y : l) : l := pr1 l x y.
Definition join {X : hSet} {l : lattice X} (x y : l) : l := pr1 (pr2 l) x y.
Definition le {X : hSet} {l : lattice X} : hrel l := fun x y => (meet x y = x)%logic.

Global Infix "<*>" := meet(at level 30).
Global Infix "<+>" := join (at level 30).
Global Infix "≺" := le (at level 40).


Section transLheory.
  
  Variable X : hSet.
  Variable l : lattice X.
  
  Definition meetC : iscomm meet := pr1 (pr1 (pr2 (pr2 l))).
  Definition joinC : iscomm join := pr2 (pr1 (pr2 (pr2 l))).
  Definition meetA : isassoc meet := pr1 (pr1 (pr2 (pr2 (pr2 l)))).
  Definition joinA : isassoc join := pr2 (pr1 (pr2 (pr2 (pr2 l)))).
  Definition meetjoinK : isabsorb meet join := pr1 (pr2 (pr2 (pr2 (pr2 l)))).
  Definition joinmeetK : isabsorb join meet := pr2 (pr2 (pr2 (pr2 (pr2 l)))).

  Lemma meetI (a : l) :
    a <*> a = a.
  Proof.    
    move : (meetjoinK a (meet a a)) => H1.
    move : (joinmeetK a a) => H2.
    apply (transportf (fun x => a <*> x = a) H2 H1).
  Defined.

  Lemma joinI (a : l) :
    a <+> a = a.
  Proof.
    eapply (pathscomp0 (b := a <+> (a <*> a))).
    - apply (transportb (fun x => a <+> a = a <+> x) (meetI a) (idpath _)).
    - apply joinmeetK.
  Defined.

  Lemma reflL (a : l) :
    a ≺ a.
  Proof.
    simpl.
    apply meetI.
  Defined.

  Lemma transL (a b c : l) :
    a ≺ b -> b ≺ c -> a ≺ c.
  Proof.
    move => /= ab bc.
    eapply (pathscomp0 (b := (a <*> b) <*> c)). 
    apply (transportb (fun x => a <*> c = x <*> c) ab); auto.
    eapply (pathscomp0 (b := a <*> (b <*> c))).
    apply meetA.
    apply (transportb (fun x => a <*> x = a)  bc); auto.
  Defined.   

  Lemma antisymL (a b : l) :
    a ≺ b -> b ≺ a -> a = b.
  Proof.
    move => /= ab ba.
    intermediate_path (a <*> b).
    apply pathsinv0; auto.
    intermediate_path (b <*> (b <*> a)).
    intermediate_path ((b <*> b) <*> a).
    intermediate_path (a <*> (b <*> b)).
    apply (transportb (fun x => a <*> b = a <*> x) (meetI b)); auto.
    apply meetC.
    apply (meetA b b a).
    apply (transportb (fun x => b <*> x = b) ba).
    apply meetI.
  Defined.

    
  Lemma meet_lowb (a b : l) :
    meet a b ≺ a ∧ meet a b ≺ b.
  Proof.
    split => /=.
    - intermediate_path (a <*> (a <*> b)).
      apply meetC.
      intermediate_path ((a <*> a) <*> b).
      apply (pathsinv0 (meetA a a b)).
      apply (transportb (fun x => x <*> b = a <*> b) (meetI a)).
      auto.
    - intermediate_path (a <*> (b <*> b)).
      apply (meetA a b b ).
      apply (transportb (fun x => a <*> x = a <*> b) (meetI b)); auto.
  Defined.
  
  Lemma meet_inf (a b c : l) :
    c ≺ a -> c ≺ b -> c ≺ meet a b.
  Proof.
    move => /= Ha Hb.
    intermediate_path ((c <*> a) <*> b).
    apply pathsinv0. apply meetA.
    apply (transportb (fun x => x <*> b = c) Ha).
    auto.
  Defined.

  Lemma inf_uni (a b c : l) :
    c ≺ a -> c ≺ b -> (forall d, d ≺ a -> d ≺ b -> d ≺ c) -> meet a b = c.
  Proof.
    move => Ha Hb H.
    move : (meet_lowb a b) => [Ha' Hb'].
    move : (meet_inf Ha Hb) => H'.
    apply antisymL; auto.
  Defined.

  Lemma join_upb (a b : l) :
    a ≺ join a b ∧ b ≺ join a b.
  Proof.
    split; move.
    - apply  meetjoinK.
    - intermediate_path (b <*> (b <+> a)).
      apply (transportf (fun x => b <*> x = b <*> (b <+> a)) (joinC b a)); auto.
      apply meetjoinK.
  Defined.

  Lemma meet_join (a b : l) :
    meet a b = a <-> join a b = b.
  Proof.
    split => H.
    - intermediate_path ((a <*> b) <+> b).
      apply (transportb (fun x => a <+> b = x <+> b) H); auto.      
      intermediate_path (b <+> (a <*> b)).
      apply joinC.
      intermediate_path (b <+> (b <*> a)).
      apply (transportf (fun x => b <+> (a <*> b) = b <+> x) (meetC a b)); auto.
      apply joinmeetK.
    - intermediate_path (a <*> (a <+> b)).
      apply (transportb (fun x => a <*> b = a <*> x) H); auto.
      apply meetjoinK.
  Defined.

  Lemma join_sup (a b c : l) :
    a ≺ c -> b ≺ c -> join a b ≺ c.
  Proof.
    move =>  Ha Hb.
    apply meet_join in Ha.
    apply meet_join in Hb.
    apply meet_join.
    intermediate_path (a <+> b <+> (b <+> c)).
    apply (transportb (fun x => (a <+> b) <+> c = (a <+> b) <+> x) Hb); auto.
    intermediate_path  (a <+> (b <+> (b <+> c))).
    apply joinA.
    intermediate_path (a <+> ((b <+> b) <+> c)).
    apply (transportf (fun x => a <+> x =  a <+> ((b <+> b) <+> c)) (joinA b b c)); auto.
    intermediate_path (a <+> (b <+> c)).
    apply (transportb (fun x => a <+> (x <+> c) = a <+> (b <+> c)) (joinI b)); auto.
    apply (transportb (fun x => a <+> x =  c) Hb); auto.
  Defined.


  Lemma sup_uni (a b c : l) :
    a ≺ c -> b ≺ c -> (forall d, a ≺ d -> b ≺ d -> c ≺ d) -> join a b = c.
  Proof.
    move => Ha Hb H.
    move : (join_upb a b) => [Ha' Hb'].
    move : (join_sup Ha Hb) => H'.
    apply antisymL; auto.
  Qed.

End transLheory.

(*********************)
(* Monotony and etc. *)
(*********************)

Global Notation "{set : X }" := (hsubtype X).
Definition In {T : hSet} (A : {set : T}) (a : T) := A a. 
Global Notation "a ∈ A" := (In A a) (at level 70).

Definition fullset {T : hSet} : {set : T} := fun _ => htrue.
Global Notation "∅" := (emptysubtype _).



(* fullsetの検証 *)
(* Goal ∏ (T : hSet) (t : T), t ∈ fullset.
Proof.
  move => T t.
  unfold In => /=.
  apply tt.
Qed.   *)

Definition mono {T : hSet}{L1 L2 : lattice T}(f : L1 -> L2) :=
  ∏ (a b : L1), a ≺ b → f a ≺ f b.


Definition antimono {T : hSet }{L1 L2 : lattice T}(f : L1 -> L2) :=
  ∏ a b : L1, a ≺ b -> f b ≺ f a.  

Definition directed {T : hSet} {L : lattice T}(X : {set : L}) :=
  ∏ x y, x ∈ X -> y ∈ X -> ∃ z, z ∈ X ∧ x ≺ z ∧ y ≺ z.


Lemma isapropMono {T : hSet}{L1 L2 : lattice T}(f : L1 -> L2) :
  isaprop (mono f).
Proof.
  repeat (apply impred; intro).
  apply propproperty.
Defined.

Lemma isapropAntimono {T : hSet}{L1 L2 : lattice T}(f : L1 -> L2) :
  isaprop (antimono f).
Proof.
  repeat (apply impred; intro).
  apply propproperty.
Defined.

Lemma isapropDirected {T : hSet}{L : lattice T}(X : {set : L}) :
  isaprop (directed X).
Proof.
  repeat (apply impred; intro).
  apply propproperty.
Defined.

Lemma antimono_compose_mono {T : hSet}{L1 L2 L3 : lattice T}(f : L1 -> L2)(g : L2 -> L3) :
    antimono f -> antimono g -> mono (g ∘ f).
Proof. 
  move => Hf Hg x y H; eauto.
Qed.

Lemma mono_antimono_constant {T : hSet} (L : lattice T)(f : L -> L) :
  mono f -> antimono f -> ∏ x y, f x = f y.
Proof.
  move => Hm Ha x y.
  apply antisymL.
  - move : (meet_lowb x y) => [low_x low_y].
    apply transL with (f (meet x y)).      
    - apply Ha; auto.
    - apply Hm; auto.      
  - move : (join_upb x y) => [up_x up_y].
    apply transL with (f (join x y)).
    - apply Hm; auto.
    - apply Ha; auto.
Qed.