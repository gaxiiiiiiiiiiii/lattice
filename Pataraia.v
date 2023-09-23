Require Export UniMath.MoreFoundations.All.
Require Export UniMath.Algebra.Monoids.
Require Import UniMath.OrderTheory.Posets.Basics.
Require Import UniMath.OrderTheory.Posets.MonotoneFunctions.
Require Import UniMath.OrderTheory.DCPOs.Core.DirectedSets.
Require Import UniMath.OrderTheory.DCPOs.Core.Basics.
Require Import UniMath.OrderTheory.DCPOs.Examples.Products.
Require Import UniMath.OrderTheory.DCPOs.Examples.SubDCPO.
Require Import UniMath.OrderTheory.DCPOs.FixpointTheorems.Pataraia.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope dcpo.

Definition is_closed (X : dcppo) (f : monotone_function X X) (P : X -> hProp):=
    P (⊥_{X}) × 
    (∏ x : X, P x -> P (f x)) ×
    ∏ D : directed_set X, (∏ d : D, P (D d)) → P (⨆ D).

Lemma is_closed_isaprop (X : dcppo) (f : monotone_function X X) (P : X -> hProp) :
  isaprop (is_closed f P).
Proof.
  repeat apply isapropdirprod.
  - apply propproperty.
  - apply impred; intro.
    apply impred; intro.
    apply propproperty.
  - apply impred; intro.
    apply impred; intro.
    apply propproperty.
Qed.

Definition is_closed_hProp (X : dcppo) (f : monotone_function X X) (P : X -> hProp ):=
  make_hProp (is_closed f P )(@is_closed_isaprop X f P).

Definition closed {X : dcppo} (f : monotone_function X X) : (X -> hProp) -> hProp :=
  fun P => is_closed_hProp f P.

Definition smallest (X : dcppo) (f : monotone_function X X) : X -> hProp := 
  fun x => ∀ P, (closed f P ⇒ P x)%logic.

  
Lemma smallest_is_closed (X : dcppo) (f : monotone_function X X) :
  is_closed f (smallest f).
Proof.
  unfold smallest, subtype_intersection.
  unfold is_closed.
  split; [|split].
  - intros Y [k _]; auto.
  - intros x Hx P HP.
    apply (pr12 HP).    
    apply (Hx P HP); auto.
  - intros D HD P HP.
    apply (pr22 HP).
    intros d.
    apply (HD d P HP).
Qed.   


Definition smallest_included_in_closed {X : dcppo} (f : monotone_function X X) (P : X -> hProp) :
  is_closed f P -> ∏ x, smallest f x -> P x.
Proof.
  intros H x Hx.  
  apply (Hx P); auto.
Qed.



Definition smallest_dcppo (X : dcppo) (f : monotone_function X X) :  dcppo.
Proof.
  pose (L := (sub_dcpo _ (smallest f) (pr22 (smallest_is_closed f)))).
  exists (pr1 L).
  exists (pr2 L).
  use tpair.
  - exists ⊥_{X}; simpl.
    intros x [Hx _]; auto.
  - intros x.
    apply is_min_bottom_dcppo.
Defined.


Definition restrict_to_smallest (X : dcppo) (f : monotone_function X X) : monotone_function (smallest_dcppo f) (smallest_dcppo f).
Proof.
  use tpair.
  - intros [x Hx].
    exists (f x).
    intros y Hy.
    apply (pr12 Hy).
    simpl in Hx.
    apply Hx; auto.
  - simpl.
    intros x y xy.
    apply (pr2 f); auto.
Defined.

Lemma restriction_elim (X : dcppo) (f : monotone_function X X) (x : smallest_dcppo f) :
  pr1 (restrict_to_smallest f x) = f (pr1 x).
Proof.
  unfold restrict_to_smallest; auto.
Qed.  

Definition pataraia (X : dcppo) (f : monotone_function X X) : X :=
  pr1 (pataraia_fixpoint (restrict_to_smallest f)).

Lemma pataraia_is_fixpoint (X : dcppo) (f : monotone_function X X) :
  f (pataraia f) = pataraia f.
Proof.
  unfold pataraia.
  
  pose (k := f (pr1 (pataraia_fixpoint (restrict_to_smallest f)))).
  change (f (pr1 (pataraia_fixpoint (restrict_to_smallest f)))) with k.
  rewrite <- (is_fixpoint_pataraia_fixpoint ((restrict_to_smallest f))).
  rewrite restriction_elim.
  auto.
Qed.

Lemma under_is_closed (X : dcppo) (f : monotone_function X X) (x : X) :
  f x = x -> is_closed f (fun y => y ≤ x).
Proof.
  intros H.
  repeat split.
  - apply is_min_bottom_dcppo.
  - intros y Hy.
    rewrite <- H; apply (pr2 f); auto.
  - intros [D HD] H0.
    eapply dcpo_lub_is_least.
    intro i.
    apply (H0 i); auto.
Qed.

Proposition pataraia_is_leastfixpoint (X : dcppo)(f : monotone_function X X) : 
  forall x, f x = x -> pataraia f ≤ x.
Proof.
  intros x Hx.
  apply (@smallest_included_in_closed X f (fun y => y ≤ x)).
  { apply under_is_closed; auto. }
  unfold pataraia.
  apply (pr2 (pataraia_fixpoint (restrict_to_smallest f))).
Qed.


