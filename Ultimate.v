Require Export Approximation.
Require Export Pataraia.

Require Import UniMath.MoreFoundations.All.
Require Import UniMath.OrderTheory.Posets.Basics.
Require Import UniMath.OrderTheory.Posets.MonotoneFunctions.
Require Import UniMath.OrderTheory.DCPOs.Core.DirectedSets.
Require Import UniMath.OrderTheory.DCPOs.Core.Basics.
Require Import UniMath.OrderTheory.DCPOs.Examples.Products.
Require Import UniMath.OrderTheory.DCPOs.Examples.SubDCPO.
Require Import UniMath.OrderTheory.DCPOs.FixpointTheorems.Pataraia.

Open Scope dcpo.
(* Open Scope poset. *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.




Definition interval {T} {L : complat T} (x y : L) : {set : L} :=
  fun z => x ≺ z ∧ z ≺ y.  

Lemma isPredicate_interval {T} {L : complat T} (a b : L):
  isPredicate (λ x : L,  a ≺ x × x ≺ b).
Proof.  
  unfold isPredicate => x.
  apply isapropdirprod. 
  apply (propproperty (a ≺ x)).
  apply (propproperty (x ≺ b)).
Qed.  

Definition imeet {T} {L : complat T} (a b : L) :   
  binop (carrier_subset (interval a b)).
Proof.
  move => [x [xb xt]] [y [yb yt]].
  split with (meet x y); split; simpl in *.
  * apply meet_join in xb, yb.
    replace (meet x y) with (meet (join a x) (join a y)); first last.
    {rewrite xb yb; auto. }
    rewrite <- meetA, meetjoinK, meetjoinK; auto.
  * apply meet_join.
    replace (meet x y) with (meet (meet x b) (meet y b)); first last.
    {rewrite xt yt; auto. }
    rewrite meetA (meetC y b).
    rewrite <- (meetA b b y), meetI.
    rewrite <- (meetA x b y), (meetC x b), meetA, joinC, joinmeetK.
    auto.
Defined.

Definition ijoin {T} {L : complat T} (a b : L) : binop (carrier_subset (interval a b)).
Proof.
  move => [x [xb xt]] [y [yb yt]].
  split with (join x y); split.
  * simpl in *.
    apply meet_join in xb, yb.
    replace (join x y) with (join (join a x) (join a y)); first last.
    { rewrite xb yb; auto. }
    rewrite (joinC a x) joinA.
    rewrite <- (joinA a a y), joinI,  
    <- joinA, (joinC x a), joinA, meetjoinK; auto.
  * simpl in *.
    apply meet_join.
    replace (join x y) with (join (meet x b) (meet y b)); first last.
    { rewrite xt yt; auto. }
    rewrite joinA (joinC (meet _ _ ) b) (meetC y b) joinmeetK
      joinC meetC joinmeetK; auto.  
Defined.

Definition interval_lattice {T} {L : complat T} (a b : L) : 
  lattice (carrier_subset (interval a b)).
Proof.
  use tpair.
  { exact (@imeet _ _ a b). }
  use tpair.
  { exact (@ijoin _ _ a b). }
  
  repeat use tpair; simpl; unfold iscomm, isassoc, isabsorb; intros;
  apply subtypePath; auto; unfold imeet, ijoin => /=;
  try apply isPredicate_interval. 
  - apply meetC.
  - apply joinC.
  - apply meetA.
  - apply joinA.
  - apply meetjoinK.
  - apply joinmeetK.
Defined.

Section interval_complat.

Hypotheses lem : LEM.

Lemma notallnot_ex T (P : T -> hProp) :
  ¬ (∀ x, hneg (P x)) -> ∃ x, P x.
Proof.
  move => H.
  apply negforall_to_existsneg in H; auto.
  unfold ishinh, ishinh_UU in H.
  apply H => [[x Hx]].
  move => Q; apply; clear Q.
  exists x;
  apply invimpl; auto.
  apply isaninv1.    
  unfold isdecprop.
  split; first last.
  { eapply propproperty. }
  move : (lem  (P x)) => Hl.
  induction Hl; [apply ii1 | apply ii2]; auto .
Qed.

Lemma notempty_has_elm {T : hSet} (X : {set : T}) (H : ¬ (X == emptysubtype _)) :
  ∃ x, x ∈ X.
Proof.
  apply notallnot_ex => F.
  apply H.
  move : (invweq (hsubtype_univalence X (emptysubtype _))) => [f Hf].
  apply f.
  unfold subtype_equal => x; split => H0.
  - induction (F x); auto.
  - induction H0.
Qed.  


  
Definition isup {T} {L : complat T} (a b : L) (H : a ≺ b): 
  {set : carrier_subset (interval a b)} -> carrier_subset (interval a b).
Proof.
  move => X.
  set Y : {set : L}:= (image_hsubtype X pr1).
  move : (lem (X == (emptysubtype _))) => HX.
  induction HX as [HX|HX].
  * exists a; split; auto.
    apply meetI.
  * exists (sup Y).
    split; first last.
    - apply is_sup => y.
      unfold Y, In => Hy.
      unfold image_hsubtype, ishinh, ishinh_UU in Hy.    
      apply Hy => [[[k [Hk1 Hk2]] [H1 H2]]].
      simpl in *.
      induction H1; auto.
    - apply notempty_has_elm in HX.
      unfold ishinh, ishinh_UU in HX.
      apply HX => [[[k [ak kb]] Hk]].
      apply transL with k; auto.        
      apply is_upb.
      unfold Y, In.
      move => P; apply; clear P.
      exists (k,, (ak,, kb)); split; auto.
Defined.


Definition iinf {T} {L : complat T} (a b : L) (H : a ≺ b): 
  {set : carrier_subset (interval a b)} -> carrier_subset (interval a b).
Proof.
  move => X.
  set Y : {set : L}:= (image_hsubtype X pr1).
  move : (lem (X == (emptysubtype _))) => HX.
  induction HX as [HX|HX].
  * exists b; split; auto.
    apply meetI.
  * exists (inf Y).
    split.
    - apply is_inf => y.
      unfold Y, In => Hy.
      unfold image_hsubtype, ishinh, ishinh_UU in Hy.    
      apply Hy => [[[k [Hk1 Hk2]] [H1 H2]]].
      simpl in *.
      induction H1; auto.
    - apply notempty_has_elm in HX.
      unfold ishinh, ishinh_UU in HX.
      apply HX => [[[k [ak kb]] Hk]].
      apply transL with k; auto.        
      apply is_lowb.
      unfold Y, In.
      move => P; apply; clear P.
      exists (k,, (ak,, kb)); split; auto.
Defined.   

  
Definition interval_complat {T} {L : complat T} (a b : L) (H : a ≺ b): 
  complat (carrier_subset (interval a b)).
Proof.
  split with (interval_lattice a b).
  use tpair.
  { apply isup; auto. }
  use tpair.
  { apply iinf; auto. }
  simpl. repeat use tpair.
  - move => X [x [ax xb]] => Hx.
    apply subtypePath => //=.
    apply isPredicate_interval.
    unfold isup.
    set H0 := (lem (X == (emptysubtype _))).
    induction H0; simpl; auto.
    * simpl in a0.
      rewrite a0 in Hx.
      induction Hx.
    * apply is_upb.
      unfold image_hsubtype, In.
      move => P; apply; clear P.
      exists (x,, ax,, xb); split; auto.
  - move => X [x [ax xb]] => Hx.
    apply subtypePath => //=.
    apply isPredicate_interval.
    unfold isup.
    set H0 := (lem (X == (emptysubtype _))).
    induction H0; simpl; auto.

    * apply is_sup.
      move => c.
      unfold image_hsubtype, In => Hc.
      unfold ishinh, ishinh_UU in Hc.
      apply Hc => [[[k [ak kb]] [H1 H2]]].
      unfold pr1 in *.
      induction H1.
      move : (Hx (k,, ak,, kb) H2) => H0.
      simpl in H0.
      apply base_paths in H0; auto.
  - move => X [x [ax xb]] => Hx.
    apply subtypePath => //=.
    apply isPredicate_interval.
    unfold iinf.
    set H0 := (lem (X == (emptysubtype _))).
    induction H0; simpl; auto.
    * simpl in a0.
      rewrite a0 in Hx.
      induction Hx.
    * apply is_lowb.
      unfold image_hsubtype, In.
      move => P; apply; clear P.
      exists (x,, ax,, xb); split; auto.
  - move => X [x [ax xb]] => Hx.
    apply subtypePath => //=.
    apply isPredicate_interval.
    unfold iinf.
    set H0 := (lem (X == (emptysubtype _))).
    induction H0; simpl; auto.
    * apply is_inf.
      move => c.
      unfold image_hsubtype, In => Hc.
      unfold ishinh, ishinh_UU in Hc.
      apply Hc => [[[k [ak kb]] [H1 H2]]].
      unfold pr1 in *.
      induction H1.
      move : (Hx (k,, ak,, kb) H2) => H0.
      simpl in H0.
      apply base_paths in H0; auto. 
Defined.

End interval_complat.


Definition consistents {T} (L : complat T) : Type :=
  ∑ p : L^2, consistent p.
Definition consistentsL2 {T} {L : complat T} : consistents L -> L^2 := pr1.
Coercion consistentsL2 : consistents >-> pr1hSet.

Lemma isaset_consistents {T} (L : complat T) : isaset (consistents L).
Proof.
  unfold consistents.
  apply isaset_total2.
  - exact (setproperty (L^2)).
  - move => p. 
    apply isasetaprop.
    exact (propproperty (consistent p)).
Qed.

Definition Lc_hSet {T} (L : complat T) : hSet := make_hSet (consistents L) (isaset_consistents (L := L)).


Definition cle {T} {L : complat T} : hrel (Lc_hSet L) :=
  fun x y => (@kle _ (L^2) (pr1 x) (pr1 y)).

Definition consistent_struct {T} (L : complat T) : 
  dcppo_struct (Lc_hSet L).
Proof.  
  (* unfold dcppo. *)
  (* exists (Lc_hSet L). *)
  use tpair.
  - use tpair.
    exists cle.
    split; [split|].
    * move => [x Hx] [y Hy] [z Hz].
      unfold cle, pr1 => xy yz.
      eapply transL; eauto.
    * move => [x Hx].
      unfold cle, pr1.
      apply reflL.
    * move => [x Hx] [y Hy].
      unfold cle, pr1 => xy yx.
      move : (antisymL xy yx) => xx.
      induction xx.
      move : (propproperty (consistent x) Hx Hy) => [E _].
      induction E; auto.
  all : simpl.
  - unfold directed_complete_poset.
    move => I f [HI H].
    (* unfold isdirected in H. *)
    use tpair.
    - use tpair.
      * set X : {set : L^2 }:=  fun x => ∃ i, x = pr1 (f i).
        set X1 : {set : L} := fun x => ∃ y, X (x,,y).
        set X2 : {set : L} := fun y => ∃ x, X (x,,y).
        exact (sup X1,, inf X2).      
      * simpl.

        apply is_sup => a.
        unfold In, pr2 => Ha.
        unfold ishinh, ishinh_UU in Ha.
        apply Ha => [[x Hy]]; clear Ha.
        apply Hy => [[i Hi]]; clear Hy.

        apply is_inf => b.
        unfold In => Hb.
        unfold ishinh, ishinh_UU in Hb.
        apply Hb => [[y Hx]]; clear Hb.
        apply Hx => [[j Hj]]; clear Hx.

        (* induction H as [_ H]. *)
        specialize (H i j).
        unfold ishinh, ishinh_UU in H.
        apply H => [[k [ik jk]]]; clear H.
        induction (f k) as [[k1 k2] Hfk].
        unfold consistent in Hfk; simpl in Hfk.


        induction (f i) as [fi Hfi].
        simpl in Hi,ik.
        unfold consistent in Hfi.        
        rewrite <- Hi in Hfi, ik.
        unfold pr1, pr2 in Hfi.

        induction (f j) as [fj Hfj].
        simpl in Hj, jk.
        unfold consistent in Hfj.
        rewrite <- Hj in Hfj, jk.
        unfold pr1, pr2 in Hfj.
        clear Hi Hj.

        apply prod_dest in ik,jk.
        unfold pr1,pr2 in ik,jk.
        induction ik as [ak1 xk2], jk as[yk1 bk2].
        rewrite joinC in xk2; apply meet_join in xk2. 
        rewrite joinC in bk2; apply meet_join in bk2.

        apply transL with k1; auto.
        apply transL with k2; auto.

      * simpl.
        (* unfold islub => /=. *)
        split.
        + 
          (* unfold isupperbound => i. *)
          move => i.
          induction (f i) as [[fx fy] Hfi] eqn:Hi.
          simpl.
          apply two_arg_paths.
          * apply is_upb.
            unfold In.
            move => P; apply; clear P.
            exists fy.
            move => P; apply; clear P.
            exists i.
            rewrite Hi; auto.
          * rewrite joinC. apply meet_join.
            apply is_lowb.
            unfold In.
            move => P; apply; clear P.
            exists fx.
            move => P; apply; clear P.
            exists i.
            rewrite Hi; auto.
        + move => [[y1 y2] Hy] H0.
          simpl in H0.
          apply two_arg_paths.
          * apply is_sup => a.
            unfold In, pr1 => Ha.
            unfold ishinh, ishinh_UU in Ha.
            apply Ha => [[x Hx]]; clear Ha.
            apply Hx => [[i Hi]]; clear Hx.            
            move : (H0 i).
            induction (f i) as [fi Hfi].
            simpl in Hi.
            unfold pr1.
            rewrite <- Hi => H1.
            apply prod_dest in H1.
            induction H1; auto.
          * rewrite joinC; apply meet_join.
            apply is_inf => a.
            unfold In, pr1 => Ha.
            unfold ishinh, ishinh_UU in Ha.
            apply Ha => [[x Hx]]; clear Ha.
            apply Hx => [[i Hi]]; clear Hx.
            move : (H0 i).
            induction (f i) as [fi Hfi].
            simpl in Hi.
            unfold pr1.
            rewrite <- Hi => H1.
            apply prod_dest in H1.
            induction H1.
            apply meet_join; rewrite joinC; auto.
  use tpair.
  - unfold consistents.
    split with (@bot _ L ,, @top _ L  : L × L).
    apply bot_min.
  - simpl.
    move =>  /= [[x1 x2] Hx] /=.
    apply two_arg_paths.
    * apply bot_min.
    * rewrite joinC. apply meet_join. apply top_max.
Defined. 

Definition consistent_dcppo {T} (L : complat T) : dcppo := (Lc_hSet L),, (consistent_struct L).


Notation "L ^c" := (consistent_dcppo L) (at level 1).
Notation "X --> Y" := (monotone_function X Y).

Definition  exact_pair {T} {L : complat T} (x : L) : L^c := (x,,x),, (meetI x).

Definition partialApproximating {T} {L : complat T} (f : L^c --> L^c) :=
  forall x : L, pr11 (f (exact_pair x)) == pr21 (f (exact_pair x)).

Definition Appx {T} (L : complat T) : UU :=
  ∑ f : L^c --> L^c, partialApproximating f.


Definition kripke_kleene {T} {L : complat T} (f : L^c --> L^c) (Hf : partialApproximating f) 
  : L^c := pataraia f.

Definition partialApproximate {T} {L : complat T} (A : Appx L) (O : L -> L) :=
  forall x, pr11 A (exact_pair x) == (exact_pair (O x)).

Definition AppxOf {T} {L : complat T} (O : L -> L) :=
  ∑ A : Appx L, partialApproximate A O.


  
Lemma Appxof_fixpoint {T} {L : complat T} (O : L -> L) :
  forall (A : AppxOf O) (x : L), 
  pr111 A (exact_pair x) = (exact_pair x) <-> O x = x.
Proof.
  move => [[[f Hf] Hfc] HA] x /=.
  unfold partialApproximating, partialApproximate in *.
  specialize (HA x); simpl in HA.
  specialize (Hfc x); simpl in Hfc.
  split => H.
  * rewrite H in HA; clear H.
    inversion HA; auto.
  * rewrite H in HA; auto.
Qed.

  
Lemma Apprxof_KK {T} {L : complat T} (O : L -> L) :
  forall (A : AppxOf O) (x : T),
  O x = x -> kripke_kleene (pr21 A) ≤ exact_pair x.
Proof.
  move => A x Hx.
  apply  (Appxof_fixpoint A x) in Hx.
  induction A as [[f Hfx] b]; unfold pr1, pr2 in *.
  apply pataraia_is_leastfixpoint; auto.
Qed.  


Definition reliable {T} {L : complat T} (A : L^c -> L^c) (p : L^c) :=
  p ≤ A p.

Lemma Appx_leftrestriction {T} {L : complat T} (A : Appx L)
  (p : L^c) (Hp : reliable (pr11 A) p) (x : L) (Hl : ⊥ ≺ x) (Hr : x ≺ pr21 p) :  
  (⊥ : L) ≺ (pr11 (pr11 A ((x,, pr21 p),, Hr))) ×
  (pr11 (pr11 A ((x,, pr21 p),, Hr))) ≺ ((pr21 p) : L).
Proof.
  split.
  - apply bot_min.  
  - set Hf := pr2 A. 
    set f := pr11 A.
    set R := pr21 A.
    induction p as [[a b] Hab].
    unfold partialApproximating in Hf.
    unfold pr1, pr2 in *.    
    assert ((((x,, b),, Hr) : L^c) ≤ exact_pair b). {
      simpl.      
      apply two_arg_paths; auto.
      apply joinI.
    }    
    assert (((a,,b),, Hab : L^c) ≤ exact_pair b). {
      simpl. apply two_arg_paths; auto. apply joinI.      
    }
    move : (R _ _ X) => H0.
    move : (R _ _ X0) => H1.
    simpl in H0, H1, Hp.
    apply prod_dest in H0, H1, Hp.
    unfold pr1, pr2 in H0, H1, Hp.
    induction H0 as [H0 H0'], H1 as [H1' H1], Hp as [Hp1 Hp2].
    rewrite joinC in H1. apply meet_join in H1.
    rewrite joinC in Hp2. apply meet_join in Hp2.
    apply transL with ((pr11 (f (exact_pair b)))); auto.
    rewrite (Hf b).
    apply transL with (pr21 (f ((a,, b),, Hab))); auto.
Qed.

Lemma Appx_rightrestriction {T}  {L : complat T} (A : Appx L)
  (p : L^c) (Hp : reliable (pr11 A) p) (x : L) (Hl : pr11 p ≺ x) (Hr : x ≺ ⊤) :  
  ((pr11 p) : L)  ≺ (pr21 (pr11 A ((pr11 p,, x),, Hl))) ×
  (pr21 (pr11 A ((pr11 p,, x),, Hl))) ≺ (⊤ : L).
Proof.
   split; first last.
  - apply top_max.
  - induction A as [[f R] Hf].
    induction p as [[a b] Hab].
    unfold partialApproximating in Hf.
    unfold pr1, pr2 in *.    
    assert ((((a,, x),, Hl) : L^c) ≤ exact_pair a). {
      simpl.
      apply two_arg_paths; auto.
      apply meetI.
      rewrite joinC; apply meet_join; auto.
    }    
    assert (((a,,b),, Hab : L^c) ≤ exact_pair a). {
      simpl. apply two_arg_paths; auto.
      apply meetI.
      rewrite joinC; apply meet_join; auto.
    }
    move : (R _ _ X) => H0.
    move : (R _ _ X0) => H1.
    simpl in H0, H1, Hp.
    apply prod_dest in H0, H1, Hp.
    unfold pr1, pr2 in H0, H1, Hp.
    induction H0 as [H0 H0'], H1 as [H1' H1], Hp as [Hp1 Hp2].

    apply transL with (pr11 (f ((a,, b),, Hab))); auto.    
    apply transL with ((pr11 (f (exact_pair a)))); auto.
    rewrite (Hf a).
    rewrite joinC in H0'. apply meet_join in H0'; auto.
Qed.




Hypotheses lem : LEM.

Definition down_restriction (lem : LEM) {T} {L : complat T} (p : L^c) :=
  interval_complat lem  (bot_min T L (pr21 p)).

Definition up_restriction (lem : LEM) {T} {L : complat T} (p : L^c) :=
  interval_complat lem (top_max T L (pr11 p)).

Definition A1 {T} {L : complat T} (p : L^c) (A : Appx L) (Hp : reliable (pr11 A) p) :
  down_restriction lem p -> down_restriction lem p.
Proof.
  move => [x [Hb Ht]].
  split with (pr11 ((pr11 A) ((x,,(pr21 p)),, Ht))).
  apply (Appx_leftrestriction Hp Hb Ht).
Defined.

Definition A2 {T} {L : complat T} (p : L^c) (A : Appx L) (Hp : reliable (pr11 A) p) :
  up_restriction lem p -> up_restriction lem p.
Proof.
  move => [x [Hb Ht]].
  split with (pr21 ((pr11 A) ((pr11 p,,x),, Hb))).
  apply (Appx_rightrestriction Hp Hb Ht).
Defined.   

Lemma monoA1  {T} {L : complat T} (p : L^c) (A : Appx L) (Hp : reliable (pr11 A) p) :
  mono (A1 Hp).
Proof.
  move => [x Hx] [y Hy] H.
  induction A as [[f Hf] Hff].
  induction p as [[a b] ab].
  unfold A1, pr1, pr2.
  apply subtypePath => /=.
  apply isPredicate_interval.
  assert ((((x,, b),, pr2 Hx) : L^c)  ≤ ((y,, b),, pr2 Hy)). {
    simpl.
    apply two_arg_paths; first last.
    { apply joinI. }
    apply base_paths in H; auto.
  }
  move : (Hf _ _ X).
  move /base_paths; auto.
Qed.


Lemma monoA2 {T} {L : complat T} (p : L^c) (A : Appx L) (Hp : reliable (pr11 A) p) :
  mono (A2 Hp).
Proof.
  move => [x Hx] [y Hy] H.
  induction A as [[f Hf] Hff].
  induction p as [[a b] ab].
  apply subtypePath => /=.
  apply isPredicate_interval.
  assert ((((a,, y),, pr1 Hy) : L^c) ≤ (((a,, x),, pr1 Hx) : L^c) ). {
    simpl.
    apply two_arg_paths.
    { apply meetI. }
    apply base_paths in H.
    simpl in H.
    rewrite joinC; apply meet_join; auto.
  }  
  move : (Hf _ _ X) => H0.
  simpl in H0.
  apply prod_dest in H0.
  induction H0 as [H1 H2].
  unfold pr1, pr2 in *.
  apply meet_join; rewrite joinC; auto.
Qed.


Definition dlfp {T} {L : complat T} (p : L^c) (A : Appx L) (Hp : reliable (pr11 A) p) :=
  lfp (A1 Hp) (monoA1 Hp).

Definition ulfp {T} {L : complat T} (p : L^c) (A : Appx L) (Hp : reliable (pr11 A) p) :=
  lfp (A2 Hp) (monoA2 Hp).


Lemma dlfp_is_fixpoint {T} {L : complat T} (p : L^c) (A : Appx L) (Hp : reliable (pr11 A) p) :
  (A1 Hp) (dlfp Hp) = (dlfp Hp).
Proof.
  move : (tarski_lfp _ _ (A1 Hp) (monoA1 Hp)) => [Hfp Hlfp]; auto.
Qed.

Lemma ulfp_is_fixpoint {T} {L : complat T} (p : L^c) (A : Appx L) (Hp : reliable (pr11 A) p) :
  (A2 Hp) (ulfp Hp) = (ulfp Hp).
Proof.
  move : (tarski_lfp _ _ (A2 Hp) (monoA2 Hp)) => [Hfp Hlfp]; auto.
Qed.




Definition stable_revision {T} {L : complat T}  (A : Appx L) :
  ∏ P : (∑ p : L^c, reliable (pr11 A) p), down_restriction lem (pr1 P) × up_restriction lem (pr1 P) :=
  fun P => dlfp (pr2 P),, ulfp (pr2 P).

Definition stable_fixpoint {T} {L : complat T} (A : Appx L) (p : L^c) :=
  ∑ Hp : reliable (pr11 A) p, 
  pr11 p = pr11 (stable_revision (p,, Hp)) ×
  pr21 p = pr12 (stable_revision (p,, Hp)).

Lemma stable_fixpoint_fixpoint {T} {L : complat T} (A : Appx L) (p : L^c) :
  stable_fixpoint A p -> (pr11 A) p = p.
Proof.
  move => [Hr [H1 H2]].
  move : (dlfp_is_fixpoint Hr) => Hdfp.
  move : (ulfp_is_fixpoint Hr) => Hufp.
  unfold stable_revision in H1, H2.
  induction p as [[a b] Hab].
  unfold pr1,pr2 in *.
  assert (dlfp Hr = (a,, (bot_min _ _ a),, Hab)). {
    apply subtypePath => //=.
    apply isPredicate_interval.
    symmetry; auto.
  }
  assert (ulfp Hr = (b,, Hab,, (top_max _ _ b))). {
    apply subtypePath => //=.
    apply isPredicate_interval.
    symmetry; auto.
  }
  rewrite X in Hdfp.
  rewrite X0 in Hufp.
  apply base_paths in Hdfp, Hufp.
  simpl in *.
  apply subtypePath.
  { unfold isPredicate => x. apply propproperty. }
  simpl.
  induction A as [[f Hf] Hff].
  simpl in *.
  induction ((f ((a,, b),, Hab))) as [fp Hfp].
  eapply transportf with (pr11 (f ((a,, b),, Hab)),,pr21 (f ((a,, b),, Hab))).
  rewrite Hdfp Hufp; auto.
  set p := (f ((a,, b),, Hab)).
  induction p as [p Hp]; simpl.
  induction p as [n m]; simpl.
  auto.
Qed.  


Definition stable_fixpoint_of {T} {L : complat T} (O : L -> L) (A : AppxOf O) (x : L) :=
  stable_fixpoint (pr1 A) (exact_pair x).


Definition prudent {T} {L : complat T} (A : Appx L) (p : L^c) :=
  ∑ Hp : reliable (pr11 A) p, (pr11 p) ≺ (pr1 (dlfp Hp)).

Lemma stable_fixpoint_prudent {T} {L : complat T} (A : Appx L) (p : L^c) :
  stable_fixpoint A p -> prudent A p.
Proof.
  move => [Hp [H1 H2]].
  exists Hp.
  induction p as [[a b] Hab].
  unfold stable_revision, pr1,pr2 in *.
  apply (transportb (fun x => x ≺ pr1 (dlfp Hp)) H1 (meetI  _)).
Qed.  

Lemma a_au  {T} {L : complat T} (A : Appx L) (p : L^c) (Hp : reliable (pr11 A) p) :
  (pr11 p) ≺ (pr1 (ulfp Hp)).
Proof.
  set a :=  (ulfp Hp).
  induction a as [a [H1 H2]]; auto.
Qed.

Lemma bd_b {T} {L : complat T} (A : Appx L) (p : L^c) (Hp : reliable (pr11 A) p) :
  (pr1 (dlfp Hp)) ≺ (pr21 p).
Proof.
  set b := (dlfp Hp).
  induction b as [b [H1 H2]]; auto.
Qed.

Lemma au_b {T} {L : complat T} (A : Appx L) (p : L^c) (Hp : reliable (pr11 A) p) :
   (pr1 (ulfp Hp)) ≺ (pr21 p).
Proof.  
  assert (A2 Hp (pr21 p,, pr2 p,, top_max _ _ (pr21 p) ) ≺ (pr21 p,, pr2 p,, top_max _ _ (pr21 p) )). {
    apply subtypePath.
    apply isPredicate_interval.
    induction p as [[a b] Hab].
    simpl.
    rename Hp into Hr.
    unfold reliable in Hr.
    simpl in Hr.
    apply prod_dest in Hr.
    induction Hr.
    apply meet_join. rewrite joinC; auto.
  }
  move : (lfp_prefixpoint _ _ (A2 Hp) (monoA2 Hp) (pr21 p,, pr2 p,, top_max _ _ (pr21 p)) X).
  move /base_paths; auto.
Qed.

Section stable_consistent.

Variable T : hSet.
Variable L : complat T.
Variable A : Appx L.
Variable p : L^c.
Variable H : reliable (pr11 A) p.

Let a := (pr11 p).
Let b := (pr21 p).

Notation "a↑" := (pr1 (ulfp H)).
Notation "b↓" := (pr1 (dlfp H)).

Let au_b := (au_b H).
Let a_au := (a_au H).
Let bd_b := (bd_b H).



(*a↑,b ≤ a↑,a↑*)
Local Lemma aub_auau :
  (((a↑,, b),, au_b) : L^c) ≤ ((a↑,, a↑),, meetI a↑).
Proof.
  simpl.
  move : (meetI (pr1 (ulfp H))) => Hk.
  rewrite Hk.
  move : au_b => Hb.
  apply meet_join in Hb. rewrite joinC in Hb.
  rewrite Hb; auto. 
Qed.

(* a,,a↑ ≤ a↑,,a↑ *)
Local Lemma aau_auau :
  ((a,, a↑),, a_au : L ^c) ≤ (a↑,, a↑),, meetI (X:=T) (l:=L) a↑.
Proof.
  simpl.  
  rewrite a_au.
  rewrite joinI; auto.
Qed.



  
Lemma ulfp_prefixpoint :
  A1 (H)  (a↑,, bot_min _ _ a↑,, au_b) ≺  (a↑,, bot_min _ _ a↑,, au_b).
Proof.
  
  set Hm := (pr21 A).
  move : (Hm _ _ aau_auau) => Ha.
  move : (Hm _ _ aub_auau) => Hb.
  simpl in Ha, Hb.
  apply prod_dest in Ha, Hb. unfold pr1,pr2 in *.
  induction Ha as [_ Ha].
  induction Hb as [Hb _].
  apply subtypePath.
  apply isPredicate_interval.
  unfold A1; simpl.
  apply transL with ((pr11 ((pr11 A) ((a↑,, a↑),, meetI (X:=T) (l:=L) a↑)))); auto.
  move : ((pr2 A) a↑).
  unfold exact_pair.
  move ->.
  rewrite joinC in Ha. apply meet_join in Ha. 
  apply transL with (pr21 ((pr11 A) ((a,, a↑),, a_au))); auto.

  move : (tarski_lfp _ _ (A2 (H)) (monoA2 (H))) => [Hfp _].
  apply base_paths in Hfp.    
  simpl in Hfp.
  (* change (pr1 (lfp (A2 (H)) (monoA2 (H)))) with a↑ in Hfp. *)
  move : (propproperty (a ≺ a↑)) => Hc.
  move : (Hc a_au ( pr12 (lfp (A2 (H)) (monoA2 (H))))) => [c hc].
  rewrite c Hfp.
  apply meetI.
Qed.  


Lemma stable_consistent :
    @consistent T L (b↓,, a↑).
Proof.
  move : (lfp_prefixpoint _ _ (A1 H) (monoA1 H) _ ulfp_prefixpoint).
  move /base_paths => H0; auto.
Qed.



End stable_consistent.


Section prudent.

Variable T : hSet.
Variable L : complat T.
Variable A : Appx L.
Variable p : L^c.
Variable H : prudent A p.

Let a := (pr11 p).
Let b := (pr21 p).

Notation "a↑" := (pr1 (ulfp (pr1 H))).
Notation "b↓" := (pr1 (dlfp (pr1 H))).

Let au_b := (au_b (pr1 H)).
Let a_au := (a_au (pr1 H)).
Let bd_b := (bd_b (pr1 H)).
Let stable_consistent := (stable_consistent (pr1 H)).




Lemma stable_pricise :
  p ≤ ((b↓,, a↑),, stable_consistent).
Proof.
  simpl.
  rewrite (pr2 H).
  rewrite joinC.
  move : au_b => Hb.
  apply meet_join in Hb.
  rewrite Hb.
  auto.
Qed.  



(* (b↓,b) ≤ (b↓,a↑) *)
Local Lemma bdb_bdau :
  (((b↓,, b),, bd_b) : L^c) ≤ ((b↓,, a↑),, stable_consistent).
Proof.
  simpl.
  rewrite meetI.
  move : au_b => Hb.
  apply meet_join in Hb.
  rewrite joinC Hb; auto.
Qed.

(* (a, a↑) ≤ (b↓, a↑) *)
Local Lemma aau_bdau :
  ((a,, a↑),, a_au : L^c) ≤ ((b↓,, a↑),, stable_consistent).
Proof.
  simpl.
  rewrite (pr2 H).
  rewrite joinI.
  auto.
Qed.

Lemma stable_reliable : 
  reliable (pr11 A) ((b↓,, a↑),, stable_consistent).
Proof.
  simpl.
  apply two_arg_paths.
  - move : (tarski_lfp _ _ (A1 (pr1 H)) (monoA1 (pr1 H))) =>  [Hfp _].
    apply base_paths in Hfp.    
    simpl in Hfp.
    (* change (pr1 (lfp (A1 (pr1 H)) (monoA1 (pr1 H)))) with b↓ in Hfp. *)
    move : (propproperty (b↓ ≺ b)) => Hc.
    move : (Hc (pr22 (lfp (A1 (pr1 H)) (monoA1 (pr1 H)))) bd_b) => [E _].
    rewrite E in Hfp.
    apply transL with (pr11 ((pr11 A) ((b↓,, b),, bd_b))).
    * rewrite Hfp. apply meetI.
    * move : ((pr21 A) _ _ bdb_bdau) => /= Hb.
      apply prod_dest in Hb.
      induction Hb; auto.
  - move : (tarski_lfp _ _ (A2 (pr1 H)) (monoA2 (pr1 H))) =>  [Hfp _].
    apply base_paths in Hfp.    
    simpl in Hfp.
    (* change (pr1 (lfp (A2 (pr1 H)) (monoA2 (pr1 H)))) with a↑ in Hfp. *)
    move : (propproperty (a ≺ a↑)) => Hc.
    move : ((Hc (pr12 (lfp (A2 (pr1 H)) (monoA2 (pr1 H))))) a_au) => [E _].
    rewrite E in Hfp.
    rewrite joinC; apply meet_join.
    apply transL with (pr21 ((pr11 A) ((a,, a↑),, a_au))); first last.
    * rewrite Hfp. apply meetI.
    * move : ((pr21 A) _ _ aau_bdau) => /= Hb.
      apply prod_dest in Hb.
      apply meet_join. rewrite joinC.
      induction Hb; auto.
Qed.



(* (x,, b) ∈ L^c *)
Local Definition xb (x : L) (Hx : x ≺ a↑) : L^c.
Proof.
  split with (x,,b); simpl.
  apply transL with a↑; auto.
Defined.

(* (x,, a↑) ∈ L^c*)
Local Definition xau (x : L) (Hx : x ≺ a↑) : L^c.
Proof.
  split with (x,,a↑); auto.
Defined.

Local Lemma xb_xau x (Hx : x ≺ a↑) :
  xb Hx ≤ xau Hx.
Proof.
  simpl.
  rewrite meetI.
  move : au_b => Hb.
  apply meet_join in Hb.
  rewrite joinC Hb; auto.
Qed.

Local Lemma Axb_Axau x (Hx : x ≺ a↑) :
  (pr11 A) (xb Hx) ≤ (pr11 A) (xau Hx).
Proof.
  apply (pr21 A).
  apply xb_xau.
Qed.  


Local Lemma Axau_au x (Hx : x ≺ a↑) :
  pr11 ((pr11 A) (xau Hx)) ≺ a↑.
Proof.
  auto.
  unfold xau.
  move : stable_reliable => Hr.
  unfold reliable in Hr.
  simpl in Hr.
  apply prod_dest in Hr.
  unfold pr1,pr2 in Hr.
  induction Hr as [Hb Ha].
  rewrite joinC in Ha.
  apply meet_join in Ha.
  apply transL with (pr21 ((pr11 A) ((b↓,, a↑),, stable_consistent))); auto.
  assert ((((b↓,, a↑),, stable_consistent) : L^c) ≤ ((a↑,, a↑),, meetI a↑)). {
    simpl.
    apply two_arg_paths; auto.
    apply joinI.
  }
  move : (pr21 A _ _ X) => H0.
  apply prod_dest in H0.
  induction H0 as [_ H2].
  simpl in H2.
  rewrite joinC in H2.
  apply meet_join in H2.
  apply transL with (pr21 ((pr11 A) ((a↑,, a↑),, meetI (X:=T) (l:=L) a↑))); auto.
  move : (pr2 A a↑).
  unfold exact_pair.
  move <-.
  suff : (pr11 A) ((x,, a↑),, Hx) ≤ (pr11 A) ((a↑,, a↑),, meetI (X:=T) (l:=L) a↑). 
  { move /base_paths; auto. }
  apply (pr21 A).
  simpl. apply two_arg_paths; auto.
  apply joinI.
Qed.  




Lemma stable_prudent :
  prudent A ((b↓,, a↑),, stable_consistent).
Proof.
  unfold prudent.
  exists stable_reliable.
  simpl.
  move : (tarski_lfp _ _ (A1 (pr1 H)) (monoA1 (pr1 H))) => [Hfp1 Hlfp1]; auto.
  apply base_paths in Hfp1.
  simpl in Hfp1.
  (* change (pr1 (lfp (A1 (pr1 H)) (monoA1 (pr1 H)))) with b↓ in *. *)

  move : (tarski_lfp _ _  (A1  stable_reliable) (monoA1  stable_reliable)) => [Hfp2 Hlfp2].
  apply base_paths in Hfp2.
  simpl in Hfp2, H.
  (* change (pr1 (lfp (A1 (pr1 H)) (monoA1 (pr1 H)))) with b↓ in *. *)
  (* change (lfp (A1 stable_reliable) (monoA1 stable_reliable)) with (dlfp stable_reliable) in *. *)
  
  move : (Axb_Axau stable_consistent) => Hbd.
  apply base_paths in Hbd. 
  unfold xb, xau in Hbd.
  simpl in Hbd.
  move : (propproperty (b↓ ≺ b) 
    (pr22 (lfp (A1 (pr1 H)) (monoA1 (pr1 H))))
    (transL (X:=L) (l:=L) (a:=b↓) (b:=a↑) (c:=b) stable_consistent au_b)
  ) => [E _].
  rewrite <- E in Hbd. clear E.
  rewrite Hfp1 in Hbd.
  move : (propproperty (b↓ ≺ b)
    (pr22 (lfp (A1 (pr1 H)) (monoA1 (pr1 H))))  bd_b ) => [E _].
  rewrite E in Hfp1. clear E.
  
  move : (Axau_au stable_consistent) => Hau.

  move : (Axb_Axau) => HA.
  assert (forall x (Hx : x ≺ a↑), 
    pr11 ((pr11 A) (xau Hx))  ≺ x -> 
    pr11 ((pr11 A) (xb Hx)) ≺ x). {
    move => x Hx Hxa.
    move : (Axb_Axau Hx) => Hxb.
    apply base_paths in Hxb.
    simpl in Hxb.
    apply transL with (pr11 ((pr11 A) (xau Hx))); auto.    
  }
  unfold xb, xau in X.
  unfold dlfp in Hfp1.
  assert ( forall x,
    A1 stable_reliable x ≺ x  ->
    pr1 (lfp (A1 (pr1 H)) (monoA1 (pr1 H))) ≺ pr1 x
  ). {
    move => [x [Hx' Hx]] H0.
    unfold pr1, pr2 in *.
    (* unfold A1 in H0. *)
    apply base_paths in H0.
    simpl in H0.
    apply X in H0.
    suff : 
      (lfp (A1 (pr1 H)) (monoA1 (pr1 H)))
      ≺
      (x,, bot_min _ _ x ,, (transL Hx au_b)).
    { move /base_paths; auto. }
    apply lfp_prefixpoint.
    apply subtypePath; auto.
    apply isPredicate_interval.
  }
  eapply X0.
  apply subtypePath; simpl.
  apply isPredicate_interval.
  rewrite Hfp2.
  apply meetI.
Qed.  

End prudent.



Section stable_monotonicity.

Variable T : hSet.
Variable L : complat T.
Variable A : Appx L.
Variable p q : L^c.
Variable Hp : reliable (pr11 A) p.
Variable Hq : prudent A q.
Variable Hpq : p ≤ q.

Let a := (pr11 p).
Let b := (pr21 p).
Let c := (pr11 q).
Let d := (pr21 q).

Let Hr := (pr1 Hq).
Let Hpr := (pr2 Hq).

Local Notation "a↑" := (pr1 (ulfp Hp)).
Local Notation "b↓" := (pr1 (dlfp Hp)).
Local Notation "c↑" := (pr1 (ulfp (pr1 Hq))).
Local Notation "d↓" := (pr1 (dlfp (pr1 Hq))).


Local Notation a_b := (pr2 p).
Local Notation c_d := (pr2 q).
Local Notation dd_cu := (stable_consistent T L A q Hq).

Local Lemma a_c :
  @le T L a c.
Proof.
  apply prod_dest in Hpq; simpl in Hpq.
  induction Hpq; auto.
Qed.

Local Lemma d_b :
  @le T L d b.
Proof.
  apply prod_dest in Hpq; simpl in Hpq.
  induction Hpq; auto.
  apply meet_join; rewrite joinC; auto.
Qed.

Let c_cu := a_au Hr.
Let dd_d := bd_b Hr.
Let cu_d := au_b Hr.

Let a_au := a_au Hp.
Let bd_b := bd_b Hp.
Let au_b := au_b Hp.




Definition dd' : down_restriction lem p.
Proof.
  split with (d↓); split.
  - apply bot_min.
  - apply transL with d.
    apply dd_d.
    apply d_b.
Defined.


Lemma dd_prefix :
  A1 Hp dd' ≺  dd'.
Proof.
  apply subtypePath => /=.
  apply isPredicate_interval.
  move : (tarski_lfp _ _ (A1 Hr) (monoA1 Hr)) => [Hfp Hlfp]; auto.
  apply base_paths in Hfp.
  (* change (pr1 (lfp (A1 Hr) (monoA1 Hr))) with d↓ in Hfp. *)
  apply transL with (pr1 (A1 Hr (lfp (A1 Hr) (monoA1 Hr)))); first last.
  { rewrite Hfp. apply meetI. }

  set x := (lfp (A1 Hr) (monoA1 Hr)).
  unfold A1; simpl; unfold x.

  suff : 
  (pr11 A) ((d↓,, b),, transL dd_d d_b) 
  ≤
  ((pr11 A)
          ((pr1 (lfp (A1 Hr) (monoA1 Hr)),, d),,
          pr22 (lfp (A1 Hr) (monoA1 Hr)))).
  { move /base_paths; auto. }
  apply (pr21 A).
  simpl.
  move : d_b => d_b.
  apply meet_join in d_b.
  rewrite joinC d_b.
  rewrite meetI; auto.
Qed.    

Lemma bd_dd :
  b↓ ≺ d↓.
Proof.
  move : (lfp_prefixpoint _ _ _ (monoA1 Hp) _ (dd_prefix)).
  move /base_paths; auto.
Qed.

Lemma a_dd :
  a ≺ d↓.
Proof.
  move : (stable_pricise (Hr,, Hpr)) => H0.
  move : (trans_dcpo Hpq H0).
  move /base_paths; auto.
Qed.


Let u := (meet a↑ d↓).

Lemma u_au :
  u ≺ a↑.
Proof.
  unfold u.
  apply (meet_lowb a↑ d↓).
Qed.  

Lemma a_u :
  a ≺ u.
Proof.
  unfold u.
  apply meet_inf.
  - apply a_au.
  - apply a_dd.
Qed.  

Lemma u_dd :
  u ≺ d↓.
Proof.
  unfold u.
  apply meet_lowb.
Qed.

Definition u' : down_restriction lem q.
Proof.
  split with u; split.
  - apply bot_min.
  - apply transL with d↓.
    * apply u_dd.
    * apply dd_d.
Defined.
    


Lemma u_prefixpoint :
  A1 Hr u' ≺ u'.
Proof.
  apply subtypePath => /=.
  apply isPredicate_interval.
  apply meet_inf.
  - move : (tarski_lfp _ _ (A2 Hp) (monoA2 Hp)) => [Hfp _]; auto.
    apply base_paths in Hfp.
    change (pr1 (lfp (A2 Hp) (monoA2 Hp))) with a↑ in Hfp.
    rewrite <- Hfp; clear Hfp.
    set x := (lfp (A2 Hp) (monoA2 Hp)).
    unfold A2, pr1, pr2, x.
    (* change (pr1 (lfp (A2 Hp) (monoA2 Hp))) with a↑. *)
    eapply transL with (pr21 ((pr11 A) ((u,,u),, meetI u))); first last.
    * suff : 
      ((pr11 A) ((a,, a↑),, pr12 (lfp (A2 Hp) (monoA2 Hp))))
      ≤
      ((pr11 A) ((u,, u),, meetI u)).
      { 
       move => /= H0.
       apply prod_dest in H0.
       induction H0 as [_ H0].
       simpl in H0.
       apply meet_join; rewrite joinC; auto.
      }
      apply (pr21 A); simpl.
      apply two_arg_paths; auto.
      + apply a_u.
      + rewrite joinC; apply meet_join.
        apply u_au.
    * move : (pr2 A u).
      unfold exact_pair.
      move <-.
      suff : 
        ((pr11 A) ((u,, d),, transL u_dd dd_d))
        ≤
        ((pr11 A) ((u,, u),, meetI u)).
      { move /base_paths; auto. }
      apply (pr21 A); simpl.
      apply two_arg_paths; auto.
      + apply meetI.
      + rewrite joinC; apply meet_join.
        apply transL with d↓.
        * apply u_dd.
        * apply dd_d.
  - move : (tarski_lfp _ _ (A1 Hr) (monoA1 Hr)) => [Hfp _]; auto.
    apply base_paths in Hfp.
    (* change (pr1 (lfp (A1 Hr) (monoA1 Hr))) with d↓ in Hfp. *)
    apply transL with (pr1 (A1 Hr (lfp (A1 Hr) (monoA1 Hr)))); first last.
    { rewrite Hfp. apply meetI. }
    clear Hfp.
    set x := (lfp (A1 Hr) (monoA1 Hr)).
    unfold A1, pr1, pr2, x.
    suff : 
      ((pr11 A) ((u,, d),, transL u_dd dd_d))
      ≤ 
      ((pr11 A) ((d↓,, d),, pr22 (lfp (A1 Hr) (monoA1 Hr)))).
    { move /base_paths; auto. }
    apply (pr21 A); simpl.
    rewrite u_dd joinI; auto.
Qed.

Lemma dd_au :
  d↓ ≺ a↑.
Proof.
  apply transL with u; first last.
  - apply u_au.
  - move : (lfp_prefixpoint _ _ _ (monoA1 Hr) _ u_prefixpoint).
    move /base_paths; auto; simpl.
Qed.

Definition au' :up_restriction lem q.
Proof.
  split with (a↑); split; first last.
  - apply top_max.
  - apply transL with (d↓); first last.
    * apply dd_au.
    * exact Hpr.
Defined.

Lemma au_prefixpoint :
  A2 Hr au' ≺ au'.
Proof.
  apply subtypePath.
  apply isPredicate_interval.
  simpl.
  move : (tarski_lfp _ _ (A2 Hp) (monoA2 Hp)) => [Hfp _].
  apply base_paths in Hfp.
  (* change (pr1 (lfp (A2 Hp) (monoA2 Hp))) with a↑ in Hfp. *)
  apply transL with (pr1 (A2 Hp (lfp (A2 Hp) (monoA2 Hp)))); first last.
  { rewrite Hfp. apply meetI. }
  set x := (lfp (A2 Hp) (monoA2 Hp)).
  unfold A2, pr1, pr2, x.

  suff : 
    (pr11 A) ((a,, a↑),, pr12 (lfp (A2 Hp) (monoA2 Hp)))
    ≤
    ((pr11 A) ((c,, a↑),, transL Hpr dd_au)).
  {
    move => /= H0.
    apply prod_dest in H0.
    induction H0 as [_ H0].
    simpl in H0.
    apply meet_join; rewrite joinC; auto.
  }
  apply (pr21 A); simpl.
  rewrite a_c joinI; auto.
Qed.

Lemma cu_au :
  c↑ ≺ a↑.
Proof.
  move : (lfp_prefixpoint _ _ _ (monoA2 Hr) _ au_prefixpoint).
  move /base_paths; auto.
Qed.


Lemma stable_monotonicity :
  ((b↓,,a↑) : L^2) ≺k (d↓,,c↑).
Proof.
  simpl.
  apply two_arg_paths.
  - apply bd_dd.
  - rewrite joinC.
    apply meet_join.
    apply cu_au.
Qed.    

End stable_monotonicity.

Definition stable_revision' {T} {L : complat T}  (A : Appx L) (p : L^c) (Hp : reliable (pr11 A) p) : L^2 :=  
  pr11 (stable_revision (p,, Hp)),, pr12 (stable_revision (p,, Hp)).


Lemma stable_fixpoint_monotonicity {T} {L : complat T} (A : Appx L) (p q : L^c) 
  (Hp : stable_fixpoint A p)(Hq : reliable (pr11 A) q) :
  q ≤ p ->  stable_revision' Hq ≺k pr1 p.
Proof.
  move => H.
  move : (stable_fixpoint_prudent Hp) => Hpr.
  move : (stable_monotonicity Hq Hpr H) => H0.
  simpl in H0.
  apply prod_dest in H0. simpl in H0.
  induction H0 as [H1 H2].
  induction p as [[c d] Hcd].
  induction Hp as [Hr [Hc Hd]].
  unfold stable_revision, pr1, pr2 in Hc,Hd.
  move : (propproperty (reliable (pr11 A) ((c,, d),, Hcd)) Hr (pr1 Hpr)) => [E _].
  rewrite E in Hc, Hd; clear E.
  unfold stable_revision'.
  simpl.    
  apply two_arg_paths.
  - rewrite Hc; auto.
  - rewrite Hd; auto.
Qed.



Definition prudent_chain {T} {L : complat T} (A : Appx L) :=
  ∑ C : directed_set (L^c), (∏ i, prudent A (pr12 C i)).


Section prudent_chain_lub_prudent.

Variable T : hSet.
Variable L : complat T.
Variable A : Appx L.
Variable PC : prudent_chain A.
(* Let C := pr1 PC. *)
Let I := (pr11 PC).
Let f := (pr121 PC).
Let Hdr := (pr221 PC).
Let Hpr := (pr2 PC).
Let X := (dcpo_lub (pr1 PC)).
Let asup := (pr11 X).
Let binf := (pr21 X).


Local Lemma fi_X :
  forall i, f i ≤ X.
Proof.  
  move => i.
  induction (f i) as [[a b] Hab] eqn:E.
  simpl.
  apply two_arg_paths.
  * apply is_upb.
    unfold In.
    move => P; apply; clear P.
    exists b.
    move => P; apply; clear P.
    exists i => /=.    
    unfold f in E.
    unfold directed_set_map.
    rewrite E; auto.
  * rewrite joinC. apply meet_join.
    apply is_lowb.
    unfold In.
    move => P; apply; clear P.
    exists a.
    move => P; apply; clear P.
    exists i.
    unfold f in E.
    unfold directed_set_map.
    rewrite E; auto.
Qed.

Lemma prudent_chain_lub_reliable :
  reliable (pr11 A) X.
Proof.
  assert (forall i, reliable (pr11 A) (f i)) as Hr. {
    move => i; move : (Hpr i) => [Hr]; auto.
  }
  unfold reliable in *.
  move : fi_X => fi_X.
  unfold reliable in *.
  assert (forall i, (pr11 A) (f i) ≤ (pr11 A) X) as HX'. {
    move => i.
    apply (pr21 A).
    apply (fi_X i).
  }
  simpl.
  apply two_arg_paths.
  * apply is_sup => x.
    unfold In => Hx.
    unfold ishinh, ishinh_UU in Hx.
    apply Hx => [[y Hy]].
    apply Hy => [[i Hi]].    
    apply transL with  (pr11 ((pr11 A) (f i))); eauto.
    * move : (Hr i) => Hf.
      unfold f in *.    
      unfold directed_set_map in *.  
      induction ((pr121 PC) i) as [[n m] Hnm] eqn:E.      
      simpl in Hi.
      apply prod_dest in Hi.
      simpl in Hi.
      induction Hi as [H1 H2].
      induction H1, H2.
      simpl in Hf.
      apply prod_dest in Hf.
      simpl in Hf.
      induction Hf; auto.
    * move : (HX' i) => Hi'.
      simpl in Hi'.
      apply prod_dest in Hi'.
      simpl in Hi'.
      induction Hi' as [H1 H2]; auto.
  * rewrite joinC. apply meet_join.
    apply is_inf => x.    
    unfold In => Hx.
    unfold ishinh, ishinh_UU in Hx.
    apply Hx => [[y Hy]].
    apply Hy => [[i Hi]].
    apply transL with  (pr21 ((pr11 A) (f i))); eauto.
    * move : (HX' i) => Hi'.
      apply meet_join; rewrite joinC.
      simpl in Hi'.
      apply prod_dest in Hi'.
      simpl in Hi'.
      induction Hi' as [H1 H2]; auto.
    * move : (Hr i) => Hf.
      apply meet_join; rewrite joinC.
      unfold f in *.
      unfold directed_set_map in *.
      induction ((pr121 PC) i) as [[n m] Hnm].
      simpl in Hi.
      apply prod_dest in Hi.
      simpl in Hi.
      induction Hi as [H1 H2].
      induction H1, H2.
      simpl in Hf.
      apply prod_dest in Hf.
      simpl in Hf.
      induction Hf; auto.
Qed. 


Local Lemma x_fi i (x : L) (Hx : x ≺ binf) :
  x ≺ pr21 (f i).
Proof.
  move : (fi_X i) => HX.
  simpl in HX.
  apply prod_dest in HX.
  simpl in HX.
  induction HX as [H1 H2].
  rewrite joinC in H2.
  apply meet_join in H2.
  eapply transL; eauto.
Qed.


Local Lemma Afi_Afibinf (i : I) (x : L) (Hx : x ≺ binf) :
  (pr11 ((pr11 A) (((x,, pr21 (f i)),, x_fi i Hx) ))  : L ) ≺ (pr11 ((pr11 A) ((x,, binf),, Hx))).
Proof.
  suff :
    ((pr11 A) ((x,, pr21 (f i)),, x_fi i Hx))
    ≤
    ((pr11 A) ((x,, binf),, Hx)).
  { move /base_paths; auto. }
  apply (pr21 A).
  simpl.
  apply two_arg_paths.
  { apply meetI. }
  rewrite joinC; apply meet_join.
  apply is_lowb.
  unfold In => P; apply; clear P.
  exists (pr11 (f i)) => P; apply; clear P .
  exists i.
  auto.
Qed.

Local Lemma binf_prefix (i : I) (x : L) (Hx : x ≺ binf) :
  (pr11 ((pr11 A) ((x,, binf),, Hx)): L) ≺ binf.
Proof.
  move : prudent_chain_lub_reliable.
  unfold reliable => H.
  simpl in H; apply prod_dest in H; unfold pr1,pr2 in H; induction H as [H1 H2].
  rewrite joinC in H2; apply meet_join in H2.
  apply transL with ((pr21 ((pr11 A) X))); auto.
  assert (X ≤ ((binf,,binf),, meetI binf : L^c)) as HX. {
    simpl. apply two_arg_paths; first last.
    { apply joinI. }
    move : (pr2 X); auto.
  }  
  move : ((pr21 A) _ _ HX) => HXX.  
  simpl in HXX.
  apply prod_dest in HXX. simpl in HXX. induction HXX as [h1 h2].  
  rewrite joinC in h2. apply meet_join in h2.
  eapply transL; first last.
  { apply h2. }
  move : (pr2 A binf).
  unfold exact_pair => <-.  
  suff : 
    ((pr11 A) ((x,, binf),, Hx))
    ≤
    ((pr11 A) ((binf,, binf),, meetI binf)).
  { move /base_paths; auto. }
  apply (pr21 A); simpl.
  apply two_arg_paths; first last; auto.
  apply joinI. 
Qed.

 
Local Definition x' i (x : L) (Hx : x ≺ binf)  : down_restriction lem (f i).
Proof.
  split with x. split.
  apply bot_min.
  move : (fi_X i) => H0.
  simpl in H0.
  apply prod_dest in H0.
  simpl in H0.
  induction H0 as [H1 H2].
  rewrite joinC in H2.
  apply meet_join in H2.
  eapply transL; eauto.
Defined.

Local Lemma pre_pre (i : I) x :
  A1 prudent_chain_lub_reliable x ≺ x ->
  (pr1 (lfp (A1 (pr1 (Hpr i))) (monoA1  (pr1 (Hpr i))))) ≺ pr1 x.
Proof.
  move => H.
  induction x as [x [Hb Ht]].
  unfold pr1.
  suff :
    (lfp (A1 (pr1 (Hpr i))) (monoA1 (pr1 (Hpr i)))) ≺ x' i Ht.
  { move /base_paths; auto. }  
  apply lfp_prefixpoint.  
  unfold A1.  
  (* change  (pr1 (x' i Ht)) with x. *)
  apply subtypePath; auto.
  apply isPredicate_interval.
  unfold pr1. 
  eapply transL; unfold pr1.
  - move : (propproperty (x ≺ pr21 (f i)) (x_fi i Ht) (pr22 (x' i Ht))) => [E _].
    move : (Afi_Afibinf i Ht).
    rewrite E. apply.
  - 
    (* change (pr1 (x' i Ht)) with x. *)
    apply base_paths in H.
    simpl in H.
    eapply transL; first last.
    { apply H. }
    apply meetI.
Qed.

  
Lemma prudent_chain_lub_prudent :
  prudent A X.
Proof.
  unfold prudent.
  exists prudent_chain_lub_reliable.
  apply is_sup => x.
  unfold In, ishinh, ishinh_UU.
  apply => [[y]].
  apply => [[i Hi]].
   unfold f, directed_set_map in *.
  induction ((pr121 PC) i) as [[x_ y_] xy] eqn:E.
  simpl in Hi.
  apply prod_dest in Hi. simpl in Hi. induction Hi as [Hx_ Hy_].
  induction Hx_, Hy_.
  eapply transL.
  { move : (pr2 (Hpr i)).
    replace (pr11 ((pr121 PC) i)) with x.    
    apply.
    rewrite E; auto.
  }
  move : (tarski_lfp _ _ (A1 prudent_chain_lub_reliable) (monoA1 prudent_chain_lub_reliable)) => [Hfp Hflp].
  eapply pre_pre.
  unfold dlfp.
  rewrite Hfp.
  apply meetI.
Qed.

End prudent_chain_lub_prudent.





Lemma prudent_isaprop {T} (L : complat T) (A : Appx L) l : 
  isaprop (prudent A l).
Proof.
  unfold prudent.
  apply isaprop_total2.
Qed.

Definition prudent_hProp {T} (L : complat T) (A : Appx L) l : hProp := make_hProp (prudent A l) (prudent_isaprop (A := A) (l := l)).

Definition dcpoLcp {T} (L : complat T) (A : Appx L): dcpo.
Proof.
  eapply (sub_dcpo (L^c) (fun l => prudent_hProp A l)).
  move => D HD /=.
  apply (prudent_chain_lub_prudent (D,, HD)).
Defined.

Definition dcppoLcp {T} (L : complat T) (A : Appx L): dcppo.
Proof.
  set l := dcpoLcp A.
  exists (pr1 l).
  exists (pr2 l).  
  use tpair => /=.
  - exists (⊥_{L^c}).
    use tpair => /=.
    * apply two_arg_paths.
      + apply bot_min.
      + rewrite joinC; apply meet_join; apply top_max.
    * apply bot_min.
  - simpl => y.
    apply two_arg_paths.
    + apply bot_min.
    + rewrite joinC; apply meet_join; apply top_max.
Defined.

Section well_founded_fixpoint.
  


Variable T : hSet.
Variable L : complat T.
Variable A : Appx L.

Definition WF_iter : dcppoLcp A -> dcppoLcp A.
Proof.
  move => [l Hl].
  exists ((stable_revision' (pr1 Hl)),, (stable_consistent (pr1 Hl))).
  unfold stable_revision', stable_revision, pr1, pr2.
  exact (stable_prudent Hl).
Defined.


Lemma WF_iter_mono :
  is_monotone (dcppoLcp A) (dcppoLcp A) WF_iter.
Proof.
  move => x y H.
  eapply stable_monotonicity; simpl; auto. 
Qed.

Definition well_founded  : dcppoLcp A := pataraia (WF_iter,, WF_iter_mono).


Lemma well_founded_stable_fixpoint :
  stable_fixpoint A (pr1 well_founded).
Proof.    
  use tpair.
  - suff : prudent A (pr1 well_founded); auto.
    - move => [Hr _]; auto.
    - apply (pr2 well_founded).
  - 
    suff : (pr11 well_founded = (pr1 (dlfp (pr12 well_founded)),, pr1 (ulfp (pr12 well_founded)))). {
      move /prod_dest; auto.
    }
    move : (pataraia_is_fixpoint (WF_iter,, WF_iter_mono)) => H.
    apply base_paths in H.
    apply base_paths in H.
    unfold well_founded.
    rewrite <- H.
    auto.
Qed.

End well_founded_fixpoint.



Definition pointwise (T : hSet) (L : complat T) (A B : Appx L) :=
 ∏ p, pr11 A p ≤ pr11 B p.

Notation "A ⊏ B" := (pointwise A B)(at level 30).

Lemma pointwise_isaprop (T : hSet) (L : complat T) (A B : Appx L) :
  isaprop (A ⊏ B).
Proof.
  apply impred_isaprop => p.
  apply (propproperty ((pr11 A) p ≤ (pr11 B) p)).
Qed.

Definition pointwise_hProp (T : hSet) (L : complat T) (A B : Appx L) : hProp :=
  make_hProp (A ⊏ B) (pointwise_isaprop (A := A) (B := B)).


Lemma pointwise_approximate T (L : complat T) (A B : Appx L) :
  A ⊏ B -> ∃ O, partialApproximate A O × partialApproximate B O.
Proof.
Abort.

Section pointwise_order_monotonic.

Variable T : hSet.
Variable L : complat T.
Variable A B : Appx L.
Hypotheses H : A ⊏ B.


Lemma Aprudent_Breliable p :
  prudent A p -> reliable (pr11 B) p.
Proof.
  move => [Hr Hp].
  eapply trans_dcpo; eauto.
Qed.


Lemma Adlfp_Bdlfp (p : L^c) (HA : prudent A p) :
  pr1 (dlfp (pr1 HA)) ≺ pr1 (dlfp (Aprudent_Breliable HA)).
Proof.
  suff :  (dlfp (pr1 HA)) ≺  (dlfp (Aprudent_Breliable HA)).
  { move /base_paths; auto. }
  apply prefix_inverse_lfp_order.
  move => [x [Hb Ht]] Hx.
  apply base_paths in Hx.
  simpl in Hx.  
  apply subtypePath => /=.
  { apply isPredicate_interval. }
  apply transL with (pr11 ((pr11 B) ((x,, pr21 p),, Ht))); auto.
  move : (H ((x,, pr21 p),, Ht)) => H0.
  simpl in H0.
  apply prod_dest in H0. simpl in H0.
  induction H0 as [H1 H2]; auto.
Qed.

Lemma Aulfp_Bulfp (p : L^c) (HA : prudent A p) :
  pr1 (ulfp (Aprudent_Breliable HA)) ≺ pr1 (ulfp (pr1 HA)).
Proof.
  suff : (ulfp (Aprudent_Breliable HA)) ≺ (ulfp (pr1 HA)).
  { move /base_paths; auto. }
  apply prefix_inverse_lfp_order.
  move => [x [Hb Ht]] Hx.
  apply base_paths in Hx.
  simpl in Hx.  
  apply subtypePath => /=.
  { apply isPredicate_interval. }
  apply transL with (pr21 ((pr11 A) ((pr11 p,, x),, Hb))); auto.
  move : (H ((pr11 p,, x),, Hb)) => H0.
  simpl in H0.
  apply prod_dest in H0. simpl in H0.
  induction H0 as [H1 H2].
  apply meet_join. rewrite joinC; auto.
Qed.

Lemma Aprudent_Bprudent (p : L^c) :
  prudent A p -> prudent B p.
Proof.
  move => HA.
  exists (Aprudent_Breliable HA).
  eapply transL; first last.
  - apply Adlfp_Bdlfp.
  - apply (pr2 HA) .
Qed.

Lemma pointwise_preserve_stable p (HA : prudent A p) :
  stable_revision' (pr1 HA) ≺k stable_revision' (Aprudent_Breliable HA).
Proof.
  unfold stable_revision', stable_revision, pr1, pr2 => /=.
  apply two_arg_paths.
  - apply Adlfp_Bdlfp.
  - rewrite joinC; apply meet_join.
    apply Aulfp_Bulfp.
Qed.

End pointwise_order_monotonic.





Lemma pataraia_induction (X : dcppo) (f : X --> X) P:
  is_closed f P -> P (pataraia f).
Proof.
  move => HP.
  eapply smallest_included_in_closed; eauto.
  set x :=  (pataraia f).
  apply (pr2 (pataraia_fixpoint (restrict_to_smallest f))).
Qed.  



Section pointwise_preserve.

Variable T : hSet.
Variable L : complat T.
Variable O : L -> L.
Variable A B : AppxOf O.
Hypotheses H : (pr1 A) ⊏ (pr1 B).



Lemma pointwise_preserve_KK :
  kripke_kleene (pr21 A) ≤ kripke_kleene (pr21 B).
Proof.  
  unfold kripke_kleene.
  set P := fun x => x ≤ pataraia (pr11 B).
  apply (pataraia_induction (f := pr11 A) (P := P)).
  unfold P; clear P.
  repeat split.
  - apply is_min_bottom_dcppo.
  - move => x Hx.
    rewrite <- (pataraia_is_fixpoint (pr11 B)).
    eapply trans_dcpo.
    * apply (pr211 A) in Hx.
      apply Hx.
    * apply H.
  - move => D HD.
    apply dcpo_lub_is_least; auto.
Qed.    
 
Lemma pointwise_preserve_WF :
  pr1 (well_founded (pr1 A)) ≤ pr1 (well_founded (pr1 B)).
Proof.
  unfold well_founded.  
  set P := fun x : dcppoLcp (pr1 A) => pr1 x ≤ pr1 (pataraia (WF_iter (A:=pr1 B),, WF_iter_mono (A:=pr1 B))).
  apply (pataraia_induction (f := WF_iter (A:=pr1 A),, WF_iter_mono (A:=pr1 A)) (P := P)).
  unfold P; clear P.
  repeat split.
  - apply is_min_bottom_dcppo.
  - move => x Hx.    
    rewrite <- (pataraia_is_fixpoint (WF_iter (A:=pr1 B),, WF_iter_mono (A:=pr1 B))).
    unfold monotone_function_to_function, pr1.
    set X := pr1 (WF_iter (pataraia (WF_iter (A:=pr1 B),, WF_iter_mono (A:=pr1 B)))).
    unfold WF_iter, X; clear X.
    move : (pointwise_preserve_stable H (pr2 x)).
    set Y := (pataraia (WF_iter (A:=pr1 B),, WF_iter_mono (A:=pr1 B))).
    unfold monotone_function_to_function, pr1, WF_iter => Hy.
    move : (stable_monotonicity (Aprudent_Breliable H (pr2 x)) (pr2 Y) Hx) => H1.
    suff : (stable_revision' (pr12 x) ≺k stable_revision' (pr12 Y)); auto.
    unfold stable_revision', stable_revision, pr1, pr2 in *.
    apply transL with ((pr1 (dlfp (Aprudent_Breliable H (pr2 x))),, pr1 (ulfp (Aprudent_Breliable H (pr2 x))))); auto.
  - move => D HD.
    apply dcpo_lub_is_least; auto.
Qed.

Lemma pointwise_preserve_exact_fixpoint x :
  (pr111 A) (exact_pair x) = (exact_pair x) -> (pr111 B) (exact_pair x) = (exact_pair x).
Proof.
  move => H0.
  move : (pr2 A x) => HA.
  move : (pr2 B x) => HB.
  rewrite  HB. rewrite <- H0, HA; auto.
Qed.

Lemma pointwise_preserve_exact_stable_fixpoint x :
  stable_fixpoint_of A x  -> stable_fixpoint (pr1 B) (exact_pair x).
Proof.
  unfold stable_fixpoint_of.
  move => H0.
  move : (stable_fixpoint_prudent H0) => HAp.
  move : H0.
  unfold stable_fixpoint, exact_pair, stable_revision, pr1, pr2.
  move => [Hr [H1 H2]].
  move : (pointwise_preserve_stable H HAp) => Hst.
  exists (pr1 (Aprudent_Bprudent H HAp)).
  move : (propproperty (reliable (pr111 A) (exact_pair x)) Hr (pr1 HAp)) => [E _].
  rewrite E in H1, H2. clear E.
  unfold stable_revision', stable_revision, pr1, pr2 in Hst.
  simpl in Hst.
  apply prod_dest in Hst. simpl in Hst.
  induction Hst as [Hst1 Hst2].
  rewrite joinC in Hst2; apply meet_join in Hst2. 
  move : (stable_consistent (pr1 (Aprudent_Bprudent H HAp))) => HBc.
  move : (propproperty (reliable (pr111 B) (exact_pair x)) 
    (pr1 (Aprudent_Bprudent H HAp)) (Aprudent_Breliable H HAp) ) => [E _].
  rewrite E. rewrite E in HBc. clear E.
  set x1 := (pr1 (dlfp (pr1 HAp))).
  set x2 := (pr1 (ulfp (pr1 HAp))).
  set y1 := (pr1 (dlfp (Aprudent_Breliable H HAp))).
  set y2 := (pr1 (ulfp (Aprudent_Breliable H HAp))).  
  assert (x1 ≺ y1) as Hxy1 by auto. clear Hst1.
  assert (y2 ≺ x2) as Hyx2 by auto. clear Hst2.  
  assert (y1 ≺ y2) as Hy by auto. clear HBc.
  split.
  - apply antisymL.
    * rewrite H1; auto.
    * apply transL with y2; auto.
      rewrite H2; auto.
  - apply antisymL.
    * apply transL with y1; auto.
      rewrite H1; auto.
    * rewrite H2; auto.
Qed.

End pointwise_preserve.



Definition imageOfInterval T (L : complat T) (O : L -> L) (p : L^c) : {set : L} :=
  fun Oz => ∃ z, Oz == O z ∧ (pr11 p) ≺ z ∧ z ≺ (pr21 p).

Definition ultimate T (L : complat T) (O : L -> L) : L^c -> L^c.
Proof.
  move => p.
  split with ( (inf (imageOfInterval O p)),, (sup (imageOfInterval O p))).
  unfold consistent, pr1, pr2.
  induction p as [[x y] Hc].
  apply transL with (O x); [apply is_lowb|apply is_upb].
  all:unfold In => P; apply; clear P;
      exists x; repeat split; auto;
      apply reflL.
Defined.

Lemma partialApproximating_isaprop T (L : complat T) (A : L^c --> L^c) :
  isaprop (partialApproximating A).
Proof.
  apply impred_isaprop => x.
  simpl.
  apply (propproperty (pr11 (A (exact_pair x)) = pr21 (A (exact_pair x)))%logic).
Qed.



Section ultimate.

Variable T : hSet.
Variable L : complat T.
Variable O : L -> L.
Variable p : L^c.
Let x := pr11 p.
Let y := pr21 p.
Let Hc := pr2 p.

Lemma ultimate_is_monotone :
  is_monotone (L^c) (L^c) (ultimate O).
Proof.
  move => [[x1 x2] Hx] [[y1 y2] Hy] H.
  simpl in H. apply prod_dest in H. induction H as [H1 H2]. simpl in H1, H2.
  rewrite joinC in H2; apply meet_join in H2.
  unfold ultimate => /=.
  apply two_arg_paths.
  - apply is_inf => b.
    unfold In => Hb.
    unfold imageOfInterval in Hb.
    unfold ishinh, ishinh_UU, pr1, pr2 in Hb.
    apply Hb => [[z [b_Oz [yz zy]]]].
    apply is_lowb.
    unfold In, imageOfInterval => P; apply; clear P.
    exists z; repeat split; auto; unfold pr1, pr2.
    * apply transL with y1; auto.
    * apply transL with y2; auto.
  - rewrite joinC. apply meet_join.
    apply is_sup => b.
    unfold In => Hb.
    unfold imageOfInterval in Hb.
    unfold ishinh, ishinh_UU, pr1, pr2 in Hb.
    apply Hb => [[z [b_Oz [yz zy]]]].
    apply is_upb.
    unfold In, imageOfInterval => P; apply; clear P.
    exists z; repeat split; auto; unfold pr1, pr2.
    * apply transL with y1; auto.
    * apply transL with y2; auto.
Qed.

Lemma ultimate_exact a :
  ultimate O (exact_pair a) = exact_pair (O a).
Proof.
  apply antisymm_dcpo; simpl; apply two_arg_paths.
  - apply is_lowb.
    unfold In.
    move => P; apply; exists a; repeat split; auto; apply reflL.
  - rewrite joinC. apply meet_join.
    apply is_upb.
    unfold In.
    move => P; apply; exists a; repeat split; auto; apply reflL.
  - apply is_inf => b Hb.
    unfold In, ishinh, ishinh_UU in Hb.
    unfold imageOfInterval in Hb.
    unfold ishinh, ishinh_UU in Hb.
    apply Hb => [[z [E [az za]]]].
    unfold pr1, pr2 in *.
    rewrite (antisymL az za) E.
    apply reflL.
  - rewrite joinC. apply meet_join. 
    apply is_sup => b Hb.
    unfold In, ishinh, ishinh_UU in Hb.
    unfold imageOfInterval, ishinh, ishinh_UU in Hb.
    apply Hb => [[z [E [az za]]]].
    unfold pr1, pr2 in *.
    rewrite (antisymL az za) E.
    apply reflL.
Qed.    

  
Lemma partialApproximateing_ultimate :
  partialApproximating (ultimate O,, ultimate_is_monotone).
Proof.
  move => a.
  Set Printing Coercions.
  unfold monotone_function_to_function, pr1, pr2.
  rewrite ultimate_exact.
  unfold exact_pair.
  apply paths_refl.
Qed.
  

Definition ultimateAppx := ((ultimate O,, ultimate_is_monotone),, partialApproximateing_ultimate).
Definition ultimateAppxOf : AppxOf O := (ultimateAppx,, ultimate_exact).





Lemma ultimate_is_greatest :
  ∏ U : AppxOf O, (pr1 U) ⊏ (pr1 ultimateAppxOf).
Proof.
  unfold ultimateAppxOf.
  move => [[[U Um] F] HU] [[a b] ab].
  unfold ultimateAppx, pr1.
  unfold partialApproximate, pr1 in HU.
  clear F.
  assert (∏ c, a ≺ c -> c ≺ b -> U ((a,, b),, ab) ≤ exact_pair (O c)) as H1. {
    move => c ac cb.
    rewrite <- (HU c).
    apply Um.
    simpl.
    apply two_arg_paths; auto.
    rewrite joinC; apply meet_join; auto.
  }
  assert ((pr11 (U ((a,, b),, ab))) ≺ (inf (imageOfInterval O ((a,, b),, ab)))). {
    apply is_inf => d.
    unfold In, imageOfInterval, ishinh, ishinh_UU.
    apply => [[z [Hz [az zb]]]].
    unfold pr1, pr2 in *.
    rewrite Hz.
    move : (H1 z az zb) => H0.
    simpl in H0.
    apply prod_dest in H0.
    simpl in H0.
    induction H0 as [H01 _]; auto.
  }
  assert ((sup (imageOfInterval O ((a,, b),, ab))) ≺ (pr21 (U ((a,, b),, ab)))). {
    apply is_sup => d.
    unfold In, imageOfInterval, ishinh, ishinh_UU.
    apply => [[z [Hz [az zb]]]].
    unfold pr1, pr2 in *.
    rewrite Hz.
    apply meet_join; rewrite joinC.
    move : (H1 z az zb) => H0.
    simpl in H0.
    apply prod_dest in H0.
    simpl in H0.
    induction H0 as [_ H02]; auto.
  }
  simpl.
  rewrite X.
  apply meet_join in X0.  
  rewrite joinC in X0.
  rewrite X0; auto.
Qed.




Definition ultimate_kripke_kleene := kripke_kleene (pr2 ultimateAppx).
 (* partialApproximateing_ultimate. *)
Definition ultimate_well_founded := pr1 (well_founded ultimateAppx).
Definition ultimate_partial_stable_fixpoint :=
  stable_fixpoint ultimateAppx.
Definition ultimate_stable_fixpoint x :=
  stable_fixpoint ultimateAppx (exact_pair x).


Lemma ultimate_kripke_kleene_is_greatest :
  ∏ A : AppxOf O, kripke_kleene  (pr21 A) ≤ ultimate_kripke_kleene.
Proof.
  move => A.
  unfold ultimate_kripke_kleene.
  move : (pointwise_preserve_KK (ultimate_is_greatest A)).
  move : (partialApproximating_isaprop 
    (A := (ultimate O,, ultimate_is_monotone))
    (pr2 ultimateAppx)
    (pr21 ultimateAppxOf)
  ) => [E _].
  rewrite E; auto.
Qed.

Lemma ultimate_well_founded_is_greatest :
  ∏ A : AppxOf O, pr1 (well_founded (pr1 A)) ≤ ultimate_well_founded.
Proof.
  move => A.
  unfold ultimate_well_founded.
  apply (pointwise_preserve_WF (ultimate_is_greatest A)).
Qed.

Print stable_fixpoint.

Lemma stable_fixpoint_ultimate_stable_fixpoint :
  ∏ (A : AppxOf O) (x : L), stable_fixpoint_of A x -> ultimate_stable_fixpoint x.
Proof.  
  move => A a H.
  apply (pointwise_preserve_exact_stable_fixpoint (ultimate_is_greatest A) H).
Qed.

End ultimate.

Lemma monotone_ultimate T (L : complat T) (O : L -> L) (p : L^c) (H : mono O) :
  pr11 (ultimate O  p) = O (pr11 p) × pr21 (ultimate O p) = O (pr21 p).
Proof.
Check (mono O).
  induction p as [[x y] Hc].
  split; unfold ultimate => /=; apply antisymL; unfold imageOfInterval.
  - apply is_lowb.
    unfold In => P; apply; clear P.
    exists x; repeat split; auto; apply reflL.
  - apply is_inf.
    move => b Hb.
    unfold In, ishinh, ishinh_UU in Hb.
    apply Hb => [[z[Hz [xz zy]]]].
    unfold pr1, pr2 in *.
    rewrite Hz; apply H; auto.
  - apply is_sup.
    move => b Hb.
    unfold In, ishinh, ishinh_UU in Hb.
    apply Hb => [[z[Hz [xz zy]]]].
    unfold pr1, pr2 in *.
    rewrite Hz; apply H; auto.
  - apply is_upb.
    unfold In => P; apply; clear P.
    exists y; repeat split; auto; apply reflL.
Qed.

Lemma antimonotone_ultimate T (L : complat T) (O : L -> L) (p : L^c) (H : antimono O) :
  pr11 (ultimate O  p) = O (pr21 p) × pr21 (ultimate O p) = O (pr11 p).
Proof.
  induction p as [[x y] Hc].
  split; unfold ultimate => /=; apply antisymL; unfold imageOfInterval.
  - apply is_lowb.
    unfold In => P; apply; clear P.
    exists y; repeat split; auto; apply reflL.
  - apply is_inf.
    move => b Hb.
    unfold In, ishinh, ishinh_UU in Hb.
    apply Hb => [[z[Hz [xz zy]]]].
    unfold pr1, pr2 in *.
    rewrite Hz; apply H; auto.
  - apply is_sup.
    move => b Hb.
    unfold In, ishinh, ishinh_UU in Hb.
    apply Hb => [[z[Hz [xz zy]]]].
    unfold pr1, pr2 in *.
    rewrite Hz; apply H; auto.
  - apply is_upb.
    unfold In => P; apply; clear P.
    exists x; repeat split; auto; apply reflL.
Qed.
  






  




  


