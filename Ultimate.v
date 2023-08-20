Require Export Approximation.
From UniMath Require Export OrderTheory.DCPOs.AlternativeDefinitions.Dcpo.
From UniMath Require Export OrderTheory.DCPOs.AlternativeDefinitions.FixedPointTheorems.

Open Scope DCPO.
Open Scope poset.


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

Definition Lc {T} (L : complat T) : hSet := make_hSet (consistents L) (isaset_consistents L).
(* Notation "L ^c" := (Lc L) (at level 10). *)

Definition cle {T} {L : complat T} : hrel (Lc L) :=
  fun x y => (@kle _ (L^2) (pr1 x) (pr1 y)).
  

Definition dcpoLc {T} (L : complat T) : dcpowithbottom.
Proof.  
  unfold dcpowithbottom.
  repeat use tpair.
  - exact (Lc L).
  - exact cle.
  - move => [x Hx] [y Hy] [z Hz].
    unfold cle, pr1 => xy yz.
    eapply transL; eauto.
  - simpl.
    move => [x Hx].
    unfold cle, pr1.
    apply reflL.
  - simpl.
    move => [x Hx] [y Hy].
    unfold cle, pr1 => xy yx.
    move : (antisymL xy yx) => xx.
    induction xx.
    move : (propproperty (consistent x)).
    unfold isaprop, isofhlevel.
    move /(_ Hx Hy) => [c _].
    induction c; auto.
  all : simpl.
  - unfold isdirectedcomplete => /=.
    move => I f H.
    unfold isdirected in H.
    use tpair.
    - use tpair.
      * set X : {set : L^2 }:=  fun x => ∃ i, x = f i.
        set X1 : {set : L} := fun x => ∃ y, X (x,,y).
        set X2 : {set : L} := fun y => ∃ x, X (x,,y).
        exact (sup X1,, inf X2).
      *  

        
        
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
        
        induction (f i) as [fi Hfi].
        simpl in Hi.
        unfold consistent in Hfi.
        rewrite <- Hi in Hfi.
        unfold pr1, pr2 in Hfi.

        induction (f j) as [fj Hfj].
        simpl in Hj.
        unfold consistent in Hfj.
        rewrite <- Hj in Hfj.
        unfold pr1, pr2 in Hfj.       
        clear Hi Hj.

        apply transL with x; auto.
        apply transL with y; auto.

        admit.
      * simpl.
        unfold islub => /=.
        split.
        + unfold isupperbound => i.
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
  - unfold consistents.
    split with (@bot _ L ,, @top _ L  : L × L).
    apply bot_min.
  - simpl.
    move =>  /= [[x1 x2] Hx] /=.
    apply two_arg_paths.
    * apply bot_min.
    * rewrite joinC. apply meet_join. apply top_max.
Admitted.