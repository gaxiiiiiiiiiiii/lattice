Require Export Approximation.
From UniMath Require Export OrderTheory.DCPOs.AlternativeDefinitions.Dcpo.
From UniMath Require Export OrderTheory.DCPOs.AlternativeDefinitions.FixedPointTheorems.

Open Scope DCPO.
Open Scope poset.


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
  { exact (imeet a b). }
  use tpair.
  { exact (ijoin a b). }
  
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

Lemma notempty_has_elm {T : hSet} (X : {set : T}) (H : ¬ (X == ∅)) :
  ∃ x, x ∈ X.
Proof.
  apply notallnot_ex => F.
  apply H.
  move : (invweq (hsubtype_univalence X ∅)) => [f Hf].
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
  move : (lem (X == ∅)) => HX.
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
  move : (lem (X == ∅)) => HX.
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
    set H0 := (lem (X == ∅)).
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
    set H0 := (lem (X == ∅)).
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
    set H0 := (lem (X == ∅)).
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
    set H0 := (lem (X == ∅)).
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

Definition Lc_hSet {T} (L : complat T) : hSet := make_hSet (consistents L) (isaset_consistents L).


Definition cle {T} {L : complat T} : hrel (Lc_hSet L) :=
  fun x y => (@kle _ (L^2) (pr1 x) (pr1 y)).
  

Definition dcpoLc {T} (L : complat T) : dcpowithbottom.
Proof.  
  unfold dcpowithbottom.
  use tpair. use tpair. use tpair.
  - exact (Lc_hSet L).
  use tpair.
  - exact cle.
  use tpair.
  use tpair.
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

        induction H as [_ H].
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

Notation "L ^c" := (dcpoLc L) (at level 10).

Definition trans {T} {L : complat T} (f : L^2 -> L^2) (Hf : approximating f) : L^c -> L^c.
Proof.
  move => x.
  induction x as [x Hx].
  move : (approximating_consistent Hf).
  move /(_ x Hx) => H.
  split with (f x); auto.
Qed.

(* Definition partialApproximation {T} {L : complat T} (f : L^2 -> L^2) :=
  klemono f × (forall x, fstOf f (x,,x) = sndOf f (x,,x)). *)

Definition  exact_pair {T} {L : complat T} (x : L) : L^c := (x,,x),, (meetI x).


Definition partialApproximating {T} {L : complat T} (f : L^c --> L^c) :=
  forall x : L, pr11 (pr1 f (exact_pair x)) = pr21 (pr1 f (exact_pair x)).

Definition Appx {T} (L : complat T) : UU :=
  ∑ f : L^c --> L^c, partialApproximating f.
(* Definition Appx_fun {T} {L : complat T} : Appx L -> L^c --> L^c := pr1. *)
(* Coercion Appx_fun : Appx >-> pr1hSet.   *)

Definition kripke_kleene {T} {L : complat T} (f : L^c --> L^c) (Hf : partialApproximating f) 
  : L^c := (pr1 leastfixedpoint) f.

Definition partialApproximate {T} {L : complat T} (A : Appx L) (O : L -> L) :=
  forall x, pr11 A (exact_pair x) = (exact_pair (O x)).

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
  O x = x -> kripke_kleene (pr11 A) (pr21 A) ≤ exact_pair x.
Proof.
  move => A x Hx.
  apply  (Appxof_fixpoint O A x) in Hx.
  induction A as [[f Hfx] b]; unfold pr1, pr2 in *.
  unfold kripke_kleene.
  apply leastfixedpoint_isleast.
  rewrite Hx. apply meetI.
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
  - induction A as[[f [R HR]] Hf].
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
  - induction A as[[f [R HR]] Hf].
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


Section restriction.

Hypotheses lem : LEM.

Definition down_restriction (lem : LEM) {T} {L : complat T} (p : L^c) :=
  interval_complat lem ⊥ (pr21 p) (bot_min T L (pr21 p)).

Definition up_restriction (lem : LEM) {T} {L : complat T} (p : L^c) :=
  interval_complat lem (pr11 p) ⊤ (top_max T L (pr11 p)).

Definition A1 {T} {L : complat T} (p : L^c) (A : Appx L) (Hp : reliable (pr11 A) p) :
  down_restriction lem p -> down_restriction lem p.
Proof.
  move => [x [Hb Ht]].
  split with (pr11 ((pr11 A) ((x,,(pr21 p)),, Ht))).
  apply (Appx_leftrestriction A p Hp x Hb Ht).
Defined.

Definition A2 {T} {L : complat T} (p : L^c) (A : Appx L) (Hp : reliable (pr11 A) p) :
  up_restriction lem p -> up_restriction lem p.
Proof.
  move => [x [Hb Ht]].
  split with (pr21 ((pr11 A) ((pr11 p,,x),, Hb))).
  apply (Appx_rightrestriction A p Hp x Hb Ht).
Defined.   

Lemma monoA1  {T} {L : complat T} (p : L^c) (A : Appx L) (Hp : reliable (pr11 A) p) :
  mono (A1 p A Hp).
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
  induction Hf as [Hf Hf'].
  move : (Hf _ _ X).
  move /base_paths; auto.
Qed.


Lemma monoA2 {T} {L : complat T} (p : L^c) (A : Appx L) (Hp : reliable (pr11 A) p) :
  mono (A2 p A Hp).
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
  induction Hf as [Hf Hf'].
  move : (Hf _ _ X) => H0.
  simpl in H0.
  apply prod_dest in H0.
  induction H0 as [H1 H2].
  unfold pr1, pr2 in *.
  apply meet_join; rewrite joinC; auto.
Qed.


Definition dlfp {T} {L : complat T} (p : L^c) (A : Appx L) (Hp : reliable (pr11 A) p) :=
  lfp (A1 p A Hp) (monoA1 p A Hp).

Definition ulfp {T} {L : complat T} (p : L^c) (A : Appx L) (Hp : reliable (pr11 A) p) :=
  lfp (A2 p A Hp) (monoA2 p A Hp).


Lemma dlfp_is_fixpoint {T} {L : complat T} (p : L^c) (A : Appx L) (Hp : reliable (pr11 A) p) :
  (A1 p A Hp) (dlfp p A Hp) = (dlfp p A Hp).
Proof.
  move : (tarski_lfp _ _ (A1 p A Hp) (monoA1 p A Hp)) => [Hfp Hlfp]; auto.
Qed.

Lemma ulfp_is_fixpoint {T} {L : complat T} (p : L^c) (A : Appx L) (Hp : reliable (pr11 A) p) :
  (A2 p A Hp) (ulfp p A Hp) = (ulfp p A Hp).
Proof.
  move : (tarski_lfp _ _ (A2 p A Hp) (monoA2 p A Hp)) => [Hfp Hlfp]; auto.
Qed.




Definition stable_revision {T} {L : complat T}  (A : Appx L) :
  ∏ P : (∑ p : L^c, reliable (pr11 A) p), down_restriction lem (pr1 P) × up_restriction lem (pr1 P) :=
  fun P => dlfp (pr1 P) A (pr2 P),, ulfp (pr1 P) A (pr2 P).

Definition stable_fixpoint {T} {L : complat T} (A : Appx L) (p : L^c) :=
  ∑ Hp : reliable (pr11 A) p, 
  pr11 p = pr11 (stable_revision A (p,, Hp)) ×
  pr21 p = pr12 (stable_revision A (p,, Hp)).

Lemma stable_fixpoint_fixpoint {T} {L : complat T} (A : Appx L) (p : L^c) :
  stable_fixpoint A p -> (pr11 A) p = p.
Proof.
  move => [Hr [H1 H2]].
  move : (dlfp_is_fixpoint p A Hr) => Hdfp.
  move : (ulfp_is_fixpoint p A Hr) => Hufp.
  unfold stable_revision in H1, H2.
  induction p as [[a b] Hab].
  unfold pr1,pr2 in *.
  assert (dlfp ((a,,b),,Hab) A Hr = (a,, (bot_min _ _ a),, Hab)). {
    apply subtypePath => //=.
    apply isPredicate_interval.
    symmetry; auto.
  }
  assert (ulfp ((a,,b),,Hab) A Hr = (b,, Hab,, (top_max _ _ b))). {
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
  (pr111 A) ((x,,x),, meetI x) = ((x,,x),, meetI x).


Definition prudent {T} {L : complat T} (A : Appx L) (p : L^c) :=
  ∑ Hp : reliable (pr11 A) p, (pr11 p) ≺ (pr1 (dlfp p A Hp)).

Lemma stabla_fixpoint_prudent {T} {L : complat T} (A : Appx L) (p : L^c) :
  stable_fixpoint A p -> prudent A p.
Proof.
  move => [Hp [H1 H2]].
  exists Hp.
  induction p as [[a b] Hab].
  unfold stable_revision, pr1,pr2 in *.
  Set Printing Coercions.
  apply (transportb (fun x => x ≺ pr1 (dlfp ((a,, b),, Hab) A Hp)) H1 (meetI  _)).
Qed.  

Lemma a_au  {T} {L : complat T} (A : Appx L) (p : L^c) (Hp : reliable (pr11 A) p) :
  (pr11 p) ≺ (pr1 (ulfp p A Hp)).
Proof.
  set a :=  (ulfp p A Hp).
  induction a as [a [H1 H2]]; auto.
Qed.

Lemma bd_b {T} {L : complat T} (A : Appx L) (p : L^c) (Hp : reliable (pr11 A) p) :
  (pr1 (dlfp p A Hp)) ≺ (pr21 p).
Proof.
  set b := (dlfp p A Hp).
  induction b as [b [H1 H2]]; auto.
Qed.

Lemma au_b {T} {L : complat T} (A : Appx L) (p : L^c) (Hp : reliable (pr11 A) p) :
   (pr1 (ulfp p A Hp)) ≺ (pr21 p).
Proof.  
  assert (A2 p A Hp (pr21 p,, pr2 p,, top_max _ _ (pr21 p) ) ≺ (pr21 p,, pr2 p,, top_max _ _ (pr21 p) )). {
    apply subtypePath.
    apply isPredicate_interval.
    induction p as [[a b] Hab].
    simpl.
    rename Hp into Hr.
    (* induction H as [Hr _]. *)
    unfold reliable in Hr.
    simpl in Hr.
    apply prod_dest in Hr.
    induction Hr.
    apply meet_join. rewrite joinC; auto.
  }
  move : (lfp_prefixpoint _ _ (A2 p A Hp) (monoA2 p A Hp) (pr21 p,, pr2 p,, top_max _ _ (pr21 p)) X).
  move /base_paths; auto.
Qed.

Section prudent.

Variable T : hSet.
Variable L : complat T.
Variable A : Appx L.
Variable p : L^c.
Variable H : prudent A p.

Notation a := (pr11 p).
Notation b := (pr21 p).

Notation "a↑" := (pr1 (ulfp p A (pr1 H))).
Notation "b↓" := (pr1 (dlfp p A (pr1 H))).

Notation au_b := (au_b A p (pr1 H)).
Notation a_au := (a_au A p (pr1 H)).
Notation bd_b := (bd_b A p (pr1 H)).


(*a↑,b ≤ a↑,a↑*)
Local Lemma aub_auau :
  (((a↑,, b),, au_b) : L^c) ≤ ((a↑,, a↑),, meetI a↑).
Proof.
  simpl.
  move : (meetI (pr1 (ulfp p A (pr1 H)))) => Hk.
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



  
Lemma ac_prefix :
  A1 p A (pr1 H)  (a↑,, bot_min _ _ a↑,, au_b) ≺  (a↑,, bot_min _ _ a↑,, au_b).
Proof.
  set Hm := (pr121 A).
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

  move : (tarski_lfp _ _ (A2 p A (pr1 H)) (monoA2 p A (pr1 H))) => [Hfp _].
  apply base_paths in Hfp.    
  simpl in Hfp.
  change (pr1 (lfp (A2 p A (pr1 H)) (monoA2 p A (pr1 H)))) with a↑ in Hfp.
  move : (propproperty (a ≺ a↑)) => Hc.
  move : (Hc a_au ( pr12 (lfp (A2 p A (pr1 H)) (monoA2 p A (pr1 H))))) => [c hc].
  rewrite c Hfp.
  apply meetI.
Qed.  

Lemma stable_consistent :
    @consistent T L (b↓,, a↑).
Proof.
  move : (lfp_prefixpoint _ _ (A1 p A (pr1 H)) (monoA1 p A (pr1 H)) _ ac_prefix).
  move /base_paths => H0; auto.
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

Lemma stable_relaible : 
  reliable (pr11 A) ((b↓,, a↑),, stable_consistent).
Proof.
  simpl.
  apply two_arg_paths.
  - move : (tarski_lfp _ _ (A1 p A (pr1 H)) (monoA1 p A (pr1 H))) =>  [Hfp _].
    apply base_paths in Hfp.    
    simpl in Hfp.
    change (pr1 (lfp (A1 p A (pr1 H)) (monoA1 p A (pr1 H)))) with b↓ in Hfp.
    move : (propproperty (b↓ ≺ b)) => Hc.
    move : (Hc (pr22 (lfp (A1 p A (pr1 H)) (monoA1 p A (pr1 H)))) bd_b) => [E _].
    rewrite E in Hfp.
    apply transL with (pr11 ((pr11 A) ((b↓,, b),, bd_b))).
    * rewrite Hfp. apply meetI.
    * move : ((pr121 A) _ _ bdb_bdau) => /= Hb.
      apply prod_dest in Hb.
      induction Hb; auto.
  - move : (tarski_lfp _ _ (A2 p A (pr1 H)) (monoA2 p A (pr1 H))) =>  [Hfp _].
    apply base_paths in Hfp.    
    simpl in Hfp.
    change (pr1 (lfp (A2 p A (pr1 H)) (monoA2 p A (pr1 H)))) with a↑ in Hfp.
    move : (propproperty (a ≺ a↑)) => Hc.
    move : ((Hc (pr12 (lfp (A2 p A (pr1 H)) (monoA2 p A (pr1 H))))) a_au) => [E _].
    rewrite E in Hfp.
    rewrite joinC; apply meet_join.
    apply transL with (pr21 ((pr11 A) ((a,, a↑),, a_au))); first last.
    * rewrite Hfp. apply meetI.
    * move : ((pr121 A) _ _ aau_bdau) => /= Hb.
      apply prod_dest in Hb.
      apply meet_join. rewrite joinC.
      induction Hb; auto.
Qed.


(* (x,, b) ∈ L^c *)
Local Definition xb (x : L) (Hx : x ≺ a↑) : L^c.
Proof.
  split with (x,,b); simpl.
  apply transL with a↑; auto.
  apply au_b.
Defined.

(* (x,, a↑) ∈ L^c*)
Local Definition xau (x : L) (Hx : x ≺ a↑) : L^c.
Proof.
  split with (x,,a↑); auto.
Defined.

Local Lemma xb_xau x Hx :
  xb x Hx ≤ xau x Hx.
Proof.
  simpl.
  rewrite meetI.
  move : au_b => Hb.
  apply meet_join in Hb.
  rewrite joinC Hb; auto.
Qed.

Local Lemma Axb_Axau x Hx :
  (pr11 A) (xb x Hx) ≤ (pr11 A) (xau x Hx).
Proof.
  apply (pr121 A).
  apply xb_xau.
Qed.  


Local Lemma Axau_au x Hx :
  pr11 ((pr11 A) (xau x Hx)) ≺ a↑.
Proof.
  unfold xau.
  move : stable_relaible => Hr.
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
    apply stable_consistent.
    apply joinI.
  }
  move : (pr121 A _ _ X) => H0.
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
  apply (pr121 A).
  simpl. apply two_arg_paths; auto.
  apply joinI.
Qed.  

  


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



Lemma stable_prudent :
  prudent A ((b↓,, a↑),, stable_consistent).
Proof.
  unfold prudent.
  exists stable_relaible.
  simpl.
  move : (tarski_lfp _ _ (A1 p A (pr1 H)) (monoA1 p A (pr1 H))) => [Hfp1 Hlfp1]; auto.
  apply base_paths in Hfp1.
  simpl in Hfp1.
  change (pr1 (lfp (A1 p A (pr1 H)) (monoA1 p A (pr1 H)))) with b↓ in *.
  move : (tarski_lfp _ _ 
    (A1 ((pr1 (lfp (A1 p A (pr1 H)) (monoA1 p A (pr1 H))),, a↑),, stable_consistent) A stable_relaible)
    (monoA1 ((pr1 (lfp (A1 p A (pr1 H)) (monoA1 p A (pr1 H))),, a↑),, stable_consistent) A stable_relaible)
  ) => [Hfp2 Hlfp2].

  apply base_paths in Hfp2.
  simpl in Hfp2, H.
  change (pr1 (lfp (A1 p A (pr1 H)) (monoA1 p A (pr1 H)))) with b↓ in *.
  change (lfp (A1 ((b↓,, a↑),, stable_consistent) A stable_relaible)
            (monoA1 ((b↓,, a↑),, stable_consistent) A stable_relaible))
  with (dlfp ((b↓,, a↑),, stable_consistent) A stable_relaible) in *.
  
  move : (Axb_Axau b↓ stable_consistent) => Hbd.
  apply base_paths in Hbd. 
  unfold xb, xau in Hbd.
  simpl in Hbd.
  move : (propproperty (b↓ ≺ b) 
    (pr22 (lfp (A1 p A (pr1 H)) (monoA1 p A (pr1 H))))
    (transL (X:=L) (l:=L) (a:=b↓) (b:=a↑) (c:=b) stable_consistent au_b)
  ) => [E _].
  rewrite <- E in Hbd. clear E.
  rewrite Hfp1 in Hbd.
  move : (propproperty (b↓ ≺ b)
    (pr22 (lfp (A1 p A (pr1 H)) (monoA1 p A (pr1 H))))  bd_b ) => [E _].
  rewrite E in Hfp1. clear E.
  
  move : (Axau_au _ stable_consistent) => Hau.

  move : (Axb_Axau) => HA.
  assert (forall x Hx, 
    pr11 ((pr11 A) (xau x Hx))  ≺ x -> 
    pr11 ((pr11 A) (xb x Hx)) ≺ x). {
    move => x Hx Hxa.
    move : (Axb_Axau x Hx) => Hxb.
    apply base_paths in Hxb.
    simpl in Hxb.
    apply transL with (pr11 ((pr11 A) (xau x Hx))); auto.    
  }
  unfold xb, xau in X.
  unfold dlfp in Hfp1.
  assert ( forall x,
    A1 ((b↓,, a↑),, stable_consistent) A stable_relaible x ≺ x  ->
    pr1 (lfp (A1 p A (pr1 H)) (monoA1 p A (pr1 H))) ≺ pr1 x
  ). {
    move => [x [Hx' Hx]] H0.
    unfold pr1, pr2 in *.
    (* unfold A1 in H0. *)
    apply base_paths in H0.
    simpl in H0.
    apply X in H0.
    suff : 
      (lfp (A1 p A (pr1 H)) (monoA1 p A (pr1 H)))
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

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section stable_monotonicity.

Variable T : hSet.
Variable L : complat T.
Variable A : Appx L.
Variable p q : L^c.
Variable Hp : reliable (pr11 A) p.
Variable Hq : prudent A q.
Variable Hpq : p ≤ q.

Local Notation a := (pr11 p).
Local Notation b := (pr21 p).
Local Notation c := (pr11 q).
Local Notation d := (pr21 q).

Local Notation Hr := (pr1 Hq).
Local Notation Hpr := (pr2 Hq).

Local Notation "a↑" := (pr1 (ulfp p A Hp)).
Local Notation "b↓" := (pr1 (dlfp p A Hp)).
Local Notation "c↑" := (pr1 (ulfp q A (pr1 Hq))).
Local Notation "d↓" := (pr1 (dlfp q A (pr1 Hq))).


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

Local Notation c_cu := (a_au A q Hr).
Local Notation dd_d := (bd_b A q Hr).
Local Notation cu_d := (au_b A q Hr).

Local Notation a_au := (a_au A p Hp).
Local Notation bd_b := (bd_b A p Hp).
Local Notation au_b := (au_b A p Hp).




Definition dd' : down_restriction lem p.
Proof.
  split with (d↓); split.
  - apply bot_min.
  - apply transL with d.
    apply dd_d.
    apply d_b.
Defined.


Lemma dd_prefix :
  A1 p A Hp dd' ≺  dd'.
Proof.
  apply subtypePath => /=.
  apply isPredicate_interval.
  move : (tarski_lfp _ _ (A1 q A Hr) (monoA1 q A Hr)) => [Hfp Hlfp]; auto.
  apply base_paths in Hfp.
  change (pr1 (lfp (A1 q A Hr) (monoA1 q A Hr))) with d↓ in Hfp.
  apply transL with (pr1 (A1 q A Hr (lfp (A1 q A Hr) (monoA1 q A Hr)))); first last.
  { rewrite Hfp. apply meetI. }
  Print A1.
  set x := (lfp (A1 q A Hr) (monoA1 q A Hr)).
  unfold A1; simpl; unfold x.

  suff : 
  (pr11 A) ((d↓,, b),, transL dd_d d_b) 
  ≤
  ((pr11 A)
          ((pr1 (lfp (A1 q A Hr) (monoA1 q A Hr)),, d),,
          pr22 (lfp (A1 q A Hr) (monoA1 q A Hr)))).
  { move /base_paths; auto. }
  apply (pr121 A).
  simpl.
  move : d_b => d_b.
  apply meet_join in d_b.
  rewrite joinC d_b.
  rewrite meetI; auto.
Qed.    

Lemma bd_dd :
  b↓ ≺ d↓.
Proof.
  move : (lfp_prefixpoint _ _ _ (monoA1 p A Hp) _ (dd_prefix)).
  move /base_paths; auto.
Qed.

Lemma a_dd :
  a ≺ d↓.
Proof.
  move : (stable_pricise T L A q (Hr,, Hpr)) => H0.
  move : (istrans_posetRelation (L^c) _ _ _ Hpq H0).
  move /base_paths; auto.
Qed.


Local Definition u := (meet a↑ d↓).

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
  A1 q A Hr u' ≺ u'.
Proof.
  apply subtypePath => /=.
  apply isPredicate_interval.
  apply meet_inf.
  - move : (tarski_lfp _ _ (A2 p A Hp) (monoA2 p A Hp)) => [Hfp _]; auto.
    apply base_paths in Hfp.
    change (pr1 (lfp (A2 p A Hp) (monoA2 p A Hp))) with a↑ in Hfp.
    rewrite <- Hfp; clear Hfp.
    set x := (lfp (A2 p A Hp) (monoA2 p A Hp)).
    unfold A2, pr1, pr2, x.
    change (pr1 (lfp (A2 p A Hp) (monoA2 p A Hp))) with a↑.
    eapply transL with (pr21 ((pr11 A) ((u,,u),, meetI u))); first last.
    * suff : 
      ((pr11 A) ((a,, a↑),, pr12 (lfp (A2 p A Hp) (monoA2 p A Hp))))
      ≤
      ((pr11 A) ((u,, u),, meetI u)).
      { 
       move => /= H0.
       apply prod_dest in H0.
       induction H0 as [_ H0].
       simpl in H0.
       apply meet_join; rewrite joinC; auto.
      }
      apply (pr121 A); simpl.
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
      apply (pr121 A); simpl.
      apply two_arg_paths; auto.
      + apply meetI.
      + rewrite joinC; apply meet_join.
        apply transL with d↓.
        * apply u_dd.
        * apply dd_d.
  - move : (tarski_lfp _ _ (A1 q A Hr) (monoA1 q A Hr)) => [Hfp _]; auto.
    apply base_paths in Hfp.
    change (pr1 (lfp (A1 q A Hr) (monoA1 q A Hr))) with d↓ in Hfp.
    apply transL with (pr1 (A1 q A Hr (lfp (A1 q A Hr) (monoA1 q A Hr)))); first last.
    { rewrite Hfp. apply meetI. }
    clear Hfp.
    set x := (lfp (A1 q A Hr) (monoA1 q A Hr)).
    unfold A1, pr1, pr2, x.
    suff : 
      ((pr11 A) ((u,, d),, transL u_dd dd_d))
      ≤ 
      ((pr11 A) ((d↓,, d),, pr22 (lfp (A1 q A Hr) (monoA1 q A Hr)))).
    { move /base_paths; auto. }
    apply (pr121 A); simpl.
    rewrite u_dd joinI; auto.
Qed.

Lemma dd_au :
  d↓ ≺ a↑.
Proof.
  apply transL with u; first last.
  - apply u_au.
  - move : (lfp_prefixpoint _ _ _ (monoA1 q A Hr) _ u_prefixpoint).
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
  A2 q A Hr au' ≺ au'.
Proof.
  apply subtypePath.
  apply isPredicate_interval.
  simpl.
  move : (tarski_lfp _ _ (A2 p A Hp) (monoA2 p A Hp)) => [Hfp _].
  apply base_paths in Hfp.
  change (pr1 (lfp (A2 p A Hp) (monoA2 p A Hp))) with a↑ in Hfp.
  apply transL with (pr1 (A2 p A Hp (lfp (A2 p A Hp) (monoA2 p A Hp)))); first last.
  { rewrite Hfp. apply meetI. }
  set x := (lfp (A2 p A Hp) (monoA2 p A Hp)).
  unfold A2, pr1, pr2, x.

  suff : 
    (pr11 A) ((a,, a↑),, pr12 (lfp (A2 p A Hp) (monoA2 p A Hp)))
    ≤
    ((pr11 A) ((c,, a↑),, transL Hpr dd_au)).
  {
    move => /= H0.
    apply prod_dest in H0.
    induction H0 as [_ H0].
    simpl in H0.
    apply meet_join; rewrite joinC; auto.
  }
  apply (pr121 A); simpl.
  rewrite a_c joinI; auto.
Qed.

Lemma cu_au :
  c↑ ≺ a↑.
Proof.
  move : (lfp_prefixpoint _ _ _ (monoA2 q A Hr) _ au_prefixpoint).
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

  
  
  

  

  
 