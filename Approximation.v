(* based on 'mations, stable operators and the well-jounded jixpoint' *)

Require Export ProdBilattice.



Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

 
Notation "L ^2" := (prodcompbilat L L)(at level 10).

Definition consistent {T}{L : complat T}(p : L^2) := @le _  L (pr1 p) (pr2 p).
Definition complete {T}{L : complat T}(p : L^2) :=  (pr1 p) = (pr2 p).

(* Lemma complete_maximalconsistent {T}{L : complat T}(p : L^2) : 
  complete p -> ∏ q, consistent q ->  *)


Definition isOscillating {T}{L : complat T} (f : L -> L) (p : L^2) :=
   pr1 p = f (pr2 p) × pr2 p  = f (pr1 p).

Definition  oscillating {T}{L : complat T} (f : L -> L) := ∑ p : L^2, isOscillating f p.


Definition swap {T} {L : complat T}(p : L^2) : L^2 := (pr2 p,, pr1 p).

Definition isExtreme {T} {L : complat T} (f : L -> L) (p : L^2) :=
  isOscillating f p ×  ∏ q : oscillating f, p ≺k pr1 q × p ≺k swap (pr1 q).
Definition extreme {T} {L : complat T} (f : L -> L) := 
  ∑ p : L^2, isExtreme f p.
Definition extreme_to_oscillating {T} {L : complat T} (f : L -> L) (p : extreme f) : L^2 := pr1 p.
Coercion extreme_to_oscillating : extreme >-> pr1hSet.

Lemma extreme_unique {T} {L : complat T} (f : L -> L) (p q : extreme f) : pr1 p = pr1 q.
  destruct p as [p [Hp1 Hp2]], q as [q [Hq1 Hq2]] => /=.
  move : (Hp2 (q,, Hq1)) => [pq pq'].
  move : (Hq2 (p,, Hp1)) => [qp qp'].
  destruct p as [x y], q as [a b].
  simpl in *.
  apply prod_dest in pq, pq', qp, qp'; simpl in *.
  induction pq, pq', qp, qp'.
  apply two_arg_paths;
  eapply antisymL; eauto.
  - rewrite joinC in pr5.
    apply meet_join in pr5; eauto.
  - rewrite joinC in pr2.
    apply meet_join in pr2; eauto.
Qed.



Definition lfp2 {T} {L : complat T} (f : L -> L) (Hf : antimono f) :=
  lfp (f ∘ f) (antimono_compose_mono Hf Hf).

Definition gfp2 {T} {L : complat T} (f : L -> L) (Hf : antimono f) :=
  gfp (f ∘ f) (antimono_compose_mono Hf Hf).

Theorem fp2_extreme {T} {L : complat T} (f : L -> L) (Hf : antimono f) :
  isExtreme f (lfp2 Hf,, gfp2 Hf ).
Proof.
  move : (tarski_gfp _ _ (f ∘ f) (antimono_compose_mono Hf Hf)) => [Hg1 Hg2].
  move : (tarski_lfp _ _ (f ∘ f) (antimono_compose_mono Hf Hf)) => [Hl1 Hl2].
  change (lfp (f ∘ f) (antimono_compose_mono Hf Hf)) with (lfp2 Hf) in *.
  change (gfp (f ∘ f) (antimono_compose_mono Hf Hf)) with (gfp2 Hf) in *.
  remember (gfp2 Hf) as gfp; clear Heqgfp.
  remember (lfp2 Hf) as lfp; clear Heqlfp.
  unfold funcomp in *.
  split.
  {
    unfold isOscillating; split => /=.
    - apply antisymL.
      * apply Hl2.
        rewrite Hg1; auto.
      * rewrite <- Hl1.
        apply Hf.
        apply Hg2.
        rewrite Hl1; auto.
    - apply antisymL.
      * rewrite <- Hg1.
        apply Hf.
        apply Hl2.
        rewrite Hg1; auto.  
      * apply Hg2.
        rewrite Hl1; auto.
  }
  {
    move => [[x y] Hp] => //=; split; apply two_arg_paths.
    all : unfold isOscillating in Hp; simpl in Hp; induction Hp as [x_fy y_fx].
    all : try match goal with
    | [|- join ?l _ = ?l ] => rewrite joinC; apply meet_join
    end.
    all : try apply Hg2.
    all : try apply Hl2.
    all : unfold funcomp.
    all : repeat ((try rewrite <- y_fx); (try rewrite <- x_fy)).
    all : auto.
  }
Qed.



Definition fstOf {T} {L : complat T} (f: L^2 -> L^2) : L^2 -> L := fun p => @pr1 L (λ _ : L, L) (f p).
Definition sndOf {T} {L : complat T} (f: L^2 -> L^2) : L^2 -> L := fun p => @pr2 L (λ _ : L, L) (f p).

Definition isSymmetricFunc {T} {L : complat T} (f : L^2 -> L^2) :=
  ∏ p : L^2, fstOf f p = sndOf f (swap p).



Definition klemono  {T} {L : complat T} (f : L^2 -> L^2) :=
  @mono _ (pr21 (L^2)) (pr21 (L^2)) f.
Definition tlemono {T} {L : complat T} (f : L^2 -> L^2) :=
  @mono _ (pr11 (L^2)) (pr11 (L^2)) f.
Definition tleantimono {T} {L : complat T} (f : L^2 -> L^2) :=
  @antimono _ (pr11 (L^2)) (pr11 (L^2)) f.


Lemma symmetricFunc_klemono {T} {L : complat T} (f : L^2 -> L^2) (Hf : isSymmetricFunc f) :
  klemono f
  <->
  ((∏ y : L, @mono _ L L  (fun x => fstOf f (x,, y))) ×
   (∏ x : L, @antimono _ L L  (fun y => fstOf f (x,, y)))).
Proof.
  unfold mono, antimono, fstOf, sndOf.
  split => H.
  { split; [move => y|move => x] => a b ab.
    - assert (@kle _ (L^2) (a,,y) (b,,y)). {
      simpl. apply two_arg_paths; auto.
      apply joinI.      
      }
      move : (H _ _ X) => H0.
      apply pbl_kle in H0.
      apply H0.
    - assert (@kle _ (L^2) (x,,b) (x,,a)). {
        simpl. apply two_arg_paths; auto.
        - apply meetI.
        - rewrite joinC; apply meet_join; auto. 
      }
      move : (H _ _ X) => H0.
      apply pbl_kle in H0.
      apply H0.  
  }
  { induction H as [H1 H2].
    move => [a1 a2] [b1 b2] ab.
    apply pbl_kle in ab.
    induction ab as [ab ba].
    apply pbl_kle.    
    split.    
    - eapply transL; [apply H1; eauto|].
      eapply transL; [eapply H2; eauto|].
      apply meetI.
    - move : (Hf (a2,,a1)) => Ha.
      move : (Hf (b2,,b1)) => Hb.
      unfold swap, fstOf, sndOf in Ha, Hb; simpl in Ha, Hb.
      apply transL with (pr1 (f (b2,, b1))).
      - rewrite Hb. apply meetI.
      apply transL with (pr1 (f (a2,, a1))); first last.
      - rewrite Ha. apply meetI.
      eapply transL; [apply H1; eauto|].
      eapply transL; [eapply H2; eauto|].
      apply meetI.
  }
Qed.


Lemma symmetricFunc_tlemono {T} {L : complat T} (f : L^2 -> L^2) (Hf : isSymmetricFunc f) :
  tlemono f
  <->
  ((∏ y : L, @mono _ L L  (fun x => fstOf f (x,, y))) ×
   (∏ x : L, @mono _ L L  (fun y => fstOf f (x,, y)))).
Proof.
   unfold mono, antimono, fstOf, sndOf.
  split => H.
  { split; [move => y|move => x] => a b ab.
    - assert (@tle _ (L^2) (a,,y) (b,,y)). {
      simpl. apply two_arg_paths; auto.
      apply meetI.
      }
      move : (H _ _ X) => H0.
      apply pbl_tle in H0.
      apply H0.
    - assert (@tle _ (L^2) (x,,a) (x,,b)). {
        simpl. apply two_arg_paths; auto.
        apply meetI.
      }
      move : (H _ _ X) => H0.
      apply pbl_tle in H0.
      apply H0.  
  }
  { induction H as [H1 H2].
    move => [a1 a2] [b1 b2] ab.
    apply pbl_tle in ab.
    induction ab as [ab1 ab2].
    apply pbl_tle.    
    split.    
    - eapply transL; [apply H1; eauto|].
      eapply transL; [eapply H2; eauto|].
      apply meetI.
    - move : (Hf (a2,,a1)) => Ha.
      move : (Hf (b2,,b1)) => Hb.
      unfold swap, fstOf, sndOf in Ha, Hb; simpl in Ha, Hb.
      apply transL with (pr1 (f (a2,, a1))).
      - rewrite Ha. apply meetI.
      apply transL with (pr1 (f (b2,, b1))); first last.
      - rewrite Hb. apply meetI.      
      eapply transL; [apply H1; eauto|].
      eapply transL; [eapply H2; eauto|].
      apply meetI.
  }
Qed.

Lemma symmetricFunc_tleantimono {T} {L : complat T} (f : L^2 -> L^2) (Hf : isSymmetricFunc f) :
  tleantimono f
  <->
  ((∏ y : L, @antimono _ L L  (fun x => fstOf f (x,, y))) ×
   (∏ x : L, @antimono _ L L  (fun y => fstOf f (x,, y)))).
Proof.
   unfold mono, antimono, fstOf, sndOf.
  split => H.
  { split; [move => y|move => x] => a b ab.
    - assert (@tle _ (L^2) (a,,y) (b,,y)). {
      simpl. apply two_arg_paths; auto.
      apply meetI.
      }
      move : (H _ _ X) => H0.
      apply pbl_tle in H0.
      apply H0.
    - assert (@tle _ (L^2) (x,,a) (x,,b)). {
        simpl. apply two_arg_paths; auto.
        apply meetI.
      }
      move : (H _ _ X) => H0.
      apply pbl_tle in H0.
      apply H0.  
  }
  { induction H as [H1 H2].
    move => [a1 a2] [b1 b2] ab.
    apply pbl_tle in ab.
    induction ab as [ab1 ab2].
    apply pbl_tle.    
    split.    
    - eapply transL; [apply H1; eauto|].
      eapply transL; [eapply H2; eauto|].
      apply meetI.
    - move : (Hf (a2,,a1)) => Ha.
      move : (Hf (b2,,b1)) => Hb.
      unfold swap, fstOf, sndOf in Ha, Hb; simpl in Ha, Hb.
      apply transL with (pr1 (f (a2,, a1))); first last.
      - rewrite Ha. apply meetI.
      apply transL with (pr1 (f (b2,, b1))).
      - rewrite Hb. apply meetI.      
      eapply transL; [apply H1; eauto|].
      eapply transL; [eapply H2; eauto|].
      apply meetI.
  }
Qed.

Lemma symmetricFunc_mono {T} {L : complat T} (f : L^2 -> L^2) (Hf : isSymmetricFunc f) :
  (klemono f × tlemono f)
  <->
  (∑ g : L -> L, mono g ×  ∏ x y : L, f (x,,y) = (g x,, g y)).
Proof.
  split.
  {
    move => [Hk Ht].
    apply (symmetricFunc_klemono Hf) in Hk; move : Hk => [Hky Hkx].
    apply (symmetricFunc_tlemono Hf) in Ht; move : Ht => [Hty Htx].
    exists (fun x => fstOf f (x,, x)); simpl; split.
    - move => a b ab.
      eapply transL.
      - rewrite (mono_antimono_constant (Htx a) (Hkx a) a b). 
        apply meetI.
      - apply (Hky b a b ab).
    - move => x y.
      move : (mono_antimono_constant (Htx x) (Hkx x) x y) ->.
      move : (mono_antimono_constant (Htx y) (Hkx y) y x) ->.
      move : (Hf (y,,x)) ->.
      change (swap (y,, x)) with (x,,y).
      unfold fstOf, sndOf.      
      induction (f (x,,y)) => //=.    
  }
  {
    move => [g [monog Hg]]; split.
    { apply symmetricFunc_klemono; auto.
      split; [move => y|move => x] => a b ab.
      all : unfold fstOf.
      1 : move : (Hg a y) (Hg b y).
      2 : move : (Hg x a) (Hg x b).
      all : move ->; move ->; simpl.
      - apply monog; auto.
      - apply meetI.
    }
    { apply symmetricFunc_tlemono; auto.
      split; [move => y|move => x] => a b ab.
      all : unfold fstOf.
      1 : move : (Hg a y) (Hg b y).
      2 : move : (Hg x a) (Hg x b).
      all : move ->; move ->; simpl.
      - apply monog; auto.
      - apply meetI.
    }
  }
Qed.

Lemma symmetricFunc_antimono {T} {L : complat T} (f : L^2 -> L^2) (Hf : isSymmetricFunc f) :
  (klemono f × tleantimono f)
  <->
  (∑ g : L -> L, antimono g ×  ∏ x y : L, f (x,,y) = (g y,, g x)).
Proof.
  split.
  {
    move => [Hk Ht].
    apply (symmetricFunc_klemono Hf) in Hk; move : Hk => [Hky Hkx].
    apply (symmetricFunc_tleantimono Hf) in Ht; move : Ht => [Hty Htx].
    exists (fun x => fstOf f (x,, x)); simpl; split.
    - move => a b ab.
      eapply transL.
      - apply (Htx b a b ab).
      - rewrite (mono_antimono_constant (Hky a) (Hty a) a b). 
        apply meetI.     
    - move => x y.
      move : (mono_antimono_constant (Hky x) (Hty x) x y) ->.
      move : (mono_antimono_constant (Hky y) (Hty y) y x) ->.
      move : (Hf (y,,x)) ->.
      change (swap (y,, x)) with (x,,y).
      unfold fstOf, sndOf.      
      induction (f (x,,y)) => //=.    
  }
  {
    move => [g [monog Hg]]; split.
    { apply symmetricFunc_klemono; auto.
      split; [move => y|move => x] => a b ab.
      all : unfold fstOf.
      1 : move : (Hg a y) (Hg b y).
      2 : move : (Hg x a) (Hg x b).
      all : move ->; move ->; simpl.
      - apply meetI.
      - apply monog; auto.      
    }
    { apply symmetricFunc_tleantimono; auto.
      split; [move => y|move => x] => a b ab.
      all : unfold fstOf.
      1 : move : (Hg a y) (Hg b y).
      2 : move : (Hg x a) (Hg x b).
      all : move ->; move ->; simpl.
      - apply meetI.
      - apply monog; auto.      
    }
  }
Qed.

  


Section fixpoint_extreme.

  Variable T : hSet.
  Variable L : complat T.
  Variable A : L^2 -> L^2.
  Hypotheses kle_mono :  klemono A.
  Hypotheses tle_antimono :  tleantimono A.
  Hypotheses A_sym : isSymmetricFunc A.
  
  (* fixpoints of A with respect to ≺k *)
  Notation qA := (lfp A kle_mono).
  Notation QA :=(gfp A kle_mono).
  (* fixpoints of A∘A with respect to ≺t *)
  Notation eA := (lfp2 tle_antimono ).
  Notation EA := (gfp2 tle_antimono ).
  Notation eA_AEA := (pr11 (fp2_extreme tle_antimono)).
  Notation EA_AeA := (pr21 (fp2_extreme tle_antimono)).
  Notation HeAA := (pr2 (fp2_extreme tle_antimono)).
  
  (* A (x, y)  = O y,, O x *)
  (* antimono O *)
  Notation O  := (pr1 (pr1 (symmetricFunc_antimono A_sym) (kle_mono,, tle_antimono))).
  Notation HO' :=(pr2 (pr1 (symmetricFunc_antimono A_sym) (kle_mono,, tle_antimono))).
  Notation O_antimono := (pr1 HO').
  Notation HO := (pr2 HO').
  (* fixpoints of O∘O *)
  Notation q := (lfp2 O_antimono).
  Notation Q := (gfp2 O_antimono).

  Notation q_OQ := (pr11 (fp2_extreme O_antimono)).
  Notation Q_Oq := (pr21 (fp2_extreme O_antimono)).
  Notation HeOO := (pr2 (fp2_extreme O_antimono)).
  

  Lemma qA_qQ :
    qA =q,, Q.
  Proof.
    move : HO => HO.
    move : HeOO => He.
    move : q_OQ => /= Hq.
    move : Q_Oq => /= HQ.    
    move : (tarski_lfp _ _ (O ∘ O) (antimono_compose_mono O_antimono O_antimono)) => [Hq1 Hq2].
    change (lfp (O ∘ O) (antimono_compose_mono O_antimono O_antimono)) with q in *.
    move : (tarski_lfp _ _ A kle_mono) => [H1 H2].
    apply (@antisymL _ (pr21 (L^2))).
    - move : (HO q Q) => HqQ.
      rewrite <- Hq, <- HQ in HqQ.
      apply (H2 (q,, Q) HqQ) => Hl.
    - assert (isOscillating O qA). {
        destruct qA as [x y].
        rewrite (HO x y) in H1.
        apply prod_dest in H1; simpl in H1.
        induction H1.
        split; symmetry; auto.
      }
      move : (He (qA,, X)) => [Hl Hr].
      auto.
  Qed.      

  Lemma QA_Qq :
    QA =Q,, q.
  Proof.
    move : HO => HO.
    move : HeOO => He.
    move : q_OQ => /= Hq.
    move : Q_Oq => /= HQ.
    move : (tarski_gfp _ _ (O ∘ O) (antimono_compose_mono O_antimono O_antimono)) => [HHQ1 HQ2].
    change (gfp (O ∘ O) (antimono_compose_mono O_antimono O_antimono)) with Q in *.        
    move : (tarski_gfp _ _ A kle_mono) => [H1 H2].
    apply (@antisymL _ (pr21 (L^2))); first last.
    - move : (HO Q q) => HqQ.
      rewrite <- Hq, <- HQ in HqQ.
      apply (H2 (Q,, q) HqQ) => Hl.
    - change (QA ≺ (Q,, q)) with (@kle _ (prodcompbilat L L) QA (Q,, q)).
      assert (isOscillating O QA). {
        destruct QA as [x y].
        rewrite (HO x y) in H1.
        apply prod_dest in H1; simpl in H1.
        induction H1.
        split; symmetry; auto.
      }
      move : (He (QA,, X)) => [Hl Hr].
      destruct QA as [a b] eqn: E.
      unfold swap in Hr.
      simpl in Hr.
      apply prod_dest in Hr; simpl in Hr.
      induction Hr as [Hr1 Hr2].
      simpl.
      apply two_arg_paths.
      - apply meet_join. rewrite joinC. auto.
      - rewrite joinC. apply meet_join. auto. 
  Qed.

  Lemma eA_qq :
    eA =q,, q.
  Proof.
    move : HO => HO.
    move : HeOO => HeOO.
    move : HeAA => HeAA.
    move : q_OQ => /= Hq.
    move : Q_Oq => /= HQ.
    move : (HO q q). rewrite <- HQ => Aq.
    move : (HO Q Q). rewrite <- Hq => AQ.
    apply (@antisymL _ (pr11 (L^2))).
    -  move : (tarski_lfp _ _ (A ∘ A) (antimono_compose_mono tle_antimono tle_antimono)) => [_ H2]. 
      change (lfp (A ∘ A) (antimono_compose_mono tle_antimono tle_antimono)) with eA in *.          
      eapply H2. 
      unfold funcomp; rewrite Aq AQ; auto.
    -       
      assert (@isOscillating _ (pr21 (L^2)) A ((q,,q),,(Q,,Q))). {
        split => /=; symmetry; auto.
      }
      assert (@isExtreme _ (pr11 (L^2)) A ((q,,q),,(Q,,Q))). {     
        split; auto.        
        move => [[[x1 x2] [y1 y2]]] [/= Hy Hx].       
        change (join (Q,, Q : L^2)  (y1,, y2)) with (join Q y1,, join Q y2 : L^2).
        change (join (Q,, Q : L^2)  (x1,, x2)) with (join Q x1,, join Q x2 : L^2).

        rewrite (HO x1 x2) in Hx.
        rewrite (HO y1 y2) in Hy.
        apply prod_dest in Hx, Hy; simpl in Hx,Hy.
        induction Hx as [Hy1 Hy2].
        induction Hy as [Hx1 Hx2].

        assert ((O∘O) x1 = x1) by  (unfold funcomp; rewrite <- Hy2, Hx1; auto).
        assert ((O∘O) x2 = x2) by  (unfold funcomp; rewrite <- Hy1, Hx2; auto).
        assert ((O∘O) y1 = y1) by  (unfold funcomp; rewrite <- Hx2, Hy1; auto).
        assert ((O∘O) y2 = y2) by  (unfold funcomp; rewrite <- Hx1, Hy2; auto).
        move : (tarski_lfp _ _ (O ∘ O) (antimono_compose_mono O_antimono O_antimono)) => [Hf1 Hf2].
        move : (tarski_gfp _ _ (O ∘ O) (antimono_compose_mono O_antimono O_antimono)) => [Hg1 Hg2].               
        change (lfp (O ∘ O) (antimono_compose_mono O_antimono O_antimono)) with q in *.
        change (gfp (O ∘ O) (antimono_compose_mono O_antimono O_antimono)) with Q in *.


        split; repeat apply two_arg_paths.       
        all : try match goal with
                  | [|- join _ _ = _] => rewrite joinC; apply meet_join
                  end.
         all : try apply Hf2; auto.
         all : try apply Hg2; auto.         
      }

      move : ((pr2 X0) ((eA,,EA),, (pr1 (fp2_extreme tle_antimono)))) => [Hl Hr].
      simpl in Hr, Hl.
      change ((join (Q,, Q : L^2) EA)) with (join Q (pr1 EA),, join Q (pr2 EA) : L^2) in *.
      change ((join (Q,, Q : L^2) eA)) with (join Q (pr1 eA),, join Q (pr2 eA) : L^2) in *.
      
      change ((inf (image_hsubtype (λ x : T × T, A (A x) ≺ x) pr1))) with (pr1 eA) in *.
      change ((inf (image_hsubtype (λ x : T × T, A (A x) ≺ x) pr2))) with (pr2 eA) in *.
      change (sup (image_hsubtype (λ x , x ≺ A (A x)) pr2)) with (pr2 EA) in *.
      change (sup (image_hsubtype (λ x , x ≺ A (A x)) pr1)) with (pr1 EA) in *.
      
      apply  (@prod_dest (L^2) (L^2)) in Hr, Hl.
      induction Hr as [Hr Hr'].
      induction Hl as [Hl Hl'].
      unfold pr1, pr2 in Hr, Hr', Hl, Hl'.
      apply prod_dest in Hr, Hr', Hl, Hl'.

      unfold pr1, pr2 in Hr, Hr', Hl, Hl'.
      induction Hr as [Hr1 Hr2].
      induction Hr' as [Hr1' Hr2'].
      induction Hl as [Hl1 Hl2].
      induction Hl' as [Hl1' Hl2'].
      
      simpl.
      change ((inf (image_hsubtype (λ x : T × T, A (A x) ≺ x) pr1))) with (pr1 eA) in *.
      change ((inf (image_hsubtype (λ x : T × T, A (A x) ≺ x) pr2))) with (pr2 eA) in *.
      apply two_arg_paths; auto.
  Qed.

  Lemma EA_QQ :
    EA = Q,,Q.
  Proof.
    move : HO => HO.
    move : HeOO => HeOO.
    move : HeAA => HeAA.
    move : q_OQ => /= Hq.
    move : Q_Oq => /= HQ.
    move : (HO q q). rewrite <- HQ => Aq.
    move : (HO Q Q). rewrite <- Hq => AQ.
    apply (@antisymL _ (pr11 (L^2))); first last.
    - move : (tarski_gfp _ _ (A ∘ A) (antimono_compose_mono tle_antimono tle_antimono)) => [_ H2]. 
      change (gfp (A ∘ A) (antimono_compose_mono tle_antimono tle_antimono)) with EA in *.      
      apply H2. 
      unfold funcomp; rewrite AQ Aq; auto.
    -       
      assert (@isOscillating _ (pr21 (L^2)) A ((q,,q),,(Q,,Q))). {
        split => /=; symmetry; auto.
      }
      assert (@isExtreme _ (pr11 (L^2)) A ((q,,q),,(Q,,Q))). {     
        split; auto.        
        move => [[[x1 x2] [y1 y2]]] [/= Hy Hx].       
        change (join (Q,, Q : L^2)  (y1,, y2)) with (join Q y1,, join Q y2 : L^2).
        change (join (Q,, Q : L^2)  (x1,, x2)) with (join Q x1,, join Q x2 : L^2).

        rewrite (HO x1 x2) in Hx.
        rewrite (HO y1 y2) in Hy.
        apply prod_dest in Hx, Hy; simpl in Hx,Hy.
        induction Hx as [Hy1 Hy2].
        induction Hy as [Hx1 Hx2].

        assert ((O∘O) x1 = x1) by  (unfold funcomp; rewrite <- Hy2, Hx1; auto).
        assert ((O∘O) x2 = x2) by  (unfold funcomp; rewrite <- Hy1, Hx2; auto).
        assert ((O∘O) y1 = y1) by  (unfold funcomp; rewrite <- Hx2, Hy1; auto).
        assert ((O∘O) y2 = y2) by  (unfold funcomp; rewrite <- Hx1, Hy2; auto).
        move : (tarski_lfp _ _ (O ∘ O) (antimono_compose_mono O_antimono O_antimono)) => [Hf1 Hf2].
        move : (tarski_gfp _ _ (O ∘ O) (antimono_compose_mono O_antimono O_antimono)) => [Hg1 Hg2].               
        change (lfp (O ∘ O) (antimono_compose_mono O_antimono O_antimono)) with q in *.
        change (gfp (O ∘ O) (antimono_compose_mono O_antimono O_antimono)) with Q in *.


        split; repeat apply two_arg_paths.       
        all : try match goal with
                  | [|- join _ _ = _] => rewrite joinC; apply meet_join
                  end.
         all : try apply Hf2; auto.
         all : try apply Hg2; auto.         
      }

      move : ((pr2 X0) ((eA,,EA),, (pr1 (fp2_extreme tle_antimono)))) => [Hl Hr].
      simpl in Hr, Hl.
      change ((join (Q,, Q : L^2) EA)) with (join Q (pr1 EA),, join Q (pr2 EA) : L^2) in *.
      change ((join (Q,, Q : L^2) eA)) with (join Q (pr1 eA),, join Q (pr2 eA) : L^2) in *.
      
      change ((inf (image_hsubtype (λ x : T × T, A (A x) ≺ x) pr1))) with (pr1 eA) in *.
      change ((inf (image_hsubtype (λ x : T × T, A (A x) ≺ x) pr2))) with (pr2 eA) in *.
      change (sup (image_hsubtype (λ x , x ≺ A (A x)) pr2)) with (pr2 EA) in *.
      change (sup (image_hsubtype (λ x , x ≺ A (A x)) pr1)) with (pr1 EA) in *.
      
      apply  (@prod_dest (L^2) (L^2)) in Hr, Hl.
      induction Hr as [Hr Hr'].
      induction Hl as [Hl Hl'].
      unfold pr1, pr2 in Hr, Hr', Hl, Hl'.
      apply prod_dest in Hr, Hr', Hl, Hl'.

      unfold pr1, pr2 in Hr, Hr', Hl, Hl'.
      induction Hr as [Hr1 Hr2].
      induction Hr' as [Hr1' Hr2'].
      induction Hl as [Hl1 Hl2].
      induction Hl' as [Hl1' Hl2'].
      
      simpl. 

      change ((sup (image_hsubtype (λ x, x ≺ A (A x)) pr1))) with (pr1 EA) in *.
      change ((sup (image_hsubtype (λ x, x ≺ A (A x)) pr2))) with (pr2 EA) in *.
      rewrite joinC in Hl1'.
      rewrite joinC in  Hl2'.
      apply meet_join in Hl1', Hl2'.      
      rewrite Hl1' Hl2'.
      eauto.
  Qed.

  Lemma qA_kmeet :
    qA = eA <*> EA.
  Proof.
    rewrite qA_qQ eA_qq EA_QQ.
    unfold kmeet, meet => //=.
    move : (tarski_lfp _ _ (O ∘ O) (antimono_compose_mono O_antimono O_antimono)) => [_ Hl].
    move : (tarski_gfp _ _ (O ∘ O) (antimono_compose_mono O_antimono O_antimono)) => [Hg _ ].
    apply two_arg_paths; apply pathsinv0; [| apply meet_join];
    apply Hl; auto.
  Qed.

  Lemma QA_kjoin :
    QA = eA <+> EA.
  Proof.
    rewrite QA_Qq eA_qq EA_QQ.
    unfold kjoin, join => //=.
    move : (tarski_lfp _ _ (O ∘ O) (antimono_compose_mono O_antimono O_antimono)) => [_ Hl].
    move : (tarski_gfp _ _ (O ∘ O) (antimono_compose_mono O_antimono O_antimono)) => [Hg _ ].
    apply two_arg_paths; apply pathsinv0; [apply meet_join|];
    apply Hl; auto.
  Qed.

  Lemma eA_tmeet :
    eA = @tmeet _ (L^2) qA  QA.
  Proof.
    rewrite eA_qq qA_qQ QA_Qq.
    unfold tmeet, kmeet, meet => //=.
    move : (tarski_lfp _ _ (O ∘ O) (antimono_compose_mono O_antimono O_antimono)) => [_ Hl].
    move : (tarski_gfp _ _ (O ∘ O) (antimono_compose_mono O_antimono O_antimono)) => [Hg _ ].
    apply two_arg_paths; apply pathsinv0; [| rewrite meetC];
    apply Hl; auto.
  Qed.

  Lemma eA_tjoin :
    EA = @tjoin _ (L^2) qA  QA.
  Proof.
    rewrite EA_QQ qA_qQ QA_Qq.
    unfold tjoin, kjoin, join => //=.
    move : (tarski_lfp _ _ (O ∘ O) (antimono_compose_mono O_antimono O_antimono)) => [_ Hl].
    move : (tarski_gfp _ _ (O ∘ O) (antimono_compose_mono O_antimono O_antimono)) => [Hg _ ].
    apply two_arg_paths; apply pathsinv0; [| rewrite joinC];
    apply meet_join; apply Hl; auto.
  Qed.

End fixpoint_extreme.

Definition extends {T : hSet} {L : complat T} (A : L^2 -> L^2) (O : L -> L) :=
  ∏ x, A (x,,x) = O x,, O x.

Definition extending {T : hSet} {L : complat T} (A : L^2 -> L^2)  :=
  ∏ x, ∑ y, A (x,,x) = y,,y.

Definition trivial {T : hSet} {L : complat T} (O : L -> L) : L^2 -> L^2 :=
  fun p => O (pr1 p),, O (pr2 p).

Definition exact {T : hSet} {L : complat T} (p : L^2 ) :=
  pr1 p = pr2 p.

Lemma extends_fixpoint {T : hSet} {L : complat T} (A : L^2 -> L^2) (O : L -> L) :
  extends A O -> ∏ x, (A (x,,x) = x,,x <-> O x = x).
Proof.
  move => He x; split => H.
  - rewrite (He x) in H.
    apply prod_dest in H.
    induction H as [_ H2]; auto.
  - rewrite (He x) H; auto.
Qed.

Lemma symmetricFunc_extending {T : hSet} {L : complat T} (A : L^2 -> L^2) :
  isSymmetricFunc A -> extending A.
Proof.
  move => H x.
  move : (H (x,,x)).
  unfold swap, fstOf, sndOf => /= HA.
  destruct (A (x,, x)) as [a b]; simpl in HA.
  exists a. rewrite HA; auto.
Qed.


  

Definition approximates {T} {L : complat T} (A : L^2 -> L^2) (O : L -> L) :=
  isSymmetricFunc A × klemono A × extends A O.

Definition approximating {T} {L : complat T} (A : L^2 -> L^2) :=
  isSymmetricFunc A × klemono A.

Definition consistentFunc {T} {L : complat T} (A : L^2 -> L^2) :=
  ∏ p, consistent p -> consistent (A p).

Lemma approximating_consistent {T} {L : complat T} (A : L^2 -> L^2) :
  approximating A -> consistentFunc A.
Proof.
  move => [HA Hk] [x y].
  unfold consistent, pr1, pr2 => H0.  
  move : (HA (x,,y)).
  unfold swap, fstOf, pr1, sndOf,pr2.
  move ->.
  assert (@kle _ (L^2) (x,,y) (y,,x)). {
    simpl.
    apply two_arg_paths; auto.
    rewrite joinC; apply meet_join; auto.
  }
  move : (Hk _ _ X) => Hxy.
  simpl in Hxy. simpl in Hxy.
  apply prod_dest in Hxy.
  unfold pr1, pr2 in Hxy.
  induction Hxy as [Hxy1 Hxy2].
  rewrite joinC in Hxy2.
  apply meet_join in Hxy2.
  auto.
Qed.


Lemma lfpA_consistent {T} {L : complat T} (A : L^2 -> L^2) (O : L -> L) (HA : approximates A O):
  @consistent _ L (lfp A (pr12 HA)).
Proof.
  unfold consistent.
  induction HA as [Hs [Hk He]].
  unfold pr1,pr2.
  destruct (lfp A Hk) as [a b] eqn:E.
  rewrite E.
  move : (Hs (a,,b)).
  unfold swap, fstOf, sndOf, pr1, pr2 => H1.
  move : (Hs (b,,a)).
  unfold swap, fstOf, sndOf, pr1, pr2 => H2.
  move : (tarski_lfp _ _ _ Hk) => [Hfp Hlfp].
  rewrite E in Hfp.
  rewrite Hfp in H1, H2.
  assert (A (b,,a) = b,,a). {
    induction (A (b,,a)) as [x y].
    rewrite H1 H2; auto.
  }
  move : (Hlfp _ X) => H0.
  rewrite E in H0.
  simpl in H0.
  apply prod_dest in H0.
  induction H0; auto.
Qed.  
  
Lemma approximate_fixpoint {T} {L : complat T} (A : L^2 -> L^2) (O : L -> L) (HA : approximates A O):
  ∏ x : L, O x = x -> pr1 (lfp A (pr12 HA)) ≺ x × x ≺ pr2 (lfp A (pr12 HA)).
Proof.
  move => x H.  
  induction HA as [Hs [Hk He]].
  unfold pr1,pr2 in *.
  move : (tarski_lfp _ _ _ Hk) => [Hfp Hlfp].
  destruct (lfp A Hk) as [a b] eqn:E.
  rewrite E.  
  move : (He x) => Hx.
  rewrite H in Hx.
  move : (Hlfp _ Hx).
  rewrite E => Hxx.
  simpl in Hxx.
  apply prod_dest in Hxx.
  induction Hxx as [ax xb].
  split; auto.
  apply meet_join. 
  rewrite joinC; auto.
Qed.


Lemma symmetric_trivial {T} {L : complat T} (O : L -> L) (Hm : mono O):
  isSymmetricFunc (trivial O).
Proof.
  move => [x y].
  unfold trivial, swap, fstOf, sndOf, pr1, pr2; auto.
Qed.

Lemma klemono_trivial {T} {L : complat T} (O : L -> L) (Hm : mono O):
  klemono (trivial O).
Proof.
  suff : (klemono (trivial O) × tlemono (trivial O)). {
    move => [Hk _]; auto.
  }
  apply symmetricFunc_mono; first last.
  - exists O; split; auto.
  - apply symmetric_trivial; auto. 
Qed.

Lemma tlemono_trivial {T} {L : complat T} (O : L -> L) (Hm : mono O):
  tlemono (trivial O).
Proof.
  suff : (klemono (trivial O) × tlemono (trivial O)). {
    move => [_ Ht]; auto.
  }
  apply symmetricFunc_mono; first last.
  - exists O; split; auto.
  - apply symmetric_trivial; auto. 
Qed.

Definition applroximating_trivial {T} (L : complat T) (O : L -> L) (Hm : mono O)
  : approximating (trivial O) := (symmetric_trivial Hm,, klemono_trivial Hm).

Lemma approximates_trivial {T} (L : complat T) (O : L -> L) (Hm : mono O) :
  approximates (trivial O) O.
Proof.
  repeat split.
  exact (klemono_trivial Hm).
Qed. 

Lemma extends_trivial {T} (L : complat T) (O : L -> L) (Hm : mono O) :
  extends (trivial O) O.
Proof.
  unfold extends, trivial => //=.
Qed.

Lemma exact_trivial {T} (L : complat T) (O : L -> L) (Hm : mono O)  :
  ∏ p, exact p ->  exact (trivial O p).
Proof.
  unfold exact, trivial => /=.
  move => p ->; auto.
Qed.  

Lemma trivial_lfp_exact {T} (L : complat T) (O : L -> L) (HO : mono O) :
  @exact _ L (lfp (trivial O) (klemono_trivial HO)).
Proof.
  (*帰納法を実装しないとできないかも*)
Abort.  


Lemma trivial_lfp {T} (L : complat T) (O : L -> L) (HO : mono O) :
  lfp (trivial O) (klemono_trivial HO) = lfp O HO,, lfp O HO.
Proof.
  move : (tarski_lfp _ _ _ (klemono_trivial HO)) => [AOfp AOlfp].
  move : (tarski_lfp _ _ _ HO) => [Ofp Olfp].  
  move : (approximate_fixpoint (approximates_trivial HO) Ofp) => [H1 H2].  
  eapply pathscomp0.
  - symmetry.
    exact AOfp.
  - rewrite <- Ofp.
    unfold trivial.
    change ((λ p : L ^2, O (pr1 p),, O (pr2 p))) with (trivial O).
    apply two_arg_paths.
    all : apply maponpaths.
    all : apply antisymL; auto.
    * apply is_inf => b.
      unfold In => H.
      unfold image_hsubtype in H.
      unfold ishinh, ishinh_UU in H.
      apply H => [[[x1 x2] [Hx1 Hx2]]].
      simpl in Hx1.
      unfold trivial, pr1, pr2 in Hx2.
      simpl in Hx2.
      apply prod_dest in Hx2.
      unfold pr1, pr2 in Hx2.
      induction Hx2 as [Hl Hr].
      move : (lfp_prefixpoint T L O HO x1 Hl) => Ha.
      rewrite <- Hx1; auto.
    * apply is_sup => b.
      unfold In => H.
      unfold image_hsubtype in H.
      unfold ishinh, ishinh_UU in H.
      apply H => [[[x1 x2] [Hx1 Hx2]]].
      simpl in Hx1.
      unfold trivial, pr1, pr2 in Hx2.
      simpl in Hx2.
      apply prod_dest in Hx2.
      unfold pr1, pr2 in Hx2.
      induction Hx2 as [Hl Hr].
Abort.     


Definition completeStable {T} {L : complat T} (A : L^2 -> L^2) (H : approximating A) :
  L -> L.
Proof.
  move => y.
  exact (lfp _ (pr1 (pr1 (symmetricFunc_klemono  (pr1 H)) (pr2 H)) y)).  
Defined.

Definition stable {T} {L : complat T} (A : L^2 -> L^2) (H : approximating A) : L^2 -> L^2 :=
  fun p => (completeStable H (pr2 p),, completeStable H (pr1 p)).

Lemma stable_constant{T} {L : complat T} (A : L^2 -> L^2) 
  (H : approximating A) (Ht : tlemono A) :
  ∏ y1 y2, stable H y1 = stable H y2.
Proof.
  induction H as [Hs Hk].
  move => y1 y2.
  move :  (symmetricFunc_mono Hs) => [Hm _].
  move : (Hm (Hk,,Ht)) => [O [monoO HO]].
  assert (∏ y, completeStable (Hs,, Hk) y = lfp O monoO). {    
    move => y.
    remember  (completeStable (Hs,, Hk) y) as p.
    remember (lfp O monoO) as q.
    move : (tarski_lfp _ _ _ (pr1 (pr1 (symmetricFunc_klemono Hs) Hk) y)) => [Afp Alfp].
    change (lfp (λ x : L, fstOf A (x,, y)) (pr1 (pr1 (symmetricFunc_klemono Hs) Hk) y))
    with (completeStable (Hs,, Hk) y) in *.
    rewrite <- Heqp in *.
    move : (tarski_lfp _ _ _ monoO) => [Ofp Olfp].
    rewrite <- Heqq in *.
    apply antisymL.
    - apply Alfp.
      unfold fstOf.
      rewrite (HO q y); simpl; auto.
    - apply Olfp.    
      unfold fstOf in Afp.
      rewrite (HO p y) in Afp.
      auto.
  }
  unfold stable.
  repeat rewrite X.
  apply two_arg_paths; auto.  
Qed.

Lemma approximating_tleantimono {T} {L : complat T} (A : L^2 -> L^2) 
  (H : approximating A) (Ht : tleantimono A) :
  stable H = A.
Proof.
  induction H as [Hs Hk].
  move :  (symmetricFunc_antimono Hs) => [Hm _].
  move : (Hm (Hk,,Ht)) => [O [monoO HO]].
  assert (completeStable (Hs,, Hk) = O). {    
    apply funextfun => x.
    move : (tarski_lfp _ _ _ (pr1 (pr1 (symmetricFunc_klemono Hs) Hk) x)) => [Afp Alfp].
    change (lfp (λ x0 : L, fstOf A (x0,, x)) (pr1 (pr1 (symmetricFunc_klemono Hs) Hk) x))
    with (completeStable (Hs,, Hk) x) in *.
    remember  (completeStable (Hs,, Hk) x) as p.
    unfold fstOf in Afp.
    rewrite (HO p x) in Afp; simpl in Afp.
    rewrite Afp; auto.
  }
  apply funextfun => p.
  induction p as [x y].
  unfold stable => /=.
  rewrite X.
  rewrite (HO x y); auto.
Qed.

Lemma stable_fixpoint_minimal {T} {L : complat T} (A : L^2 -> L^2) (HA : approximating A) :
  ∏ p, stable HA p = p -> ∏ q, A q = q -> q ≺t p -> p ≺t q.
Proof.
  induction HA as [Hs Hk].
  move => [x y] Hxy [a b] Hab Hpq.
  suff : ((x,, y) = (a,, b)).
  { move => ->. apply meetI. }
  apply prod_dest in Hxy.
  induction Hxy as [Hx Hy]; simpl in Hx, Hy.
  move : (symmetricFunc_klemono Hs) => [Hkle _].
  move : (Hkle Hk) => [_ Han].
  simpl in Hpq.
  apply prod_dest in Hpq; simpl in Hpq.
  induction Hpq as [Hpq1 Hpq2].  
  unfold completeStable in Hx, Hy.

  move : (Han a b y Hpq2). 
  assert (fstOf A (a,,b) = a). { 
    unfold fstOf, pr1, pr2. rewrite Hab. auto. 
  }  
  rewrite X => Ha; clear X.  
  move : (lfp_prefixpoint _ _ _ (pr1 (pr1 (symmetricFunc_klemono Hs) Hk) y)  _ Ha) => Ha'.  
  rewrite Hx in Ha'.

  move : (Han b a x Hpq1).
  rewrite (Hs (b,,a)).
  unfold swap, pr1, pr2.
  assert (sndOf A (a,,b) = b). { 
    unfold sndOf, pr1, pr2. rewrite Hab. auto. 
  }
  rewrite X => Hb; clear X.
  move : (lfp_prefixpoint _ _ _ (pr1 (pr1 (symmetricFunc_klemono Hs) Hk) x)  _ Hb) => Hb'.
  rewrite Hy in Hb'.

  apply two_arg_paths; apply (@antisymL _ L); auto.
Qed. 

Lemma Ay_antimono {T} {L : complat T} (A : L^2 -> L^2) (HA : approximating A) :
  ∏ x : L, antimono (λ y : L, fstOf A (x,, y)).
Proof.
  move => x a b ab.
  induction HA as [Hs Hk].
  assert (@kle _ (L^2) (x,,b) (x,,a)). {
    simpl.
    apply two_arg_paths.
    - apply meetI.
    - rewrite joinC. apply meet_join. auto.
  }
  apply Hk in X.
  simpl in X.
  apply prod_dest in X.
  induction X as [H1 H2].
  unfold fstOf,pr1,pr2 in *.
  auto.
Qed.

Lemma completeStable_antimono {T} {L : complat T} (A : L^2 -> L^2) 
  (HA : approximating A) : antimono (completeStable HA).
Proof.
  move => x y xy.
  move : (tarski_lfp _ _ _ (pr1 (pr1 (symmetricFunc_klemono  (pr1 HA)) (pr2 HA)) y)) => [fpy lfpy].
  move : (tarski_lfp _ _ _ (pr1 (pr1 (symmetricFunc_klemono  (pr1 HA)) (pr2 HA)) x)) => [fpx lfpx].
  unfold completeStable.
  set f := fun y : L => (lfp (λ x0 : L, fstOf A (x0,, y)) (pr1 (pr1 (symmetricFunc_klemono (pr1 HA )) (pr2 HA)) y)).    
  change (lfp (λ x : L, fstOf A (x,, y)) (pr1 (pr1 (symmetricFunc_klemono (pr1 HA)) (pr2 HA)) y)) with (f y) in *.  
  change (lfp (λ x0 : L, fstOf A (x0,, x))(pr1 (pr1 (symmetricFunc_klemono (pr1 HA)) (pr2 HA)) x)) with (f x) in *.
  move : (Ay_antimono HA (f x) xy) => Hx.
  rewrite fpx in Hx.
  apply is_lowb; auto .
Qed.


Lemma stable_property {T} {L : complat T} (A : L^2 -> L^2) 
  (HA : approximating A) : klemono (stable HA) × tleantimono (stable HA).
Proof.
  apply symmetricFunc_antimono.
  - inversion HA.
    move => [x y].
    unfold stable, fstOf, sndOf => //=.    
  - exists (completeStable HA); split; auto.
    apply completeStable_antimono; auto.
Qed.

Lemma approximating_stable {T} {L : complat T} (A : L^2 -> L^2) 
  (HA : approximating A)  : approximating (stable HA).
Proof.
  move : (stable_property HA) => [Hk _].
  split; auto.
  unfold isSymmetricFunc.
  move => [x y].
  unfold swap, pr1,pr2.
  unfold stable, fstOf, sndOf, pr1, pr2.
  auto.
Qed.

Lemma stable_of_stable {T} {L : complat T} (A : L^2 -> L^2) 
  (HA : approximating A) :
  stable (approximating_stable HA) = stable HA.
Proof.
  apply  (approximating_tleantimono (approximating_stable HA)).
  move : (stable_property HA ) => [_]; auto.
Qed.

Lemma stablefixpoint_approximationfixpoint {T} {L : complat T} (A : L^2 -> L^2) (HA : approximating A) :
  ∏ p, stable HA p = p -> A p = p.
Proof.
Admitted.


Section semantics.

  Variable T : hSet.
  Variable L : complat T.
  Variable A : L^2 -> L^2.
  Hypotheses HA : approximating A.

  (* stable fixpoint : ≺k fixpoint of approximating operator A *)
  Notation α := (lfp A (pr2 HA)).
  (* well-founded fixpoint : ≺k fixpoint of stable operator C_A *)
  Notation β := (lfp (stable HA )(pr1 (stable_property HA))).
  
  Notation Afp := (pr1 (tarski_lfp _ _ _ (pr2 HA))).
  Notation Alfp := (pr2 (tarski_lfp _ _ _ (pr2 HA))).
  Notation Cfp := (pr1 (tarski_lfp _ _ _ (pr1 (stable_property HA)))).
  Notation Clfp := (pr2 (tarski_lfp _ _ _ (pr1 (stable_property HA)))).

  Lemma alpha_kle_beta :
    @kle _ (L^2) α  β.
  Proof.
    apply Alfp.
    eapply stablefixpoint_approximationfixpoint.
    apply Cfp.
  Qed.

  Lemma bela_kle_stablefp :
    ∏ x, stable HA x = x -> @kle _ (L^2) β x.
  Proof.
    move => x Hx.
    apply Clfp; auto.
  Qed.

  Lemma completebeta_consistentalphe :
    pr1 β = pr2 β -> ∏ x : L^2, stable HA x = x -> consistent x -> β ≺k x -> x ≺k β.
  Proof. 
    move => Hb x Hfp Hc H.
    induction x as [x1 x2].
    induction β as [b1 b2].  
    simpl in *.
    rewrite Hb in H. rewrite Hb.
    rename b2 into b.
    apply prod_dest in H.
    induction H as [H1 H2]; simpl in *.
    rewrite joinC in H2.
    apply meet_join in H2.
    apply two_arg_paths.
    - apply transL with x2; auto.
    - rewrite joinC.
      apply meet_join.
      apply transL with x1; auto.
  Qed.
  


  Lemma consistentstable_consistentbeta :
    consistentFunc (stable HA) -> @consistent _ L β.
  Proof.
    move => H.
    eapply lfpA_consistent.
    Unshelve.
    - exact (completeStable HA).
    - unfold approximates.
      repeat split.
      apply (stable_property HA).
  Qed.

End semantics.

Lemma completFixpointStable_minimal {T} (L : complat T) (A : L^2 -> L^2) (O : L -> L) (HA : approximates A O) :
  ∏ x, stable (pr1 HA,, pr12 HA) (x,,x) = (x,,x) -> 
  ∏ y, O y = y -> y ≺ x -> x ≺ y.
Proof.
  move => x Hx y Hy yx.
  move : (pr22 HA).
  unfold extends => H.
  assert (A (y,,y) = y,, y). {
    rewrite (H y) Hy; auto.      
  }
  assert (@tle _ (L^2) (y,, y)  (x,, x)). {
    simpl. apply two_arg_paths; auto.
  }
  move : (stable_fixpoint_minimal Hx X X0).    
  move /prod_dest; simpl => H0.
  induction H0; auto.
Qed.

Lemma stable_trivial {T} (L : complat T) (O : L -> L) (HO : mono O) :
  ∏ p, stable (applroximating_trivial HO) p = lfp O HO,, lfp O HO.
Proof.
Abort.