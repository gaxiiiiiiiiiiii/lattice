Require Export ProdBilattice.

Print mono.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

 
Notation "L ^2" := (prodcompbilat L L)(at level 10).

Definition consistent {T}{L : complat T}(p : L^2) := @meet _  L (pr1 p) (pr2 p).

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



Definition fstOf {T} {L : complat T} (f: L^2 -> L^2) : L^2 -> L := fun p => @pr1 L (fun _ => L) (f p).
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





