Require Export Bilattice.
From UniMath Require Import MoreFoundations.Univalence.

Lemma prod_dest {A B : UU} {a b : A × B} : a = b -> pr1 a = pr1 b × pr2 a = pr2 b.
Proof.
  destruct a as [a1 a2], b as [b1 b2]; simpl => H.
  inversion H; split; auto.
Qed.


Definition prodbilatT {T1 T2} (L1 : lattice T1) (L2 : lattice T2) : lattice ((T1 × T2)%set).
Proof.
  repeat use tpair.
  - move => [x1 x2] [y1 y2].
    exact (@meet _ L1 x1 y1 ,, @meet _ L2 x2 y2).
  - move => [x1 x2] [y1 y2].
    exact (@join _ L1 x1 y1 ,, @join _ L2 x2 y2).
  all : (simpl => [[x1 x2] [y1 y2]]; try move => [z1 z2]).
  all : apply two_arg_paths.
  all : try apply meetC.
  all : try apply joinC.
  all : try apply meetA.
  all : try apply joinA.
  all : try apply meetjoinK.
  all : try apply joinmeetK.
Defined.

Definition prodbilatK {T1 T2} (L1 : lattice T1) (L2 : lattice T2) : lattice ((T1 × T2)%set).
Proof.
  repeat use tpair.
  - move => [x1 x2] [y1 y2].
    exact (@meet _ L1 x1 y1 ,, @join _ L2 x2 y2).
  - move => [x1 x2] [y1 y2].
    exact (@join _ L1 x1 y1 ,, @meet _ L2 x2 y2).
  all : (simpl => [[x1 x2] [y1 y2]]; try move => [z1 z2]).
  all : apply two_arg_paths.
  all : try apply meetC.
  all : try apply joinC.
  all : try apply meetA.
  all : try apply joinA.
  all : try apply meetjoinK.
  all : try apply joinmeetK.
Defined.


Definition prodbilat {T1 T2} (L1 : lattice T1) (L2 : lattice T2) : interlaced ((T1 × T2)%set).
Proof.
  use tpair.
  { exact (make_bilattice (prodbilatT L1 L2) (prodbilatK L1 L2)). }
  repeat use tpair.
  all : move => [x1 x2] [y1 y2] [z1 z2] /= H.
  all : apply prod_dest in H; induction H as [H1 H2]; simpl in *.
  all :unfold tmeet, tjoin, kmeet, kjoin => //=.  
  all : try change (@join _ (prodbilatK L1 L2) (x1,, x2) (z1,, z2)) with (@join _ L1 x1 z1,, @meet _ L2 x2 z2 : T1 × T2).
  all : try change (@join _ (prodbilatT L1 L2) (x1,, x2) (z1,, z2)) with (@join _ L1 x1 z1,, @join _ L2 x2 z2 : T1 × T2).
  all : try apply two_arg_paths. 
  6 : rewrite joinC; apply meet_join; rewrite joinC in H2;   apply meet_join in H2.
  all : try  (rewrite meetA; rewrite <- (meetA z1);
          rewrite (meetC _ z1); rewrite <- (meetA z1 _);
          rewrite meetI; rewrite (meetC z1 _); rewrite <- meetA, H1; auto).
  all : try  (rewrite meetA; rewrite <- (meetA z2);
          rewrite (meetC _ z2); rewrite <- (meetA z2 _);
          rewrite meetI; rewrite (meetC z2 _); rewrite <- meetA, H2; auto).
  1 : apply meet_join; apply meet_join in H2.
  2 : apply meet_join; apply meet_join in H1.
  3 : apply meet_join; apply meet_join in H1.
  all : try  (rewrite joinA; rewrite <- (joinA z2);
          rewrite (joinC _ z2); rewrite <- (joinA z2 _);
          rewrite joinI; rewrite (joinC z2 _); rewrite <- joinA, H2; auto).
  all : try  (rewrite joinA; rewrite <- (joinA z1);
          rewrite (joinC _ z1); rewrite <- (joinA z1 _);
          rewrite joinI; rewrite (joinC z1 _); rewrite <- joinA, H1; auto).
Defined.        


  
Definition prodcompbilatT {T1 T2} (L1 : complat T1) (L2 : complat T2) : complat (T1 × T2)%set.
Proof.
  use tpair.
  { exact (prodbilatT L1 L2). }
  repeat use tpair.
  - move => X.
    pose l := @sup _ L1 (image_hsubtype X pr1).
    pose r := @sup _ L2 (image_hsubtype X pr2).
    exact (l ,, r).
  - move => X.
    pose l := @inf _ L1 (image_hsubtype X pr1).
    pose r := @inf _ L2 (image_hsubtype X pr2).
    exact (l ,, r).
  all : simpl.
  - move => X [x1 x2]  H.
    apply two_arg_paths;
    apply is_upb;
    unfold image_hsubtype, In;
    move => P; apply; clear P;
    exists (x1,,x2); split => //=.
  - move => X [x1 x2] H.
    apply two_arg_paths;
    apply is_sup => y0;
    unfold image_hsubtype, In; apply => [[[y1 y2] [Hy Xy]]];
    move : (H (y1 ,, y2) Xy) => H0;
    induction H0;
    simpl in Hy;
    rewrite <- Hy;
    apply meet_lowb.
  - move => X [x1 x2] H.
    apply two_arg_paths;
    apply is_lowb => P; apply; clear P;
    exists (x1,,x2); split; auto.
  - move => X [x1 x2] H.
    apply two_arg_paths;
    apply is_inf => y; apply => [[[y1 y2] /= [E Hy]]];
    induction E;
    move : (H (y1,,y2) Hy) => E; inversion E;
    rewrite meetA meetI; auto.
  Defined.


Definition prodcompbilatK {T1 T2} (L1 : complat T1) (L2 : complat T2) : complat (T1 × T2)%set.
Proof.
  use tpair.
  { exact (prodbilatK L1 L2). }
  repeat use tpair.
  - move => X.
    pose l := @sup _ L1 (image_hsubtype X pr1).
    pose r := @inf _ L2 (image_hsubtype X pr2).
    exact (l ,, r).
  - move => X.
    pose l := @inf _ L1 (image_hsubtype X pr1).
    pose r := @sup _ L2 (image_hsubtype X pr2).
    exact (l ,, r).
  all : simpl.
  - move => X [x1 x2]  H.
    apply two_arg_paths.
    - apply is_upb.    
      move => P; apply; clear P.
      exists (x1,,x2); split => //=.
    - rewrite joinC.
      apply  meet_join.
      apply is_lowb.
      move => P; apply; clear P.
      exists (x1,,x2); split => //=.
  - move => X [x1 x2] H.
    apply two_arg_paths.
    - apply is_sup => y0;
      unfold image_hsubtype, In; apply => [[[y1 y2] [Hy Xy]]];
      move : (H (y1 ,, y2) Xy) => H0;
      induction H0;
      simpl in Hy;
      rewrite <- Hy;
      apply meet_lowb.
    - rewrite joinC. apply meet_join. 
      apply is_inf => y; apply => [[[y1 y2] /= [E Hy]]];
      induction E;
      move : (H (y1,,y2) Hy) => E; inversion E.
      rewrite joinC meetjoinK; auto.
  - move => X [x1 x2]  H.
    apply two_arg_paths.
    - apply is_lowb.
      move => P; apply; clear P.
      exists (x1,,x2); split => //=.
    - rewrite joinC. apply meet_join.
      apply is_upb.    
      move => P; apply; clear P.
      exists (x1,,x2); split => //=.    
  - move => X [x1 x2] H.
    apply two_arg_paths.
    - apply is_inf => y; apply => [[[y1 y2] /= [E Hy]]];
      induction E;
      move : (H (y1,,y2) Hy) => E; inversion E;
      rewrite meetA meetI; auto.
    - rewrite joinC. apply meet_join.
      apply is_sup => y; apply => [[[y1 y2] /= [E Hy]]];
      induction E;
      move : (H (y1,,y2) Hy) => E; inversion E.
      rewrite joinC meetjoinK; auto.
  Defined.



Definition prodcompbilat  {T1 T2} (L1 : complat T1) (L2 : complat T2) : interlaced ((T1 × T2)%set).
Proof.
  use tpair.
  { exact (make_compbilat (prodcompbilatT L1 L2) (prodcompbilatK L1 L2)). }  
  repeat use tpair.
  all : move => [x1 x2] [y1 y2] [z1 z2] /= H.
  all : apply prod_dest in H; induction H as [H1 H2]; simpl in *.
  all :unfold tmeet, tjoin, kmeet, kjoin => //=.  
  all : try change (@join _ (prodbilatK L1 L2) (x1,, x2) (z1,, z2)) with (@join _ L1 x1 z1,, @meet _ L2 x2 z2 : T1 × T2).
  all : try change (@join _ (prodbilatT L1 L2) (x1,, x2) (z1,, z2)) with (@join _ L1 x1 z1,, @join _ L2 x2 z2 : T1 × T2).
  all : try apply two_arg_paths. 
  6 : rewrite joinC; apply meet_join; rewrite joinC in H2;   apply meet_join in H2.
  all : try  (rewrite meetA; rewrite <- (meetA z1);
          rewrite (meetC _ z1); rewrite <- (meetA z1 _);
          rewrite meetI; rewrite (meetC z1 _); rewrite <- meetA, H1; auto).
  all : try  (rewrite meetA; rewrite <- (meetA z2);
          rewrite (meetC _ z2); rewrite <- (meetA z2 _);
          rewrite meetI; rewrite (meetC z2 _); rewrite <- meetA, H2; auto).
  1 : apply meet_join; apply meet_join in H2.
  2 : apply meet_join; apply meet_join in H1.
  3 : apply meet_join; apply meet_join in H1.
  all : try  (rewrite joinA; rewrite <- (joinA z2);
          rewrite (joinC _ z2); rewrite <- (joinA z2 _);
          rewrite joinI; rewrite (joinC z2 _); rewrite <- joinA, H2; auto).
  all : try  (rewrite joinA; rewrite <- (joinA z1);
          rewrite (joinC _ z1); rewrite <- (joinA z1 _);
          rewrite joinI; rewrite (joinC z1 _); rewrite <- joinA, H1; auto).
Defined.        


Section prodbilatticeTheory.

  Variable T1 T2 : hSet.
  Variable L1 : lattice T1.
  Variable L2 : lattice T2.
  Definition L := prodbilat L1 L2.

  Lemma pbl_kle (a1 b1 : L1) (a2 b2 : L2) :
    (a1,,a2 : L) ≺k (b1,,b2) <-> a1 ≺ b1 × b2 ≺ a2.
  Proof.
    split =>  /= H.
    - inversion H; split.
      * rewrite meetA meetI; auto.
      * rewrite joinC meetjoinK; auto.
    - induction H.
      apply two_arg_paths; auto.      
      rewrite joinC.
      apply meet_join; auto.
  Qed.

  Lemma pbl_tle (a1 b1 : L1) (a2 b2 : L2) :
    (a1,,a2 : L) ≺t (b1,,b2) <-> a1 ≺ b1 × a2 ≺ b2.
  Proof.
    split =>  /= H.
    - inversion H; split.
      * rewrite meetA meetI; auto.
      * rewrite meetA meetI; auto.
    - induction H.
      apply two_arg_paths; auto.      
  Qed.
  
  Definition lecomp {T} {L : bilattice T} (f g : hrel L) : hrel L :=
    fun x y => ∃ c, f x c ∧ g c y.
  
  
  Lemma pbl_lemeet (a b : L) :
    a ≺k a <∧> b <-> a ≺t a <*> b.
  Proof.
    induction a as [a1 a2].
    induction b as [b1 b2].
    split => /= H; induction H; apply two_arg_paths; auto.
    - rewrite meetjoinK joinmeetK; auto.
    - rewrite meetjoinK joinmeetK; auto.
  Qed.

  Lemma lekmeet_lecomp (a b : L) :
    a ≺k a <∧> b <-> lecomp kle tle a b.
  Proof.
    induction a as [a1 a2].
    induction b as [b1 b2].    
    split => H.
    - apply prod_dest in H.
      induction H as [H1 H2].
      simpl in *.
      move => P; apply; clear P.
      exists ((a1,,a2 : L) <∧> (b1,,b2)).
      split => /=.  
      * apply two_arg_paths; auto.
      * unfold tmeet => //=.
        apply two_arg_paths; auto;
        rewrite meetA meetI; auto.
    - simpl in H; unfold ishinh_UU in H.
      apply H => [[[c1 c2] [H1 H2]]].
      apply prod_dest in H1; induction H1 as [H11 H12].
      apply prod_dest in H2; induction H2 as [H21 H22].
      simpl in *.
      apply two_arg_paths; auto.
      * rewrite <- meetA, meetI.
        eapply transL with c1; auto.
      * rewrite joinmeetK; auto.
  Qed.

  Lemma letmeet_lecomp (a b : L) :
    a ≺t a <*> b <-> lecomp tle kle a b.
  Proof.
    induction a as [a1 a2].
    induction b as [b1 b2].    
    split => H.
    - apply prod_dest in H.
      induction H as [H1 H2].
      simpl in *.
      move => P; apply; clear P.
      exists ((a1,,a2 : L) <*> (b1,,b2)).
      split => /=.  
      * apply two_arg_paths; auto.
      * unfold kmeet => //=.
        apply two_arg_paths; auto.
        + rewrite meetA meetI; auto.
        + rewrite joinA joinI; auto.
    - simpl in H; unfold ishinh_UU in H.
      apply H => [[[c1 c2] [H1 H2]]].
      apply prod_dest in H1; induction H1 as [H11 H12].
      apply prod_dest in H2; induction H2 as [H21 H22].
      simpl in *.
      apply two_arg_paths; auto.
      * rewrite <- meetA, meetI.
        eapply transL with c1; auto.
      * rewrite meetjoinK; auto.
  Defined.

  Lemma pbl_lecompC (a b : L) :
    lecomp kle tle a b <-> lecomp tle kle a b.
  Proof.
    split => H.
    - apply letmeet_lecomp.
      apply pbl_lemeet.
      apply lekmeet_lecomp; auto.
    - apply lekmeet_lecomp.
      apply pbl_lemeet.
      apply letmeet_lecomp; auto.
  Qed.

  Definition kle' (x y : L) := kle y x.

  Notation "x ≻k y" := (kle' x y)(at level 40).
  
  Lemma pbl_lemeet' (a b : L) :
    a <∧> b ≺k a <-> a ≺t a <+> b.
  Proof.
    induction a as [a1 a2].
    induction b as [b1 b2].
    unfold tmeet; simpl.
    split => H; inversion H;
    apply two_arg_paths; auto.
    - apply meetjoinK.
    - rewrite <- H2.
      rewrite (joinC _ a2) (joinC _ a2) joinmeetK meetjoinK; auto.
    - rewrite meetjoinK (meetC _ a1).
      rewrite <- meetA, meetI; auto.
    - rewrite <- (meetA a2 a2 b2), meetI.
      rewrite (meetA a2 b2 b2) meetI joinI; auto.
  Qed.      


  Lemma lekmeet_lecomp' (a b : L) :
    a <∧> b ≺k a <-> lecomp kle' tle a b.
  Proof.
    induction a as [a1 a2].
    induction b as [b1 b2].
    split => H.
    - apply prod_dest in H.
      induction H as [H1 H2].
      simpl in *.
      move => P; apply; clear P.
      exists ((a1,,a2 : L) <∧> (b1,,b2)).
      split.
      * unfold tmeet => /=.  
        apply two_arg_paths; auto.
      * unfold tmeet => /=.  
        apply two_arg_paths; auto;
        rewrite meetA meetI; auto.
    - simpl in H; unfold ishinh_UU in H.
      apply H => [[[c1 c2] [H1 H2]]].
      apply prod_dest in H1; induction H1 as [H11 H12].
      apply prod_dest in H2; induction H2 as [H21 H22].
      simpl in *.
      unfold tmeet; simpl.
      apply two_arg_paths; auto.
      * rewrite meetC. rewrite <- meetA, meetI; auto.
      * rewrite joinC joinmeetK; auto.
        apply pathsinv0.
        apply transL with c2; auto.
        apply meet_join.
        rewrite joinC; auto.
  Qed.

  Lemma letmeet_lecomp' (a b : L) :
    a ≺t a <+> b <-> lecomp tle kle' a b.
  Proof.
    induction a as [a1 a2].
    induction b as [b1 b2].    
    split => H.
    - apply prod_dest in H.
      induction H as [H1 H2].
      simpl in *.
      move => P; apply; clear P.
      exists ((a1,,a2 : L) <+> (b1,,b2)).
      split => /=.  
      * apply two_arg_paths; auto.
      * apply two_arg_paths; auto.
        + rewrite joinC meetjoinK; auto.
        + rewrite meetC joinmeetK; auto.
    - simpl in H; unfold ishinh_UU in H.
      apply H => [[[c1 c2] [H1 H2]]].
      apply prod_dest in H1; induction H1 as [H11 H12].
      apply prod_dest in H2; induction H2 as [H21 H22].
      simpl in *.
      apply two_arg_paths; auto.
      * apply meetjoinK.
      * rewrite <- meetA, meetI.
        eapply transL with c2; auto.
        apply meet_join.
        rewrite joinC; auto.
  Defined.

  Lemma pbl_lecompC' (a b : L) :
    lecomp kle' tle a b <-> lecomp tle kle' a b.
  Proof.
    split => H.
    - apply letmeet_lecomp'.
      apply pbl_lemeet'.
      apply lekmeet_lecomp'; auto.
    - apply lekmeet_lecomp'.
      apply pbl_lemeet'.
      apply letmeet_lecomp'; auto.
  Qed.
  
 

  (* Lemma lecompI (R : hrel L) :
    lecomp cong1 cong1 = cong1.
  Proof.
    apply funextsec => x.
    apply funextsec => y.
    unfold lecomp.
    apply hPropUnivalence.
    - unfold ishinh, ishinh_UU.
      apply => [[c [H1 H2]]].
      unfold cong1, lecomp in H1, H2.
      unfold ishinh, ishinh_UU in H1, H2.
      apply H1 => [[a [xa ac]]].
      apply H2 => [[b [cb by_]]].
      clear H1 H2.
      assert (cong1 a b). {
        unfold cong1.
        apply pbl_lecompC.
        move => P; apply; clear P.
        exists c; split; auto.
      }
      unfold cong1, lecomp, ishinh, ishinh_UU in X.
      apply X => [[d [ad db]]].
      move => P; apply; clear P.
      exists d; split.
      * apply transL with a; auto.
      * apply transL with b; auto.
    - move => H.
      move => P; apply; clear P.
      exists y; split; auto.
      move => P; apply; clear P.
      exists y; split; unfold tle, kle; apply meetI.
  Qed. *)

  Definition cong1 : hrel L := lecomp kle tle.
  
  Lemma istrans_cong1 : 
    istrans cong1.    
  Proof.
    move => x y z xy yz.
    unfold cong1, lecomp in *.
    unfold ishinh, ishinh_UU in xy, yz.
    apply xy => [[a [xa ay]]].
    apply yz => [[b [yb bz]]].
    assert (cong1 a b). {
      apply pbl_lecompC.
      move => P; apply; clear P.
      exists y; split; auto.
    }
    unfold cong1, lecomp, ishinh, ishinh_UU in X.
    apply X => [[c [ac bc]]].
    move => P; apply; clear P.
    exists c; split; eapply transL; eauto.
  Qed.

  Lemma isrefl_cong1 : 
    isrefl cong1.
  Proof.
    move => x.
    unfold cong1, lecomp.
    move => P; apply; clear P.
    exists x; split; apply meetI.
  Qed.

  Definition eq1 : hrel L :=
    fun x y => cong1 x y ∧ cong1 y x.
  
  Lemma iseqrel_eq1 : iseqrel eq1.
  Proof.    
    split; [split|].
    - move => a b c [ab ba] [bc cb].
      split; eapply istrans_cong1; eauto. 
    - move => a; split; apply isrefl_cong1.
    - move => a b [ab ba]; split; auto.
  Qed.

  Definition cong2 : hrel L := lecomp kle' tle.

  Lemma istrans_cong2 : 
    istrans cong2.    
  Proof.
    move => x y z xy yz.
    unfold cong2, lecomp in *.
    unfold ishinh, ishinh_UU in xy, yz.
    apply xy => [[a [xa ay]]].
    apply yz => [[b [yb bz]]].
    assert (cong2 a b). {
      unfold cong2.      
      apply pbl_lecompC'.
      move => P; apply; clear P.
      exists y; split; auto.
    }
    unfold cong2, lecomp, ishinh, ishinh_UU in X.
    apply X => [[c [ac bc]]].
    move => P; apply; clear P.
    exists c; split; eapply transL; eauto.
  Qed.

  Lemma isrefl_cong2 : 
    isrefl cong2.
  Proof.
    move => x.
    unfold cong2, lecomp.
    move => P; apply; clear P.
    exists x; split; apply meetI.
  Qed.

  Definition eq2 : hrel L :=
    fun x y => cong2 x y ∧ cong2 y x.
  
  Lemma iseqrel_eq2 : iseqrel eq2.
  Proof.    
    split; [split|].
    - move => a b c [ab ba] [bc cb].
      split; eapply istrans_cong2; eauto. 
    - move => a; split; apply isrefl_cong2.
    - move => a b [ab ba]; split; auto.
  Qed.
End prodbilatticeTheory.
Check eq1.
Definition isoprodbilat {T : hSet} (L : bilattice T) 

Theorem bilattice_prodbilat {T : hSet} (L : lattice T) :
  ∑ T1 T2, L ≃ 



    


    
    
    
    
    
    

  

    

        

    




  



    
   

  
  






  

  