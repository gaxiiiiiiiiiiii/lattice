(* based on 'Bilattices are nace things' *)

Require Export Bilattice.
From UniMath Require Import MoreFoundations.Univalence.


Lemma prod_dest {A B : hSet} {a b : A × B} : a = b -> pr1 a = pr1 b × pr2 a = pr2 b.
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
  Notation L := (prodbilat L1 L2).

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
End prodbilatticeTheory.


  
Definition lecomp {T} {L : bilattice T} (f g : hrel L) : hrel L :=
  fun x y => ∃ c, f x c ∧ g c y.

Section bilateq.

  Variable T : hSet.
  Variable L : interlaced T.   
  
  Lemma kletmeet_tlekmeet (a b : L) :
    a ≺k a <∧> b <-> a ≺t a <*> b.
  Proof.
    split => H.
    - simpl in H.
      assert (a <∧> b ≺t b). {
        unfold tmeet. apply (meet_lowb).
      }
      move : (@tle_kmeet_monotone _ L _ _ a X).
      rewrite meetC in H.
      change (meet (a <∧> b) a) with ((a <∧> b) <*> a) in H.
      rewrite H.
      unfold kmeet.
      rewrite (meetC a b); auto.
    - assert (a <*> b ≺k b). {
        unfold kmeet. apply meet_lowb.
      }
      move : (@kle_tmeet_monotone _ L _ _ a X).
      simpl in H. rewrite meetC in H.
      change (meet (a <*> b) a) with ((a <*> b) <∧> a) in H.
      rewrite H.
      unfold tmeet. rewrite meetC; auto.
  Qed.

  Lemma kletmeet_kletle (a b : L) :
    a ≺k a <∧> b -> lecomp kle tle a b.
  Proof.
    move => H P; apply; clear P.
    exists (a <∧> b).
    split; auto.  
    unfold tmeet. apply meet_lowb.
  Qed.

  Lemma kletle_tlekmeet (a b : L) :
    lecomp kle tle a b -> a ≺t a <*> b.
  Proof.
    move => H.
    unfold lecomp, ishinh, ishinh_UU in H.
    apply H => [[c [ac cb]]].
    move : (@tle_kmeet_monotone _ L _ _ a cb).
    simpl in ac. rewrite meetC in ac.
    unfold kmeet.
    rewrite ac (meetC b a); auto.
  Qed.

  Lemma tlekmeet_tlekle (a b : L) :
    a ≺t a <*> b -> lecomp tle kle a b.
  Proof.    
    
    move => H P; apply; clear P.
    exists (a <*> b); split; auto.
    apply meet_lowb.   
  Defined.

  Definition tlekle_kletmeet (a b : L) :
    lecomp tle kle a b -> a ≺k a <∧> b.
  Proof.
    move => H; unfold lecomp, ishinh, ishinh_UU in H.
    apply H => [[c [ac cb]]].
    move : (@kle_tmeet_monotone _ L _ _ a cb).
    unfold tmeet.
    simpl in ac.
    rewrite (meetC c a) ac (meetC b a); auto.
Qed.

  Lemma locomp_inv (a b : L) :
    lecomp kle tle a b <-> lecomp tle kle a b.
  Proof.
    split => H.
    - apply tlekmeet_tlekle.
      apply kletle_tlekmeet; auto.
    - apply kletmeet_kletle.
      apply tlekle_kletmeet; auto.
  Qed.

  Definition kle' (x y : L) := kle y x.

  Notation "x ≻k y" := (kle' x y)(at level 40).
  
  Lemma kletmeet_tlekmeet' (a b : L) :
    a ≻k a <∧> b <-> a ≺t a <+> b.
  Proof.
    split => H.
    - simpl in H.
      apply meet_join in H.
      assert (a <∧> b ≺t b). {
        unfold tmeet. apply (meet_lowb).
      }
      move : (@tle_kjoin_monotone _ L _ _ a X).
      unfold tmeet, kjoin in *.
      rewrite H joinC; auto.
    - assert (b ≺k a <+> b). {
        unfold kmeet. apply join_upb.
      }
      unfold kle'.
      simpl in H.
      move : (@kle_tmeet_monotone _ L _ _ a X).
      rewrite meetC in H.
      unfold tmeet.
      rewrite H meetC; auto.
  Qed.

  Lemma kletmeet_kletle' (a b : L) :
    a ≻k a <∧> b -> lecomp kle' tle a b.
  Proof.
    move => H P; apply; clear P.
    exists (a <∧> b).
    split; auto.  
    unfold tmeet. apply meet_lowb.
  Qed.

  Lemma kletle_tlekmeet' (a b : L) :
    lecomp kle' tle a b -> a ≺t a <+> b.
  Proof.
    move => H.
    unfold lecomp, ishinh, ishinh_UU in H.
    apply H => [[c [ac cb]]].
    simpl in ac.
    apply meet_join in ac.
    change (join c a) with (c <+> a) in ac.
    move : (@tle_kjoin_monotone _ L _ _ a cb).
    rewrite ac.
    unfold kjoin.
    rewrite joinC; auto.
  Qed.

  Lemma tlekmeet_tlekle' (a b : L) :
    a ≺t a <+> b -> lecomp tle kle' a b.
  Proof.        
    move => H P; apply; clear P.
    exists (a <+> b); split; auto.
    apply join_upb.
  Defined.

  Definition tlekle_kletmeet' (a b : L) :
    lecomp tle kle' a b -> a ≻k a <∧> b.
  Proof.
    move => H; unfold lecomp, ishinh, ishinh_UU in H.
    apply H => [[c [ac cb]]].
    move : (@kle_tmeet_monotone _ L _ _ a cb).
    simpl in ac.
    rewrite meetC in ac.
    (* change (meet c a) with (c <∧> a) in ac. *)
    unfold tmeet.
    rewrite ac meetC; auto.
  Qed.

  Lemma locomp_inv' (a b : L) :
    lecomp kle' tle a b <-> lecomp tle kle' a b.
  Proof.
    split => H.
    - apply tlekmeet_tlekle'.
      apply kletle_tlekmeet'; auto.
    - apply kletmeet_kletle'.
      apply tlekle_kletmeet'; auto.
  Qed.

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
      apply locomp_inv.
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

  Definition eq1 : hrel T :=
    fun x y => cong1 x y ∧ cong1 y x.
  
  Lemma iseqrel_eq1 : iseqrel eq1.
  Proof.    
    split; [split|].
    - move => a b c [ab ba] [bc cb].
      split; eapply istrans_cong1; eauto. 
    - move => a; split; apply isrefl_cong1.
    - move => a b [ab ba]; split; auto.
  Qed.

  Definition Eq1 : eqrel T := make_eqrel _ iseqrel_eq1.

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
      apply locomp_inv'.
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

  Definition eq2 : hrel T :=
    fun x y => cong2 x y ∧ cong2 y x.
  
  Lemma iseqrel_eq2 : iseqrel eq2.
  Proof.    
    split; [split|].
    - move => a b c [ab ba] [bc cb].
      split; eapply istrans_cong2; eauto. 
    - move => a; split; apply isrefl_cong2.
    - move => a b [ab ba]; split; auto.
  Qed.

  Definition Eq2 : eqrel T := make_eqrel _ iseqrel_eq2.

End bilateq.

Section bilateqTheory.

  Variable (T : hSet).
  Variable (L : interlaced T).
  Notation R1 := (Eq1 T L).
  Notation R2 := (Eq2 T L).

  Lemma tmeet_kjoin (x y : L) :
    R1 x y -> x <∧> y = x <+> y.
  Proof.

    move => [H1 H2].
    apply kletle_tlekmeet in H1, H2.

    (* move : (@tle_kjoin_monotone _ L _ _ y H1) => H1'.
    unfold kmeet, kjoin in H1'.
    rewrite (joinC (meet x y) y) meetC joinmeetK in H1'.
    change (join x y ≺t y) with ((x <+> y) ≺t y) in H1'.
    move : (@tle_kjoin_monotone _ L _ _ x H2) => H2'.
    unfold kmeet, kjoin in H2'.
    rewrite (joinC (meet y x) x) meetC joinmeetK in H2'.
    change (join y x ≺t x) with ((y <+> x) ≺t x) in H2'.

    assert (x <+> y ≺t x <*> y). {
      apply transL with x; auto.
      unfold kjoin. rewrite joinC. auto.
    }

    simpl in X.
    change ( meet (x <+> y) (x <*> y)) with ((x <+> y) <∧> (x <*> y)) in X.
    clear H1' H2'. *)

    apply kletmeet_tlekmeet in H1, H2.
    move : (@kle_tjoin_monotone _ L _ _ y H1) => H1'.
    unfold tmeet, tjoin in H1'.
    rewrite (joinC (meet x y) y) meetC joinmeetK in H1'.
    change (join x y ≺k y) with ((x <∨> y) ≺k y) in H1'.
    move : (@kle_tjoin_monotone _ L _ _ x H2) => H2'.
    unfold tmeet, tjoin in H2'.
    rewrite (joinC (meet y x) x) meetC joinmeetK in H2'.
    change (join y x ≺k x) with ((y <∨> x) ≺k x) in H2'.

    assert (x <∨> y ≺k x <∧> y). {
      apply transL with x; auto.
      unfold tjoin. rewrite joinC. auto.
    }
    assert (x <*> y ≺k x <∧> y). {
      apply transL with x; auto.
      apply meet_lowb.    
    }
    assert (x <∨> y ≺k x <+> y). {
      apply transL with y; auto.
      apply join_upb.
    }

    (*
          -----------------------------
         |         -----------         |
         |         |         |         |
      x <∨> y ≺ x <*> y ≺ x <+> y ≺ x <∧> y
         |         |         |         |
         ---------------------
                   |                   |
                   ---------------------
    *)
    apply (@antisymL _ (pr21 L)).
    - admit.
    - admit.
Abort.    
  

  Lemma R1_isCongruence (x y a b : L) :
    R1 x y -> R1 a b ->
    R1 (x <∧> a) (y <∧> b) ×
    R1 (x <∨> a) (y <∨> b) ×
    R1 (x <*> a) (y <*> b) ×
    R1 (x <+> a) (y <+> b).
  Proof.
    move => [xy yx] [ab ba].
    apply kletle_tlekmeet in xy, yx, ab, ba.
    split; [|split; [|split]]; split.
    all : apply kletmeet_kletle.
    all : apply kletmeet_tlekmeet.
  Abort.
End bilateqTheory.
