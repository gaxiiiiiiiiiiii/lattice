Require Export Bilattice.


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

Definition prodlattice_ {T1 T2} (L1 : lattice T1) (L2 : lattice T2) : bilattice ((T1 × T2)%set) :=
  make_bilattice (prodbilatT L1 L2) (prodbilatK L1 L2).

Definition prodbilatIsInterlaced {T1 T2} (L1 : lattice T1) (L2 : lattice T2) : 
  isInterlaced (prodlattice_ L1 L2).
Proof.
  repeat use tpair.
  all : move => [x1 x2] [y1 y2] /= H.
  all :unfold tmeet, tjoin, kmeet, kjoin => //=.
  all : try ( change (@join _ (prodbilatT L1 L2) (x1,, x2) (y1,, y2)) with (@join _ L1 x1 y1,, @join _ L2 x2 y2 : T1 × T2)).
  all : try change (@join _ (prodbilatK L1 L2) (x1,, x2) (y1,, y2)) with (@join _ L1 x1 y1,, @meet _ L2 x2 y2 : T1 × T2).
  all : try apply two_arg_paths.
  all : try (apply meetI; auto).
  all : try (apply joinI; auto).
Defined.

Definition prodlattice {T1 T2} (L1 : lattice T1) (L2 : lattice T2) : interlaced ((T1 × T2)%set) :=
  prodlattice_ L1 L2,,  prodbilatIsInterlaced L1 L2.

  
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
  all : move => [x1 x2] [y1 y2] /= H.
  all :unfold tmeet, tjoin, kmeet, kjoin => //=.
  all : try ( change (@join _ (prodbilatT L1 L2) (x1,, x2) (y1,, y2)) with (@join _ L1 x1 y1,, @join _ L2 x2 y2 : T1 × T2)).
  all : try change (@join _ (prodbilatK L1 L2) (x1,, x2) (y1,, y2)) with (@join _ L1 x1 y1,, @meet _ L2 x2 y2 : T1 × T2).
  all : try apply two_arg_paths.
  all : try (apply meetI; auto).
  all : try (apply joinI; auto).
Defined.




  



    
   

  
  






  

  