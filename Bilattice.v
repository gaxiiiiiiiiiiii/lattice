Require Export Complat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition bilattice (T : hSet) := lattice T × lattice T.
Definition make_bilattice {T} (L1 L2 : lattice T) : bilattice T := L1 ,, L2.
Coercion bilatticeToSet {T} (_ : bilattice T) := T.

Definition compbilat (T : hSet) := complat T × complat T.
Definition make_compbilat {T} (L1 L2 : complat T) : compbilat T := L1 ,, L2.
Coercion compbilatToPrebilattice {T} (L : compbilat T) : bilattice T := make_bilattice (pr11 L) (pr12 L).

Definition tmeet {T} {L : bilattice T} (x y : L) : L := @meet _ (pr1 L) x y.
Definition tjoin {T} {L : bilattice T} (x y : L) : L := @join _ (pr1 L) x y.
Definition tle {T} {L : bilattice T} (x y : L) := @le _ (pr1 L) x y.
Definition kmeet {T} {L : bilattice T} (x y : L) : L := @meet _ (pr2 L) x y.
Definition kjoin {T} {L : bilattice T} (x y : L) : L := @join _ (pr2 L) x y.
Definition kle {T} {L : bilattice T} (x y : L) := @le _ (pr2 L) x y.

Definition tsup {T} {L : compbilat T} (X : {set : L}) : L := @sup _ (pr1 L) X.
Definition tinf {T} {L : compbilat T} (X : {set : L}) : L := @inf _ (pr1 L) X.
Definition ksup {T} {L : compbilat T} (X : {set : L}) : L := @sup _ (pr2 L) X.
Definition kinf {T} {L : compbilat T} (X : {set : L}) : L := @inf _ (pr2 L) X.

Infix "<∧>" := tmeet(at level 30).
Infix "<∨>" := tjoin(at level 30).
Infix "<*>" := kmeet.
Infix "<+>" := kjoin.
Infix "≺t" := tle(at level 40).
Infix "≺k" := kle(at level 40).

Global Notation "⊓ X" := (tinf X)(at level 30).
Global Notation "⊔ X" := (tsup X)(at level 30).
Global Notation Π  := kinf.
Global Notation Σ := ksup.


Section bilatProperties.
  
  Variable X : hSet.
  Variable L : bilattice X.

  Definition tmeetC : iscomm tmeet := pr11 (pr221 L).
  Definition tjoinC : iscomm tjoin := pr21 (pr221 L).
  Definition tmeetA : isassoc tmeet := pr112 (pr221 L).
  Definition tjoinA : isassoc tjoin := pr212 (pr221 L).
  Definition tmeetkjoinK : isabsorb tmeet tjoin := pr122 (pr221 L).
  Definition tjoinkmeetK : isabsorb tjoin tmeet := pr222 (pr221 L).

  Definition kmeetC : iscomm kmeet := pr11 (pr222 L).
  Definition kjoinC : iscomm kjoin := pr21 (pr222 L).
  Definition kmeetA : isassoc kmeet := pr112 (pr222 L).
  Definition kjoinA : isassoc kjoin := pr212 (pr222 L).
  Definition kmeetkjoinK : isabsorb kmeet kjoin := pr122 (pr222 L).
  Definition kjoinkmeetK : isabsorb kjoin kmeet := pr222 (pr222 L).

End bilatProperties.

(* access to complat properties from compbilat *)
Section compbilatProperties.
  
  Variable X : hSet.
  Variable L : compbilat X.
  
  Definition tis_upb :
    ∏ A a, a ∈ A -> a ≺t tsup A := @is_upb _ (pr1 L).
  Definition tis_sup :
    ∏ A a, (∏ b, b ∈ A -> b ≺t a) -> tsup A ≺t a := @is_sup _ (pr1 L).
  Definition tis_lowb :
    ∏ A a, a ∈ A -> tinf A ≺t a := @is_lowb _ (pr1 L).
  Definition tis_inf :
    ∏ A a, (∏ b, b ∈ A -> a ≺t b) -> a ≺t tinf A := @is_inf _ (pr1 L).
  Definition kis_upb :
    ∏ A a, a ∈ A -> a ≺k ksup A := @is_upb _ (pr2 L).
  Definition kis_sup :
    ∏ A a, (∏ b, b ∈ A -> b ≺k a) -> ksup A ≺k a := @is_sup _ (pr2 L).
  Definition kis_lowb :
    ∏ A a, a ∈ A -> kinf A ≺k a := @is_lowb _ (pr2 L).
  Definition kis_inf :
    ∏ A a, (∏ b, b ∈ A -> a ≺k b) -> a ≺k kinf A := @is_inf _ (pr2 L).
  
End compbilatProperties.

(*  8 monotonic conditions, operators [kmeet,kjoin,tmeet,tjon] are monotone with respect to both of [tle,kle].*)
Definition isInterlaced {T} (L : bilattice T) :=  
  (∏ (x y z : L), x ≺t y -> (x <*> z) ≺t (x <*> z)) ×
  (∏ (x y z : L), x ≺t y -> (x <+> z) ≺t (x <+> z)) ×
  (∏ (x y z : L), x ≺k y -> (x <∧> z) ≺k (x <∧> z)) ×
  (∏ (x y z : L), x ≺k y -> (x <∨> z) ≺k (x <∨> z)).

Definition interlaced T := ∑ L : bilattice T, isInterlaced L.
Coercion interlacedToBilattice {T} (L : interlaced T) : bilattice T := pr1 L.

(* access to interlaced properties *)
Section interlacedProperties.
  
  Variable X : hSet.
  Variable L : interlaced X.

  Definition kmeetMonotonet : ∏ x y z, x ≺t y -> (x <*> z) ≺t (x <*> z) := pr1 (pr2 L).
  Definition kjoinMonotonet : ∏ x y z, x ≺t y -> (x <+> z) ≺t (x <+> z) := pr12 (pr2 L).
  Definition tmeetMonotonek : ∏ x y z, x ≺k y -> (x <∧> z) ≺k (x <∧> z) := pr122 (pr2 L).
  Definition tjoinMonotonek : ∏ x y z, x ≺k y -> (x <∨> z) ≺k (x <∨> z) := pr222 (pr2 L).
    
End interlacedProperties.

(* 12 bidistr laws connecting [<∧>, <∨>, <*>, <+>] *)
Definition isBidistr {T} (L : bilattice T) :=
  (∏ (x y z : L), x <∧> (y <∨> z) = (x <∧> y) <∨> (x <∧> z)) ×
  (∏ (x y z : L), x <∨> (y <∧> z) = (x <∨> y) <∧> (x <∨> z)) ×
  (∏ (x y z : L), x <*> (y <+> z) = (x <*> y) <+> (x <*> z)) ×
  (∏ (x y z : L), x <+> (y <*> z) = (x <+> y) <*> (x <+> z)) ×

  (∏ (x y z : L), x <∧> (y <*> z) = (x <∧> y) <*> (x <∧> z)) ×
  (∏ (x y z : L), x <∧> (y <+> z) = (x <∧> y) <+> (x <∧> z)) ×
  (∏ (x y z : L), x <∨> (y <*> z) = (x <∨> y) <*> (x <∨> z)) ×
  (∏ (x y z : L), x <∨> (y <+> z) = (x <∨> y) <+> (x <∨> z)) ×

  (∏ (x y z : L), x <+> (y <∧> z) = (x <+> y) <∧> (x <+> z)) ×
  (∏ (x y z : L), x <+> (y <∨> z) = (x <+> y) <∨> (x <+> z)) ×
  (∏ (x y z : L), x <*> (y <∧> z) = (x <*> y) <∧> (x <*> z)) ×
  (∏ (x y z : L), x <*> (y <∨> z) = (x <*> y) <∨> (x <*> z)).
Definition bidistr T := ∑ L : bilattice T, isBidistr L.
Coercion bidistrToBilattice {T} (L : bidistr T) : bilattice T := pr1 L.

(* access to bidistr properties *)
Section bidistrProperties.
  
  Variable X : hSet.
  Variable L : bidistr X.
  
  Definition tmeet_tjoin : 
    ∏ x y z, x <∧> (y <∨> z) = (x <∧> y) <∨> (x <∧> z) := pr1 (pr2 L).
  Definition tjoin_tmeet : 
    ∏ x y z, x <∨> (y <∧> z) = (x <∨> y) <∧> (x <∨> z) := pr12 (pr2 L).
  Definition kmeet_kjoin : 
    ∏ x y z, x <*> (y <+> z) = (x <*> y) <+> (x <*> z) := pr122 (pr2 L).
  Definition kjoin_kmeet : 
    ∏ x y z, x <+> (y <*> z) = (x <+> y) <*> (x <+> z) := pr1 (pr222 (pr2 L)).
  Definition tmeet_kmeet : 
    ∏ x y z, x <∧> (y <*> z) = (x <∧> y) <*> (x <∧> z) := pr12 (pr222 (pr2 L)).
  Definition tmeet_kjoin : 
    ∏ x y z, x <∧> (y <+> z) = (x <∧> y) <+> (x <∧> z) := pr122 (pr222 (pr2 L)).
  Definition tjoin_kmeet : 
    ∏ x y z, x <∨> (y <*> z) = (x <∨> y) <*> (x <∨> z) := pr1 (pr222 (pr222 (pr2 L))).
  Definition tjoin_kjoin : 
    ∏ x y z, x <∨> (y <+> z) = (x <∨> y) <+> (x <∨> z) := pr12 (pr222 (pr222 (pr2 L))).
  Definition kjoin_tmeet :
    ∏ x y z, x <+> (y <∧> z) = (x <+> y) <∧> (x <+> z) := pr122 (pr222 (pr222 (pr2 L))).
  Definition kjoin_tjoin :
    ∏ x y z, x <+> (y <∨> z) = (x <+> y) <∨> (x <+> z) := pr1 (pr222 (pr222 (pr222 (pr2 L)))).
  Definition kmeet_tmeet :
    ∏ x y z, x <*> (y <∧> z) = (x <*> y) <∧> (x <*> z) := pr12 (pr222 (pr222 (pr222 (pr2 L)))).
  Definition kmeet_tjoin :
    ∏ x y z, x <*> (y <∨> z) = (x <*> y) <∨> (x <*> z) := pr22 (pr222 (pr222 (pr222 (pr2 L)))).

End bidistrProperties.


(* the lows of distribution [<∧>, <∨>, <*>, <+>] over [⊓, ⊔, Σ, Π]. *)
Definition isCompdistr {T} (L : compbilat T) :=
  (∏ (x : L)(Y : {set : L}), x <∧> (⊓ Y) = ⊓ (image_hsubtype Y (fun y => x <∧> y))) ×
  (∏ (x : L)(Y : {set : L}), x <∧> (⊔ Y) = ⊔ (image_hsubtype Y (fun y => x <∧> y))) ×
  (∏ (x : L)(Y : {set : L}), x <∧> (Π Y) = Π (image_hsubtype Y (fun y => x <∧> y))) ×
  (∏ (x : L)(Y : {set : L}), x <∧> (Σ Y) = Σ (image_hsubtype Y (fun y => x <∧> y))) ×

  (∏ (x : L)(Y : {set : L}), x <∨> (⊓ Y) = ⊓ (image_hsubtype Y (fun y => x <∨> y))) ×
  (∏ (x : L)(Y : {set : L}), x <∨> (⊔ Y) = ⊔ (image_hsubtype Y (fun y => x <∨> y))) ×
  (∏ (x : L)(Y : {set : L}), x <∨> (Π Y) = Π (image_hsubtype Y (fun y => x <∨> y))) ×
  (∏ (x : L)(Y : {set : L}), x <∨> (Σ Y) = Σ (image_hsubtype Y (fun y => x <∨> y))) ×

  (∏ (x : L)(Y : {set : L}), x <*> (⊓ Y) = ⊓ (image_hsubtype Y (fun y => x <*> y))) ×
  (∏ (x : L)(Y : {set : L}), x <*> (⊔ Y) = ⊔ (image_hsubtype Y (fun y => x <*> y))) ×
  (∏ (x : L)(Y : {set : L}), x <*> (Π Y) = Π (image_hsubtype Y (fun y => x <*> y))) ×
  (∏ (x : L)(Y : {set : L}), x <*> (Σ Y) = Σ (image_hsubtype Y (fun y => x <*> y))) ×

  (∏ (x : L)(Y : {set : L}), x <+> (⊓ Y) = ⊓ (image_hsubtype Y (fun y => x <+> y))) ×
  (∏ (x : L)(Y : {set : L}), x <+> (⊔ Y) = ⊔ (image_hsubtype Y (fun y => x <+> y))) ×
  (∏ (x : L)(Y : {set : L}), x <+> (Π Y) = Π (image_hsubtype Y (fun y => x <+> y))) ×
  (∏ (x : L)(Y : {set : L}), x <+> (Σ Y) = Σ (image_hsubtype Y (fun y => x <+> y))).


Definition compditr T := ∑ L : compbilat T, isBidistr L × isCompdistr L.
Coercion compditrToCompbilat {T} (L : compditr T) : compbilat T := pr1 L.

(* access to compdistr properties *)

Section compdistrProperties.

  Variable T : hSet.
  Variable L : compditr T.
  

  Definition tmeet_tinf :
    (∏ (x : L)(Y : {set : L}), x <∧> (⊓ Y) = ⊓(image_hsubtype Y (fun y => x <∧> y))) :=
    pr1 (pr22 L).
  Definition tmmet_tsup :
    (∏ (x : L)(Y : {set : L}), x <∧> (⊔ Y) = ⊔(image_hsubtype Y (fun y => x <∧> y))) :=
    pr12 (pr22 L).
  Definition tmeet_kinf :
    (∏ (x : L)(Y : {set : L}), x <∧> (Π Y) = Π (image_hsubtype Y (fun y => x <∧> y))) :=
    pr122 (pr22 L).
  Definition tmeet_ksup :
    (∏ (x : L)(Y : {set : L}), x <∧> (Σ Y) = Σ (image_hsubtype Y (fun y => x <∧> y))) :=
    pr1 (pr222 (pr22 L)).
  
  Definition tjoin_tinf :
    (∏ (x : L)(Y : {set : L}), x <∨> (⊓ Y) = ⊓(image_hsubtype Y (fun y => x <∨> y))) :=
    pr12 (pr222 (pr22 L)).
  Definition tjoin_tsup :
    (∏ (x : L)(Y : {set : L}), x <∨> (⊔ Y) = ⊔(image_hsubtype Y (fun y => x <∨> y))) :=
    pr122 (pr222 (pr22 L)).
  Definition tjoin_kinf :
    (∏ (x : L)(Y : {set : L}), x <∨> (Π Y) = Π (image_hsubtype Y (fun y => x <∨> y))) :=
    pr1 (pr222 (pr222 (pr22 L))).
  Definition tjoin_ksup :
    (∏ (x : L)(Y : {set : L}), x <∨> (Σ Y) = Σ (image_hsubtype Y (fun y => x <∨> y))) :=
    pr12 (pr222 (pr222 (pr22 L))).
  
  Definition kmeet_tinf :
    (∏ (x : L)(Y : {set : L}), x <*> (⊓ Y) = ⊓(image_hsubtype Y (fun y => x <*> y))) :=
    pr122 (pr222 (pr222 (pr22 L))).
  Definition kmeet_tsup :
    (∏ (x : L)(Y : {set : L}), x <*> (⊔ Y) = ⊔(image_hsubtype Y (fun y => x <*> y))) :=
    pr1 (pr222 (pr222 (pr222 (pr22 L)))).
  Definition kmeet_kinf :
    (∏ (x : L)(Y : {set : L}), x <*> (Π Y) = Π (image_hsubtype Y (fun y => x <*> y))) :=
    pr12 (pr222 (pr222 (pr222 (pr22 L)))).
  Definition kmeet_ksup :
    (∏ (x : L)(Y : {set : L}), x <*> (Σ Y) = Σ (image_hsubtype Y (fun y => x <*> y))) :=
    pr122 (pr222 (pr222 (pr222 (pr22 L)))).
  
  Definition kjoin_tinf :
    (∏ (x : L)(Y : {set : L}), x <+> (⊓ Y) = ⊓(image_hsubtype Y (fun y => x <+> y))) :=
    pr1 (pr222 (pr222 (pr222 (pr222 (pr22 L))))).
  Definition kjoin_tsup :
    (∏ (x : L)(Y : {set : L}), x <+> (⊔ Y) = ⊔(image_hsubtype Y (fun y => x <+> y))) :=
    pr12 (pr222 (pr222 (pr222 (pr222 (pr22 L))))).
  Definition kjoin_kinf :
    (∏ (x : L)(Y : {set : L}), x <+> (Π Y) = Π (image_hsubtype Y (fun y => x <+> y))) :=
    pr122 (pr222 (pr222 (pr222 (pr222 (pr22 L))))).
  Definition kjoin_ksup :
    (∏ (x : L)(Y : {set : L}), x <+> (Σ Y) = Σ (image_hsubtype Y (fun y => x <+> y))) :=
    pr222 (pr222 (pr222 (pr222 (pr222 (pr22 L))))).
  
End compdistrProperties.


Definition isNegation {T} {L : bilattice T} (bneg : L -> L) :=
  (∏ x y, x ≺t y -> bneg y ≺t bneg x) ×
  (∏ x y, x ≺k y -> bneg x ≺k bneg y) ×
  (∏ x, bneg (bneg x) = x).

Definition isConflation {T} {L : bilattice T} (confl : L -> L ) :=
  (∏ x y, x ≺t y -> confl x ≺t confl y) ×
  (∏ x y, x ≺k y -> confl y ≺k confl x) ×
  (∏ x, confl (confl x) =  x).

Definition isNagConfl {T} {L : bilattice T} (bneg confl : L -> L) :=
  isNegation bneg × isConflation confl × (∏ x, confl (bneg x) = bneg (confl x)).