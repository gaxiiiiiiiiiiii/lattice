Require Export CompLat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Instance powlat (T : Type): lattice.
Proof.
  eapply (@Lattice
    ( (Ensemble T))
    Intersection
    Union
    (Intersection_commutative _)
    (Union_commutative _)
  ); intros.
  - apply Extensionality_Ensembles; split => x;
      inversion 1; subst.
      inversion H1; subst; repeat constructor; auto.
      inversion H0; subst; repeat constructor; auto.
  - rewrite Union_associative; auto.
  - apply Extensionality_Ensembles; split => x.
    inversion 1; subst; auto.
    move => Ha; repeat constructor; auto.
  - apply Extensionality_Ensembles; split => x.
    inversion 1; subst; auto.
    inversion H0; auto.
    move => Ha; constructor; auto.
Defined.

Canonical  powlat.

Lemma le_subset {T : Type} (A B : powlat T) :
  A ≺ B <-> Included _ A B.
Proof.
  unfold le, meet, powlat.
  split.
  - move => <- x.
    inversion 1; auto.
  - move => H.
    apply Extensionality_Ensembles; split => x.
    inversion 1; auto.
    move => Hx; constructor; auto.
Qed.


Global Instance powcomplat (T : Type) : complat.
Proof.
  pose L := powlat T.
  pose sup_ := fun A : {set L} => bigcup A.
  pose inf_ := fun A : {set L} => bigcap A.
  eapply (@CompLat L sup_ inf_).
  - move => A a Ha.
    apply le_subset => i Hi.
    unfold sup_.
    exists a; auto.
  - move => A a H.
    apply le_subset => x [i [Ai xi]].
    move /H : Ai.
    move /le_subset; apply; auto.
  - move => A a Ha.
    apply le_subset => i; auto.
  - move => A a H.
    apply le_subset => x xa i iA.
    move /H : iA.
    move /le_subset; apply; auto.
Defined.

Canonical powcomplat.