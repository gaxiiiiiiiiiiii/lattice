From mathcomp Require Export ssreflect.
Require Export Ensembles Image.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Arguments Union {U}.
Arguments Intersection {U}.

(****************************************************)
(* Definition of lattice *)
(****************************************************)

Class lattice := Lattice {
  base : Type;
  meet : base -> base -> base;
  join : base -> base -> base;
  meetC : forall a b, meet a b = meet b a;
  joinC : forall a b, join a b = join b a;
  meetA : forall a b c, meet a (meet b c) = meet (meet a b) c;
  joinA : forall a b c, join a (join b c) = join (join a b) c;
  joinK : forall a b, meet a (join a b) = a;
  meetK : forall a b, join a (meet a b) = a;
  le := fun a b => meet a b = a;
}.

Coercion lattice_type (L : lattice) :=
  let: Lattice T _ _ _ _ _ _ _ _  := L in T.

Infix "≺" := le(at level 40).


Global Notation "[set  x | F ]" := (fun x => F)(at level 30).
Global Notation "x \in X" := (In _ X x)(at level 30) .
Global Notation "{set  T }" := (Ensemble T)(at level 10).

(****************************************************)
(* theorems *)
(****************************************************)

Section theorem.
  Variable L : lattice.

  Lemma refl a :
    a ≺ a.
  Proof.
    unfold le.
    move : (joinK a (meet a a)).
    rewrite meetK; auto.
  Qed.

  Lemma trans a b c :
    a ≺ b -> b ≺ c -> a ≺ c.
  Proof.
    unfold le => ab bc.
    have H : (meet a (meet b c) = a). {
      rewrite bc; auto.
    }
    rewrite meetA in H.
    rewrite ab in H; auto.
  Qed.

  Lemma antisym a b :
    a ≺ b -> b ≺ a -> a = b.
  Proof.
    unfold le => ab ba.
    rewrite <- ba.
    rewrite meetC; auto.
  Qed.

    Lemma meetI a :
    meet a a = a.
  Proof.
    move : (joinK a (meet a a)).
    rewrite meetK; auto.
  Qed.

  Lemma joinI a :
    join a a = a.
  Proof.
    move : (meetK a (join a a)).
    rewrite joinK; auto.
  Qed.

  Lemma lowb' a b :
    meet a b ≺ a /\ meet a b ≺ b.
  Proof.
    split; unfold le.
    - rewrite (meetC (meet a b) a).
      rewrite meetA.
      move : (refl a).
      move => -> //=.
    - rewrite <- meetA.
      move : (refl b).
      move => -> //=.
  Qed.

  Lemma inf' a b :
    forall c, c ≺ a -> c ≺ b -> c ≺ meet a b.
  Proof.
    unfold le => c Ha  Hb.
    rewrite meetA Ha Hb; auto.
  Qed.

  Lemma inf_uni a b c :
    c ≺ a -> c ≺ b -> (forall d, d ≺ a -> d ≺ b -> d ≺ c) -> meet a b = c.
  Proof.
    move => Ha Hb H.
    move : (lowb' a b) => [Ha' Hb'].
    move : (inf' Ha Hb) => H'.
    apply antisym; auto.
  Qed.

  Lemma upb' a b :
    a ≺ join a b /\ b ≺ join a b.
  Proof.
    split; unfold le.
    - apply  (joinK a b).
    - rewrite (joinC a b).
      apply (joinK b a).
  Qed.


  Lemma sup' a b :
    forall c, a ≺ c -> b ≺ c -> join a b ≺ c.
  Proof.
    unfold le => c Ha  Hb.
    move : (meetK c a).
    rewrite (meetC c a).
    rewrite Ha => Ha'.
    move : (meetK c b).
    rewrite (meetC c b).
    rewrite Hb => Hb'.
    have : join (join c a) (join c b) = c. {
      rewrite Ha' Hb' joinI; auto.
    }
    rewrite joinA.
    rewrite <- (joinA c a c).
    rewrite (joinC a c).
    rewrite joinA joinI.
    rewrite <- joinA.
    rewrite (joinC c _).
    move => <-.
    apply joinK.
  Qed.

  Lemma sup_uni a b c :
    a ≺ c -> b ≺ c -> (forall d, a ≺ d -> b ≺ d -> c ≺ d) -> join a b = c.
  Proof.
    move => Ha Hb H.
    move : (upb' a b) => [Ha' Hb'].
    move : (sup' Ha Hb) => H'.
    apply antisym; auto.
  Qed.


End theorem.
