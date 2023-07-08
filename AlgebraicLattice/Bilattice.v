Require Export CompLat.

(****************************************************)
(* Instanzation of prod lattice *)
(****************************************************)

Instance prodlat (T T': lattice)  : lattice.
Proof.
  pose meet_ := fun (X1 X2 : T * T') => match X1, X2 with
    | (x1,y1), (x2,y2) => ((meet x1 x2), (meet y1 y2))
    end.
  pose join_ := fun (X1 X2 : T * T') => match X1, X2 with
    | (x1,y1), (x2,y2) => ((join x1 x2), (join y1 y2))
    end.
  eapply (Lattice (meet := meet_) (join := join_));
  intros; destruct a, b; try destruct c ; simpl; auto.
  - rewrite (meetC l1 l) (meetC l0 l2); auto.
  - rewrite (joinC l1 l) (joinC l0 l2); auto.
  - rewrite (meetA l l1 l3) (meetA l0 l2 l4); auto.
  - rewrite (joinA l l1 l3) (joinA l0 l2 l4); auto.
  - rewrite (joinK l l1) (joinK l0 l2); auto.
  - rewrite (meetK l l1) (meetK l0 l2); auto.
Defined.

Instance prodcomplat (T T': complat)  : complat.
Proof.
  pose fst  : {set (T * T')} -> {set T} :=
    fun X => [set x1 | exists x2, (x1,x2) \in X].
  pose snd : {set (T * T')} -> {set T'} :=
    fun X => [set x2 | exists x1, (x1,x2) \in X].
  pose sup_ : {set (T * T')} -> T * T':=
    fun A => (sup (fst A), sup (snd A)).
  pose inf_ : {set (T * T')} -> T * T':=
    fun A => (inf (fst A), inf (snd A)).
  eapply (@CompLat (prodlat T T')%type sup_ inf_).
  - move => A a Ha; destruct a.
    unfold le, meet, prodlat; simpl.
    congr pair; apply is_upb;
    unfold fst, snd, In.
    - exists l0; auto.
    - exists l; auto.
  - move => A [l1 l2] H.
    unfold sup_, le, meet, prodlat.
    suff : (sup (fst A) ≺ l1) /\ sup (snd A) ≺ l2. {
      case => -> ->; auto.
    }
    split; apply is_sup => a;
    unfold fst, snd, In => [[b ab]];
    apply H in ab; inversion ab; auto.
    - rewrite H1; unfold le; auto.
    - rewrite H2; unfold le; auto.
  - move => A [l1 l2] Ha.
    unfold inf_.
    congr pair; apply is_lowb; unfold fst, snd, In.
    - exists l2; auto.
    - exists l1; auto.
  - move => A [l1 l2] H.
    unfold inf_.
    congr pair; apply is_inf; unfold fst, snd, In;
    move => a [b ab]; apply H in ab; inversion ab.
    - rewrite H1; unfold le; auto.
    - rewrite H2; unfold le; auto.
Defined.

Canonical prodlat.
Canonical prodcomplat.


Instance infolat (T T': lattice)  : lattice.
Proof.
  pose meet_ := fun (X1 X2 : T * T') => match X1, X2 with
    | (x1,y1), (x2,y2) => ((meet x1 x2), (join y1 y2))
    end.
  pose join_ := fun (X1 X2 : T * T') => match X1, X2 with
    | (x1,y1), (x2,y2) => ((join x1 x2), (meet y1 y2))
    end.
  eapply (Lattice (meet := meet_) (join := join_));
  intros; destruct a, b; try destruct c ; simpl; auto.
  - rewrite (meetC l1 l) (joinC l0 l2); auto.
  - rewrite (joinC l1 l) (meetC l0 l2); auto.
  - rewrite (meetA l l1 l3) (joinA l0 l2 l4); auto.
  - rewrite (joinA l l1 l3) (meetA l0 l2 l4); auto.
  - rewrite (joinK l l1) (meetK l0 l2); auto.
  - rewrite (meetK l l1) (joinK l0 l2); auto.
Defined.

Instance infocomplat (T T': complat)  : complat.
Proof.
  pose fst  : {set (T * T')} -> {set T} :=
    fun X => [set x1 | exists x2, (x1,x2) \in X].
  pose snd : {set (T * T')} -> {set T'} :=
    fun X => [set x2 | exists x1, (x1,x2) \in X].
  pose sup_ : {set (T * T')} -> T * T':=
    fun A => (sup (fst A), sup (snd A)).
  pose inf_ : {set (T * T')} -> T * T':=
    fun A => (inf (fst A), inf (snd A)).
  eapply (@CompLat (prodlat T T')%type sup_ inf_).
  - move => A a Ha; destruct a.
    unfold le, meet, prodlat; simpl.
    congr pair;
    apply is_upb; unfold fst, snd, In.
    - exists l0; auto.
    - exists l; auto.
  - move => A [l1 l2] H.
    unfold sup_, le, meet, prodlat.
    suff : (sup (fst A) ≺ l1) /\ sup (snd A) ≺ l2. {
      case => -> ->; auto.
    }
    split; apply is_sup => a;
    unfold fst, snd, In => [[b ab]];
    apply H in ab; inversion ab; auto.
    - rewrite H1; unfold le; auto.
    - rewrite H2; unfold le; auto.
  - move => A [l1 l2] Ha.
    unfold inf_.
    congr pair; apply is_lowb; unfold fst, snd, In.
    - exists l2; auto.
    - exists l1; auto.
  - move => A [l1 l2] H.
    unfold inf_.
    congr pair; apply is_inf; unfold fst, snd, In;
    move => a [b ab]; apply H in ab; inversion ab.
    - rewrite H1; unfold le; auto.
    - rewrite H2; unfold le; auto.
Defined.






Goal forall (T : lattice), let TT := infolat T T in
  forall (p p' : TT), @le TT p p' <-> (fst p ≺ fst p' /\ snd p' ≺ snd p).
Proof.
  move => T TT [x y] [x' y'] => /=; split => H.  
  - unfold le, meet, TT, infolat in H.
    inversion_clear H; split.
    - move : (lowb' x x'); case ; auto.
    - move : (upb' y y'); case; auto.
  - unfold le, meet, TT, infolat.
    inversion_clear H.
    apply pair_equal_spec; split; auto.
    unfold le in H1.
    rewrite <- H1.
    rewrite meetC.
    rewrite meetK; auto.
Qed.    
    
    





