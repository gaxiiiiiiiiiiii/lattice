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
    fun A => (sup (fst A), inf (snd A)).
  pose inf_ : {set (T * T')} -> T * T':=
    fun A => (inf (fst A), sup (snd A)).
  eapply (@CompLat (infolat T T')%type sup_ inf_).
  - move => A a Ha; destruct a.
    unfold sup_.
    unfold le, meet, infolat; simpl.
    congr pair.
    - apply is_upb; unfold fst, snd, In.
      exists l0; auto.
    - rewrite joinC.
      apply join_meet.
      apply is_lowb.
      unfold snd, In.
      exists l; auto.
  - move => A [l1 l2] H.
    unfold sup_, le, meet, infolat.
    apply pair_equal_spec; split.
    - apply is_sup.
      unfold fst, In => a [b Hb].
      move : (H (a,b) Hb) => Hab.
      unfold le, meet, infolat in Hab.
      inversion Hab; auto.
      move : (lowb' a l1); case; auto.
    - rewrite joinC.
      apply join_meet.
      apply is_inf.
      unfold snd, In => b [a Ha].      
      move : (H (a,b) Ha) => Hab.
      unfold le,meet,infolat in Hab.
      inversion Hab.
      move : (upb' b l2); case; auto.   
  
  - move => A a Ha; destruct a.
    unfold inf_.
    unfold le, meet, infolat; simpl.
    congr pair.
    - apply is_lowb; unfold fst, snd, In.
      exists l0; auto.
    - rewrite joinC.
      apply join_meet.
      apply is_upb.
      unfold snd, In.
      exists l; auto.
  - move => A [l1 l2] H.
    unfold inf_, le, meet, infolat.
    apply pair_equal_spec; split.
    - apply is_inf.
      unfold fst, In => a [b Hb].
      move : (H (a,b) Hb) => Hab.
      unfold le, meet, infolat in Hab.
      inversion Hab; auto.
      rewrite meetC.
      move : (lowb' a l1); case; auto.
    - rewrite joinC.
      apply join_meet.
      apply is_sup.
      unfold snd, In => b [a Ha].      
      move : (H (a,b) Ha) => Hab.
      unfold le,meet,infolat in Hab.
      inversion Hab.
      rewrite joinC.
      move : (upb' b l2); case; auto.
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



Record bilattice := {
  CL :> complat;
  PCL := prodcomplat CL CL;
  ICL := infocomplat CL CL;
  meett := @meet PCL;
  joint := @join PCL;
  meeti := @meet ICL;
  joini := @join ICL;
  
}.

Print lattice.


Definition ascillating (L : bilattice) (f : L -> L) (p : PCL L) := 
  snd p = f (fst p) /\ fst p = f (snd p).

Definition extreme {L : bilattice} (f : L -> L) (p : L * L):= 
  ascillating L f p /\ 
  (forall p', ascillating L f p' -> @le (ICL L) p p' /\ @le (ICL L) p (snd p, fst p)).


Lemma extreme_unique {L : bilattice} (f : L -> L) :
  forall p q, extreme f p -> extreme f q -> p = q.
Proof.
  move => p q [Hp1 Hp2] [Hq1 Hq2].
  move : (Hp2 q Hq1) => [pq _].
  move : (Hq2 p Hp1) => [qp _].
  apply antisym; auto.
Qed.  


Definition lfp2 {L : bilattice} (f : L -> L) (H : antimono f) :=
  lfp (@antimono_compose_mono L L L f f H H).

Definition gfp2 {L : bilattice} (f : L -> L) (H : antimono f) :=
  gfp (@antimono_compose_mono L L L f f H H).



Lemma fp2_ascillating {L : bilattice} (f : L -> L) (Hf : antimono f) :
  ascillating L f  (lfp2 f Hf, gfp2 f Hf).
Proof.
  split => /=.
  {
    apply antisym.
    - unfold gfp2,gfp.
      apply is_sup => x.
      unfold In => H.
      apply trans with (f (f x)); auto.
      apply Hf.    
      unfold lfp2,lfp.
      apply is_lowb.
      unfold In.
      apply Hf; auto.
    - unfold gfp2,gfp.
      apply is_upb.
      unfold In.
      apply Hf.
      unfold lfp2,lfp.
      apply is_inf => x.
      unfold In => H.
      apply trans with (f (f x)); auto.
      repeat apply Hf.
      apply is_lowb; auto.    
  }
  {
    apply antisym.
    - unfold lfp2,lfp.
      apply is_lowb.
      unfold In.
      apply Hf.
      unfold gfp2, gfp.
      apply is_sup => x.
      unfold In => H.
      apply trans with (f (f x)); auto.
      repeat apply Hf.
      apply is_upb.
      unfold In; auto.
    - unfold lfp2,lfp.
      apply is_inf => x.
      unfold In => H.
      apply trans with (f (f x)); auto.
      apply Hf.
      unfold gfp2,gfp.
      apply is_upb.
      unfold In.
      apply Hf; auto.
  }
Qed.    

Lemma fp2_extreme {L : bilattice} (f : L -> L) (Hf : antimono f) :
  extreme f (lfp2 f Hf, gfp2 f Hf).
Proof.
  split => /=.
  { apply fp2_ascillating. }
  move => [x y]; case => /= y_fx x_fy.
  split.
  - unfold le, meet, infolat.
    apply pair_equal_spec; split.
    * unfold lfp2,lfp.
      apply is_lowb.
      unfold In.
      rewrite y_fx in x_fy.
      rewrite <- x_fy.
      apply meetI.
    * unfold gfp2,gfp.
      rewrite joinC.
      apply join_meet.
      apply is_upb.
      unfold In.
      rewrite x_fy in y_fx.
      rewrite <- y_fx.
      apply meetI.
  - unfold le,meet,infolat.
    apply pair_equal_spec; split.
    * apply is_lowb.
      unfold In.
      move : (tarski_gfp (@antimono_compose_mono L L L f f Hf Hf)) => [H _].
      rewrite H.
      apply meetI.
    * rewrite joinC.
      apply join_meet.
      apply is_upb.
      unfold In.
      move : (tarski_lfp (@antimono_compose_mono L L L f f Hf Hf)) => [H _].
      rewrite H.
      apply meetI.
Qed.

Definition symmetryc {T : Type} (f : T * T -> T * T) :=
  forall p, fst (f p) = snd (f (snd p, fst p)).

Definition fstOfLeft (L : bilattice) (f : ICL L -> ICL L) (x : L) : L -> L :=
  fun y : L => fst (f (x,y)).

Definition fstOfRight (L : bilattice) (f : ICL L -> ICL L) (y : L) : L -> L :=
  fun x : L => fst (f (x,y)).

Lemma bilattice_sym_iff (L : bilattice) (f : ICL L -> ICL L) (Hf : symmetryc f):
   mono f
     <-> 
    ((forall y, @mono L L (fstOfRight L f y)) /\
     (forall x, @antimono L L (fstOfLeft L f x))
    ).
Proof.
  split => H.
  {
    split; unfold fstOfRight.
    - move => y x1 x2 Hx.
      assert (@le (ICL L) (x1,y)  (x2, y)). {
        unfold le,meet, complat_type, ICL, infocomplat, infolat.
        apply pair_equal_spec; split; auto.
        apply joinI.
      }
       assert (@le (ICL L) (y,x2)  (y,x1)) as H9. {
        unfold le,meet, complat_type, ICL, infocomplat, infolat.
        apply pair_equal_spec; split; auto.
        - apply meetI.
        - rewrite joinC.
          apply join_meet; auto. 
      }           
      move : (H (x1,y)  (x2, y) H0) => H1.
      move : (H (y,x2) (y,x1) H9) => H8.
      replace (f (x1,y)) with (snd (f(y,x1)), fst (f(y,x1)))  in H1.
      replace (f (x2,y)) with (snd (f (y,x2)), fst (f (y,x2))) in H1.
      unfold le,meet, infolat, complat_type, ICL, infocomplat, infolat in H1, H0.
      inversion H1.
      rewrite (surjective_pairing (f (y, x1))) in H8.
      unfold le, meet, complat_type, ICL, infocomplat, infolat in H8.
      rewrite <- H3 in H8.
      
      unfold meet, complat_type, CL in H3.
      move : (Hf (x1,y)) => Hf1.
      move : (Hf (y,x1)) => Hf2.
      simpl in *.
      assert (f (x1,y) = (snd (f(y,x1)), fst (f(y,x1)))). {
        rewrite (surjective_pairing (f (x1,y))).
        congr pair; auto.
      }
      eapply trans.

    - move => x y1 y2 => Hy.
      unfold fstOfLeft.
      move : 

  }
  {
   move => [x y] [X Y] xy.
   destruct H as [H1 H2].
   unfold le,meet,complat_type, ICL,infocomplat,infolat in xy.
   inversion xy.
   rewrite H0 H3.
   move : (H1 y x X).
   unfold fstOfRight => H4.
   rewrite joinC in H3.
   apply join_meet in H3.
   move : (H2 X Y y H3).
   unfold fstOfLeft => H5.
   unfold le, meet, complat_type, ICL, infocomplat, infolat.
   
   destruct (f (x,y)).
  }


  
  
  

  


    
    





