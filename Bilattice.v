Require Export Complat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module bilattice.
  Section ClassDef.

    Record mixin_of T (opst opsk : lattice.ops T ):= Mixin {   
      meett := lattice.meet_ opst;
      joint := lattice.join_ opst;
      let_ := fun a b => meett a b = a;
      meetk := lattice.meet_ opsk;
      joink := lattice.join_ opsk;
      lek := fun a b => meetk a b = a;
      neg : T -> T;
      letN : forall x y, let_ x y -> let_ (neg y) (neg x);
      lekN : forall x y, lek x y -> lek (neg x) (neg y);
      NN : forall x, neg (neg x) = x;
    }.


    Record class_of T (opst opsk : lattice.ops T) := Class {
      baset : complat.class_of opst;
      basek : complat.class_of opsk;
      mixin : mixin_of opst opsk
    }.

    Structure type := Pack {
      sort : Type; 
      opst : lattice.ops sort;  
      opsk : lattice.ops sort;
      _ : class_of opst opsk
    }.

    Variables  (cT : type).
    Definition class := let: Pack _ _ _ c := cT return class_of (opst cT) (opsk cT) in c.    

    Definition complatt := @complat.Pack (sort cT) (opst cT) (baset class).
    Definition latticet := @lattice.Pack (sort cT) (opst cT) (baset class).
    Definition complatk := @complat.Pack (sort cT) (opsk cT) (basek class).
    Definition latticek := @lattice.Pack (sort cT) (opsk cT) (basek class).


    End ClassDef.
  

  Module  Exports.    
    Coercion baset : class_of >-> complat.class_of.
    Coercion mixin : class_of >-> mixin_of.
    Coercion sort : type >-> Sortclass.
    Coercion complatt : type >-> complat.type.
    Coercion latticet : type >-> lattice.type.
    Coercion complatk : type >-> complat.type.
    Coercion latticek : type >-> lattice.type.
    Canonical complatt.
    Canonical latticet.
    Canonical complatk.
    Canonical latticek.
    Notation bilattice := type.
    Notation bilatticeMixin := mixin_of.    

    Definition neg T := neg (class T).
    Definition meetk T := meetk (class T).
    Definition joink T := joink (class T).
    Definition lek T := lek (class T).
    Definition bott {T} := @bot (complatt T).
    Definition topt {T} := @top (complatt T).
    Definition botk {T} := @bot (complatk T).
    Definition topk {T} := @top (complatk T).

    Notation "x <*> y" := (meetk x y)(at level 30).
    Notation "x <+> y" := (joink x y)(at level 30).
    Notation "x ≺_k y" := (lek x y)(at level 40).
    Notation "¬ x" := (neg x)(at level 10).
    Notation TRUE := topt.
    Notation FALSE := bott.
    Notation "⊤" := topk.
    Notation "⊥" := botk.
    
    
    Lemma letN (T : bilattice) : forall (x y : T),  x ≺ y ->   (neg y) ≺ (neg x).
    Proof. apply letN. Qed.
    Lemma lekN (T : bilattice): forall (x y : T),  x ≺_k y -> (neg x) ≺_k (neg y).
    Proof. apply lekN. Qed.    
    Lemma NN (T : bilattice) : forall x : T , neg (neg x) = x.
    Proof. apply NN. Qed.


  End Exports.
End bilattice.

Export bilattice.Exports.

Section bilatticeTheory.

  Variable L : bilattice.


  Lemma neg_TRUE :  
    ¬ TRUE  = (FALSE : L) .
  Proof.
    apply antisym.
    - rewrite <- (NN (FALSE )).
      apply letN.
      unfold TRUE,top.
      apply is_upb.
      constructor.
    - unfold FALSE, bot.
      apply is_lowb.
      constructor.
  Qed.

  Lemma neg_FALSE :  
    ¬ (FALSE :  L) = TRUE.
  Proof.
    apply antisym; first last.
    - rewrite <- (NN (TRUE )).
      apply letN.
      unfold FALSE,bot.
      apply is_lowb.
      constructor.
    - unfold TRUE, top.
      apply is_upb.
      constructor.  
  Qed.

  Lemma neg_and (x y : L) :
    ¬ (x ∧ y) = ¬ x ∨ ¬ y.
  Proof.
    apply antisym.
    - rewrite <- (NN (¬ x ∨ ¬ y)).
      apply letN.
      apply meet_inf.
      * rewrite  <- (NN x). 
        apply letN.
        rewrite NN.
        move : (join_upb (¬ x) (¬ y)); case; auto.
      * rewrite <- (NN y).
        apply letN.
        rewrite NN.
        move : (join_upb (¬ x) (¬ y)); case; auto.
    - move : (meet_lowb x y) => [H1 H2].
      apply join_sup; apply letN; auto.
  Qed.

  Lemma neg_or (x y : L) :
    ¬ (x ∨ y) = ¬ x ∧ ¬ y.
  Proof.
    apply antisym.
    - rewrite <- (NN (¬ x ∧ ¬ y)).
      apply letN.
      rewrite neg_and.
      repeat rewrite NN.
      apply meetI.
    - rewrite <- (NN (¬ x ∧ ¬ y)).
      apply letN.
      rewrite neg_and.
      repeat rewrite NN.
      apply meetI.
  Qed.    

End bilatticeTheory.


Module interlaced.

  Section ClassDef.

    Record mixin_of T (opst opsk : lattice.ops T ):= Mixin {   
      meett := lattice.meet_ opst;
      joint := lattice.join_ opst;
      let_ := fun a b => meett a b = a;
      meetk := lattice.meet_ opsk;
      joink := lattice.join_ opsk;
      lek := fun a b => meetk a b = a;
      monot_meet : forall x y z, let_ x y -> let_ (meetk x z) (meetk y z);
      monot_join : forall x y z, let_ x y -> let_ (joink x z) (joink y z);
      monok_meet : forall x y z, lek x y -> lek (meett x z) (meett y z);
      monok_join : forall x y z, lek x y -> lek (joint x z) (joint y z);
    }.


    Record class_of T (opst opsk : lattice.ops T) := Class {
      baset : tblattice.class_of opst;
      basek : tblattice.class_of opsk;
      mixin : mixin_of opst opsk
    }.

    Structure type := Pack {
      sort : Type; 
      opst : lattice.ops sort;  
      opsk : lattice.ops sort;
      _ : class_of opst opsk
    }.

    Variables  (cT : type).
    Definition class := let: Pack _ _ _ c := cT return class_of (opst cT) (opsk cT) in c.    


    Definition latticet := @lattice.Pack (sort cT) (opst cT) (baset class).
    Definition latticek := @lattice.Pack (sort cT) (opsk cT) (basek class).
    Definition tblatticet := @tblattice.Pack (sort cT) (opst cT) (baset class).
    Definition tblatticek := @tblattice.Pack (sort cT) (opsk cT) (basek class).
  
  End ClassDef.

  Module  Exports.    
    Coercion baset : class_of >-> tblattice.class_of.
    Coercion mixin : class_of >-> mixin_of.
    Coercion sort : type >-> Sortclass.
    Coercion latticet : type >-> lattice.type.
    Coercion tblatticet : type >-> tblattice.type.
    Canonical latticet.
    Canonical tblatticet.
    Canonical latticek.
    Canonical tblatticek.
    Notation interlaced := type.
    Notation interlacedMixin := mixin_of.    

    Definition meetk T := meetk (mixin (class T)).
    Definition joink T := joink (mixin (class T)).
    Definition lek T := lek (class T).
    Definition bott {T} := @tblattice.bot (tblatticet T).
    Definition topt {T} := @tblattice.top (tblatticet T).
    Definition botk {T} := @tblattice.bot (tblatticek T).
    Definition topk {T} := @tblattice.top (tblatticek T).

    Notation "x <*> y" := (meetk x y)(at level 30).
    Notation "x <+> y" := (joink x y)(at level 30).
    Notation "x ≺_k y" := (lek x y)(at level 40).
    Notation TRUE := topt.
    Notation FALSE := bott.
    Notation "⊤" := topk.
    Notation "⊥" := botk.
    
    
    
    Lemma monot_meet (T : interlaced) : forall (x y z : T), x ≺ y -> x <*> z ≺ y <*> z.
    Proof. apply monot_meet. Qed.
    Lemma monot_join (T : interlaced) : forall (x y z : T), x ≺ y -> x <+> z ≺ y <+> z.
    Proof. apply monot_join. Qed.
    Lemma monok_meet (T : interlaced) : forall (x y z : T), x ≺_k y -> x ∧ z ≺_k y ∧ z.
    Proof. apply monok_meet. Qed.
    Lemma monok_join (T : interlaced) : forall (x y z : T), x ≺_k y -> x ∨ z ≺_k y ∨ z.
    Proof. apply monok_join. Qed.

  End Exports.
End interlaced.

Export interlaced.Exports.

Module prodinter.
  Section def.
  
  Variable (L1 L2 : tblattice).

  Definition opst : lattice.ops (L1 * L2) := {|
    lattice.meet_ := fun x y => ((fst x) ∧ (fst y), (snd x) ∨ (snd y));
    lattice.join_ := fun x y => ((fst x) ∨ (fst y), (snd x) ∧ (snd y));
  |}.

  Definition opsk : lattice.ops (L1 * L2) := {|
    lattice.meet_ := fun x y => ((fst x) ∧ (fst y), (snd x) ∧ (snd y));
    lattice.join_ := fun x y => ((fst x) ∨ (fst y), (snd x) ∨ (snd y));
  |}.

  Local Notation meett := (lattice.meet_ opst).
  Local Notation joint := (lattice.join_ opst).
  Local Notation meetk := (lattice.meet_ opsk).
  Local Notation joink := (lattice.join_ opsk).
  Local Notation let_ := (fun a b => meett a b = a).
  Local Notation lek := (fun a b => meetk a b = a).
  Local Notation top1 := (@TOP L1).
  Local Notation bot1 := (@BOT L1).
  Local Notation top2 := (@TOP L2).
  Local Notation bot2 := (@BOT L2).

  Lemma opst_spec (x1 y1 : L1) (x2 y2 : L2) :
    let_ (x1, x2) (y1, y2) <-> x1 ≺ y1 /\ y2 ≺ x2.
  Proof.
    split => [H | [H1 H2]].
    - unfold meett, opst in H.
      inversion_clear H.
      split.
      * move : (meet_lowb x1 y1); case; auto.
      * move : (join_upb x2 y2); case; auto.
    - unfold meett, opst => /=.
      congr pair; auto.
      rewrite joinC.
      apply join_meet; auto.
  Qed.

  Lemma opsk_spec (x1 y1 : L1) (x2 y2 : L2) :
    lek (x1, x2) (y1, y2) <-> x1 ≺ y1 /\ x2 ≺ y2.
  Proof.
    split => [H | [H1 H2]].
    - unfold meett, opsk in H.
      inversion_clear H.
      split.
      * move : (meet_lowb x1 y1); case; auto.
      * move : (meet_lowb x2 y2); case; auto.
    - unfold meett, opsk => /=.
      congr pair; auto.
  Qed.


  Definition type :  interlaced.
  Proof.
    eapply (interlaced.Pack (opst := opst) (opsk := opsk)).
    constructor.
    - split.
      {
        split; intros;
        unfold meett,joint, opst => /=;
        try congr pair.
        - apply meetC.
        - apply joinC.
        - apply joinC.
        - apply meetC.
        - apply meetA.
        - apply joinA.
        - apply joinA.
        - apply meetA.
        - rewrite joinK meetK.
          symmetry.
          apply surjective_pairing.
        - rewrite meetK joinK.
          symmetry.
          apply surjective_pairing.
      }
      {
        eapply (tblattice.Mixin (top := (top1,bot2)) (bot := (bot1,top2)));
        move => [x1 x2];
        unfold meett, opst => /=;
        congr pair.
        * apply topP.
        * rewrite joinC.
          apply join_meet.
          apply botP.
        * apply botP.
        * rewrite joinC.
          apply join_meet.
          apply topP.
      }
    - split.
      {
        split; intros;
        unfold meetk,joink, opsk => /=;
        try congr pair.
        - apply meetC.
        - apply meetC.
        - apply joinC.
        - apply joinC.
        - apply meetA.
        - apply meetA.
        - apply joinA.
        - apply joinA.
        - repeat rewrite joinK.
          symmetry.
          apply surjective_pairing.
        - repeat rewrite meetK.
          symmetry.
          apply surjective_pairing.
      }
      {
        eapply (tblattice.Mixin (top := (top1,top2)) (bot := (bot1,bot2)));
        move => [x1 x2];
        unfold meetk, opsk => /=;
        congr pair.
        * apply topP.
        * apply topP.
        * apply botP.
        * apply botP.      
      }
    - constructor; intros [x X] [y Y] [z Z];
      unfold meett, joint, opst, opsk => <- /=;
      congr pair.
      * rewrite <- (meetA x y z).
        move : (meet_lowb x (y ∧ z)).
        case; auto.
      * rewrite joinC.
        apply join_meet.
        apply meet_inf.
        - apply trans with Y.
          + move : (meet_lowb Y Z); case; auto.
          + move : (join_upb X Y); case; auto.
        - move:  (meet_lowb Y Z); case; auto.
      * apply join_sup.
        - apply trans with y.
          + apply meet_lowb.
          + apply join_upb.
        - apply join_upb.
      * rewrite joinC. apply join_meet. rewrite <- (joinA X Y Z).
        apply join_upb.
      * rewrite <- (meetA x y z).
        apply meet_lowb.
      * apply join_sup.
        - apply trans with Y.
          + apply meet_lowb.
          + apply join_upb.
        - apply join_upb.
      * apply join_sup.
        - apply trans with y.
          + apply meet_lowb.
          + apply join_upb.
        - apply join_upb.
      * rewrite <- (meetA X Y Z).
        apply meet_lowb.
  Defined.

  End def.

  Module Exports.
    Notation prodinter := type.
    Canonical prodinter.
    Notation "L1 ⊙ L2" := (prodinter L1 L2) (at level 40, left associativity).
    Notation let_spec := opst_spec.
    Notation lek_spec := opsk_spec.

    Definition neg (L : tblattice) (p : L ⊙ L) : L ⊙ L :=
      match p with
      | (x,y) => (y,x)
      end.
        
  End Exports.

End prodinter.

Export prodinter.Exports.

Section prodinterTheory.
  Variable (L : tblattice).
  Notation LL := (L ⊙ L).

  Variable (x y z : LL).

  Lemma letN :
    x ≺ y -> (neg y) ≺ (neg x).
  Proof.
    destruct x as [x1 x2], y as [y1 y2].
    move /let_spec => H => /=.
    apply /let_spec; split; apply H.
  Qed.

  Lemma lekN :
    x ≺_k y -> (neg x) ≺_k (neg y).
  Proof.
    destruct x as [x1 x2], y as [y1 y2].
    move /lek_spec => H => /=.
    apply /lek_spec; split; apply H.
  Qed.

  Lemma NN : neg (neg x) = x.
  Proof. destruct x => //=. Qed.

End prodinterTheory.


Module compbilat.
  Section def.
  Variable (L : complat).
  
  Definition LL := L ⊙ L.
  
  Definition neg (x : LL) :=
    match x with
    | (x,y) => (y,x)
    end.

  Local Notation opst := (interlaced.opst  LL).
  Local Notation opsk := (interlaced.opsk  LL).

  Definition fsts {T} {X : {set T * T}} : {set T}:=
    fun x => exists y, (x,y) \in X.
  
  Definition snds {T} {X : {set T * T}} : {set T}:=
    fun y => exists x, (x,y) \in X.

  (*
    inf := ∧ [a, b, ... ,n]
    のようにしたいが、集合を有限集合Ensembleで表現しているので難しい。
    finsetで表現しているなら、bigopを使って表現できそうではある。
    しかしそれだと、kleeneの不動点定理が証明できなくなる。
    インフォーマルには存在は主張できそうだから、axiomとしておく。    
  *)
  Check (inf ).
  Axiom inft : {set LL} -> LL.
  Axiom supt : {set LL } -> LL.
  Axiom is_upbt : forall A a, a \in A -> a ≺ (supt A).
  Axiom is_supt : forall A a, (forall b, b \in A -> b ≺ a) -> (supt A) ≺ a.
  Axiom is_lowbt : forall A a, a \in A -> (inft A) ≺ a.
  Axiom is_inft : forall A a,(forall b, b \in A -> a ≺ b) -> a ≺ (inft A).

  Axiom infk : {set LL} -> LL.
  Axiom supk : {set LL } -> LL.
  Axiom is_upbk : forall A a, a \in A -> a ≺_k (supk A).
  Axiom is_supk : forall A a, (forall b, b \in A -> b ≺_k a) -> (supk A) ≺_k a.
  Axiom is_lowbk : forall A a, a \in A -> (infk A) ≺_k a.
  Axiom is_infk : forall A a,(forall b, b \in A -> a ≺_k b) -> a ≺_k (infk A).
  
  Check bilattice.Pack.
  Definition type : bilattice.
  Proof.
    apply bilattice.Pack with (opst := opst) (opsk := opsk).
    constructor.
    - constructor. 
      * apply (lattice.class (interlaced.latticet LL)) .
      * eapply complat.Mixin with (sup := supt) (inf := inft).
        + apply is_upbt.
        + apply is_supt.
        + apply is_lowbt.
        + apply is_inft.
    -  constructor.
      * apply (lattice.class (interlaced.latticek LL)).
      * eapply complat.Mixin with (sup := supk) (inf := infk).
        + apply is_upbk.
        + apply is_supk.
        + apply is_lowbk.
        + apply is_infk.
    - eapply (bilattice.Mixin (neg := neg)) => 
      [[x1 x2] [y1 y2]|[x1 x2] [y1 y2]| [x1 x2]];
      unfold opst => //=; case => H1 H2;
      congr pair; auto.
      - apply join_meet; auto.
        rewrite joinC; auto.
      - rewrite joinC.
        apply join_meet; auto.
  Defined.  
  End def.
  Module Exports.
    Notation compbilat := type.
    Canonical compbilat.
  End Exports.
End compbilat.

Export compbilat.Exports.




Module distbilattice.
  
  Section ClassDef.

    Record mixin_of T (opst opsk : lattice.ops T) := Mixin {
      meett := lattice.meet_ opst;
      joint := lattice.join_ opst;
      meetk := lattice.meet_ opsk;
      joink := lattice.join_ opsk;

      meett_joint : forall x y z, meett x (joint y z) = joint (meett x y) (meett x z);
      meett_meetk : forall x y z, meett x (meetk y z) = meetk (meett x y) (meett x z);
      meett_joink : forall x y z, meett x (joink y z) = joink (meett x y) (meett x z);

      joint_meett : forall x y z, joint x (meett y z) = meett (joint x y) (joint x z);
      joint_meetk : forall x y z, joint x (meetk y z) = meetk (joint x y) (joint x z);
      joint_joink : forall x y z, joint x (joink y z) = joink (joint x y) (joint x z);

      meetk_meett : forall x y z, meetk x (meett y z) = meett (meetk x y) (meetk x z);
      meetk_joint : forall x y z, meetk x (joint y z) = joint (meetk x y) (meetk x z);
      meetk_joink : forall x y z, meetk x (joink y z) = joink (meetk x y) (meetk x z);

      joink_meett : forall x y z, joink x (meett y z) = meett (joink x y) (joink x z);
      joink_joint : forall x y z, joink x (joint y z) = joint (joink x y) (joink x z);
      joink_meetk : forall x y z, joink x (meetk y z) = meetk (joink x y) (joink x z);
    }.

    Record class_of T (opst opsk : lattice.ops T):= Class {
      base : bilattice.class_of opst opsk;
      mixin : mixin_of opst opsk;
    }.

    Structure type := Pack {
      sort : Type; 
      opst : lattice.ops sort;  
      opsk : lattice.ops sort;
      _ : class_of opst opsk
    }.

    Variables  (cT : type).
    Definition class := let: Pack _ _ _ c := cT return class_of (opst cT) (opsk cT) in c.    

    Definition bilattice := @bilattice.Pack (sort cT) (opst cT) (opsk cT) (base class).
    Definition complatt := @complat.Pack (sort cT) (opst cT) (base class).
    Definition latticet := @lattice.Pack (sort cT) (opst cT) (base class).
    Definition complatk := @complat.Pack (sort cT) (opsk cT) (bilattice.basek (base class)).
    Definition latticek := @lattice.Pack (sort cT) (opsk cT) (bilattice.basek (base class)).
   
  
  End ClassDef.

  Module  Exports.    
    Coercion base : class_of >-> bilattice.class_of.
    Coercion mixin : class_of >-> mixin_of.
    Coercion sort : type >-> Sortclass.
    Coercion bilattice : type >-> bilattice.type.
    Coercion complatt : type >-> complat.type.
    Coercion latticet : type >-> lattice.type.
    Coercion complatk : type >-> complat.type.
    Coercion latticek : type >-> lattice.type.
    Canonical bilattice.
    Canonical complatt.
    Canonical latticet.
    Canonical complatk.
    Canonical latticek.
    Notation distbilat := type.
    Notation distbilatMixin := mixin_of.  


    (* Section interface.
      Variable (T : distbilat).
      Variable (x y z : T).
      Locate "<*>".

        
      Lemma meett_joint : x ∧ (y ∨ z) = (x ∧ y) ∨ (x ∧ z).
      Proof. eapply (meett_joint (class T)). Qed.
      Lemma meett_meetk : x ∧ (y <*> z) = (x ∧ y) <*> (x ∧ z).
      Proof. apply (meett_meetk (class T)). Qed.
      Lemma meett_joink : x ∧ (y <+> z) = (x ∧ y) <+> ( x ∧ z).
      Proof. apply (meett_joink (class T)). Qed.

      Lemma joint_meett :  ∨ (y ∧ z) = (x ∨ y) ∧ (x ∨ z).
      Proof. apply (joint_meett (class T)). Qed.
      Lemma joint_meetk :  ∨ (y <*> z) = (x ∨ y) <*> (x ∨ z).
      Proof. apply (joint_meetk (class T)). Qed.
      Lemma joint_joink :  ∨ (y <+> z) = (x ∨ y) <+> (x ∨ z).
      Proof. apply (joint_joink (class T)). Qed.

      Lemma meetk_meett :  <*> (y ∧ z) = (x <*> y) ∧ (x <*> z).
      Proof. apply (meetk_meett (class T)). Qed.
      Lemma meetk_joint :  <*> (y ∨ z) = (x <*> y) ∨ (x <*> z).
      Proof. apply (meetk_joint (class T)). Qed.
      Lemma meetk_joink :  <*> (y <+> z) = (x <*> y) <+> (x <*> z).
      Proof. apply (meetk_joink (class T)). Qed.

      Lemma joink_meett :  <+> (y ∧ z) = (x <+> y) ∧ (x <+> z).
      Proof. apply (joink_meett (class T)). Qed.
      Lemma joink_joint :  <+> (y ∨ z) = (x <+> y) ∨ (x <+> z).
      Proof. apply (joink_joint (class T)). Qed.
      Lemma joink_meetk :  <+> (y <*> z) = (x <+> y) <*> (x <+> z).
      Proof. apply (joink_meetk (class T)). Qed. *)


  End Exports.











      
  


 
  
      

  

  

    
