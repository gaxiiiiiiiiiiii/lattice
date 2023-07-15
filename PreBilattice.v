Require Export Complat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module latticek.
  Section ClassDef.

    Record mixin_of T (ops : lattice.ops T) := Mixin {   
      meetk := lattice.meet_ ops;
      joink := lattice.join_ ops;
      meetCk : forall a b, meetk a b = meetk b a;
      joinCk : forall a b, joink a b = joink b a;
      meetAk : forall a b c, meetk a (meetk b c) = meetk (meetk a b) c;
      joinAk : forall a b c, joink a (joink b c) = joink (joink a b) c;
      joinKk : forall a b, meetk a (joink a b) = a;
      meetKk : forall a b, joink a (meetk a b) = a;            
    }.
  
    Record class_of T (ops : lattice.ops T) := Class {
      base  : lattice.class_of ops;
      mixin : mixin_of ops
    }.

    Structure type := Pack { sort; ops : lattice.ops sort; _ : class_of ops }.

    Variable (cT : type).
    Definition class := let: Pack _ _ c := cT return class_of (ops cT) in c.
    
    Definition lattice := lattice.Pack (base class).

  End ClassDef.

  Module Exports.
    Coercion base : class_of >-> lattice.class_of.
    Coercion mixin : class_of >-> mixin_of.
    Coercion sort : type >-> Sortclass.
    Coercion ops : type >-> lattice.ops.
    Canonical Structure lattice.
    Notation latticek := type.
    Notation LatticekMixin := mixin_of.

  End Exports.
End latticek.

Export latticek.Exports.

Variable L : latticek.

Goal forall a : L, a ∧ a = a.
  rewrite <- (@meetI (latticek.lattice L)).



Module PreBilattice.

  Section ClassDef.

    Record mixin_of T (opst opsk : lattice.ops T) := Mixin {   
      meett := lattice.meet_ opst;
      joint := lattice.join_ opst;
      meetCt : forall a b, meett a b = meett b a;
      joinCt : forall a b, joint a b = joint b a;
      meetAt : forall a b c, meett a (meett b c) = meett (meett a b) c;
      joinAt : forall a b c, joint a (joint b c) = joint (joint a b) c;
      joinKt : forall a b, meett a (joint a b) = a;
      meetKt : forall a b, joint a (meett a b) = a;
        
      meetk := lattice.meet_ opsk;
      joink := lattice.join_ opsk;
      meetCk : forall a b, meetk a b = meetk b a;
      joinCk : forall a b, joink a b = joink b a;
      meetAk : forall a b c, meetk a (meetk b c) = meetk (meetk a b) c;
      joinAk : forall a b c, joink a (joink b c) = joink (joink a b) c;
      joinKk : forall a b, meetk a (joink a b) = a;
      meetKk : forall a b, joink a (meetk a b) = a;            
    }.

   Record class_of T (opst opsk : lattice.ops T) := Class {
      baset : lattice.class_of opst;
      basek : lattice.class_of opsk;
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

    
    Definition latticet := lattice.Pack (baset class).
    Definition latticek : latticek.
    Proof.
      eapply latticek.Pack with (ops := opsk cT).
      constructor.
      - apply (basek class).
      - constructor. 
        * apply (meetCk (mixin class)).
        * apply (joinCk (mixin class)).
        * apply (meetAk (mixin class)).
        * apply (joinAk (mixin class)).
        * apply (joinKk (mixin class)).
        * apply (meetKk (mixin class)).
    Defined.
        


  End ClassDef.

  Module  Exports.    
    Coercion baset : class_of >-> lattice.class_of.
    Coercion basek : class_of >-> lattice.class_of.
    Coercion mixin : class_of >-> mixin_of.
    Coercion sort : type >-> Sortclass.
    Coercion latticet : type >-> lattice.type.
    Coercion latticek : type >-> latticek.type.
    Canonical Structure latticet.
    Canonical Structure latticek.
    Notation PreBilattice := type.
    Notation PreBilatticeMixin := mixin_of.    
    
    Definition meett L := @meet (latticet L).
    Definition joint L := @join (latticet L).
    Definition let_ (L : PreBilattice) (a b : L) := meett a b = a.
    Definition meetk L := @meet (latticek L).
    Definition joink L := lattice.join (lattice.class (latticek L)).
    Definition lek (L : PreBilattice) (a b : L) := meetk a b = a.

    (* Definition meett T := meett (class T).
    Definition joint T := joint (class T).
    Definition let_ (T : PreBilattice) (a b : T) := meett a b = a.
    Definition meetk T := meetk (class T).
    Definition joink T := joink (class T).
    Definition lek (T : PreBilattice) (a b : T) := meetk a b = a. *)

    Notation "x ∧ y" := (meett x y)(at level 30).
    Notation "x ∨ y" := (joint x y)(at level 30).
    Notation "x ≺ y" := (let_ x y)(at level 40).

    Notation "x <*> y" := (meetk x y)(at level 30).
    Notation "x <+> y" := (joink x y)(at level 30).
    Notation "x ≺_k y" := (lek x y)(at level 40).

   
    (* Ltac tapply lemm := apply (@lemm (latticet _)).
    Ltac trewrite lemm := rewrite (@lemm (latticet _)).
    Ltac kapply lemm := apply (@lemm (latticek _)).
    Ltac krewrite lemm := rewrite (@lemm (latticek _)). *)

    
    
    Lemma meetCt (L : PreBilattice) : forall (a b : L),  meett a b = meett b a.
    Proof. apply meetC. Qed.
    Lemma joinCt (L : PreBilattice) : forall (a b : L), joint a b = joint b a. 
    Proof. apply joinC. Qed.
    Lemma meetAt (L : PreBilattice) : forall (a b c : L), meett a (meett b c) = meett (meett a b) c. 
    Proof. apply meetA. Qed.
    Lemma joinAt (L : PreBilattice) : forall (a b c : L), joint a (joint b c) = joint (joint a b) c. 
    Proof. apply joinA. Qed.
    Lemma joinKt (L : PreBilattice) : forall (a b : L), meett a (joint a b) = a. 
    Proof. apply joinK. Qed.
    Lemma meetKt (L : PreBilattice) : forall (a b : L), joint a (meett a b) = a. 
    Proof. apply meetK. Qed.

    Lemma meetCk (L : PreBilattice) : forall (a b : L), meetk a b = meetk b a.   
    Proof. Check (@lattice.meetC ).
      rewrite meetC.
      rewrite (lattice.meetC (lattice.class (latticek L))).
      apply (meetCk (class L)). 
      
    Lemma joinCk (L : PreBilattice) : forall (a b : L), joink a b = joink b a. 
    Proof. apply joinCk. Qed.
    Lemma meetAk (L : PreBilattice) : forall (a b c : L), meetk a (meetk b c) = meetk (meetk a b) c. 
    Proof. apply meetAk. Qed.
    Lemma joinAk (L : PreBilattice) : forall (a b c : L), joink a (joink b c) = joink (joink a b) c. 
    Proof. apply joinAk. Qed.
    Lemma joinKk (L : PreBilattice) : forall (a b : L), meetk a (joink a b) = a. 
    Proof. apply joinKk. Qed.
    Lemma meetKk (L : PreBilattice) : forall (a b : L), joink a (meetk a b) = a. 
    Proof. apply meetKk. Qed.
    
  End Exports.
End PreBilattice.  



 

Export PreBilattice.Exports.
