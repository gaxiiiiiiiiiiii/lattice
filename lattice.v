From mathcomp Require Export ssreflect.
Require Export Ensembles Image.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation "x \in X" := (In _ X x)(at level 30) .
Notation "{set  T }" := (Ensemble T)(at level 10).
Notation "f ∘ g" := (fun x => f (g x))(at level 40).

Module lattice.

  Record ops T := Ops {
    meet_ : T -> T -> T;
    join_ : T -> T -> T;    
  }.

  Record mixin_of T (ops_ : ops T ):= Mixin {    
    meet := meet_ ops_;
    join := join_ ops_;
    meetC : forall a b, meet a b = meet b a;
    joinC : forall a b, join a b = join b a;
    meetA : forall a b c, meet a (meet b c) = meet (meet a b) c;
    joinA : forall a b c , join a (join b c) = join (join a b) c;
    joinK : forall a b, meet a (join a b) = a;
    meetK : forall a b, join a (meet a b) = a;
  }.
  Notation class_of := mixin_of (only parsing).

  Section ClassDef.

    Structure type := Pack {
      sort : Type; 
      ops_ : ops sort;  
      _ : class_of ops_
    }.

    Variables (cT : type).    
    Definition class := let: Pack _ _ c := cT return class_of (ops_ cT) in c.

  
  End ClassDef.

  Module Exports.
    Coercion sort : type >-> Sortclass.
    Notation lattice := type.
    Notation latticeMixin := Mixin.
    
    Definition meet T := meet (class T).
    Definition join T := join (class T).
    Definition le (T : lattice) (x y : T) := meet x y = x.

    Lemma meetC (T : lattice) : forall (a b : T), meet a b = meet b a.
    Proof. apply meetC. Qed.
    Lemma joinC (T : lattice) : forall (a b : T), join a b = join b a.
    Proof. apply joinC. Qed.
    Lemma meetA (T : lattice) : forall (a b c : T), meet a (meet b c) = meet (meet a b) c.
    Proof. apply meetA. Qed.
    Lemma joinA (T : lattice) : forall (a b c : T), join a (join b c) = join (join a b) c.
    Proof. apply joinA. Qed.
    Lemma joinK (T : lattice) : forall (a b : T), meet a (join a b) = a.
    Proof. apply joinK. Qed.
    Lemma meetK (T : lattice) : forall (a b : T), join a (meet a b) = a.
    Proof. apply meetK. Qed.


    Notation "x ∧ y" := (meet x y)(at level 30).
    Notation "x ∨ y" := (join x y)(at level 30).   
    Notation "x ≺ y" := (le x y)(at level 40). 
   
  End Exports.

End lattice.

Export lattice.Exports.

Section latticeTheory.

 Definition mono {L1 L2 : lattice}(f : L1 -> L2) :=
    forall a b, a ≺ b -> f a ≺ f b.

  Definition antimono {L1 L2 : lattice}(f : L1 -> L2) :=
    forall a b, a ≺ b -> f b ≺ f a.  

  Definition directed  {L : lattice}(X : {set L}) :=
    forall x y, x \in X  -> y \in X -> exists z, z \in X /\ x ≺ z /\ y ≺ z.
  
  Variable L : lattice.

  Lemma refl (a : L) :
    a ≺ a.
  Proof.
    move : (joinK a (meet a a)).
    rewrite meetK; auto.
  Qed.
  

  Lemma trans (a b c : L) :
    a ≺ b -> b ≺ c -> a ≺ c.
  Proof.
    move => ab bc.
    have H : (meet a (meet b c) = a). {

      rewrite bc; auto.
    }
    rewrite meetA in H.
    rewrite ab in H; auto.
  Qed.

  Lemma antisym (a b : L) :
    a ≺ b -> b ≺ a -> a = b.
  Proof.
    move => ab ba.
    rewrite <- ba.
    rewrite meetC; auto.
  Qed.

    Lemma meetI (a : L) :
    meet a a = a.
  Proof.
    move : (joinK a (meet a a)).
    rewrite meetK; auto.
  Qed.

  Lemma joinI (a : L) :
    join a a = a.
  Proof.
    move : (meetK a (join a a)).
    rewrite joinK; auto.
  Qed.

  Lemma lowb' (a b : L) :
    meet a b ≺ a /\ meet a b ≺ b.
  Proof.
    split; move.
    - rewrite (meetC (meet a b) a).
      rewrite meetA.
      move : (refl a).
      move => -> //=.
    - rewrite <- meetA.
      move : (refl b).
      move => -> //=.
  Qed.

  Lemma inf' (a b : L) :
    forall c, c ≺ a -> c ≺ b -> c ≺ meet a b.
  Proof.
    move => c Ha  Hb.
    unfold le.
    rewrite meetA Ha Hb; auto.
  Qed.

  Lemma inf_uni (a b c : L) :
    c ≺ a -> c ≺ b -> (forall d, d ≺ a -> d ≺ b -> d ≺ c) -> meet a b = c.
  Proof.
    move => Ha Hb H.
    move : (lowb' a b) => [Ha' Hb'].
    move : (inf' Ha Hb) => H'.
    apply antisym; auto.
  Qed.

  Lemma upb' (a b : L) :
    a ≺ join a b /\ b ≺ join a b.
  Proof.
    split; move.
    - apply  (joinK a b).
    - rewrite (joinC a b).
      apply (joinK b a).
  Qed.


  Lemma sup' (a b : L) :
    forall c, a ≺ c -> b ≺ c -> join a b ≺ c.
  Proof.
    move => c Ha  Hb.
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

  Lemma sup_uni (a b c : L) :
    a ≺ c -> b ≺ c -> (forall d, a ≺ d -> b ≺ d -> c ≺ d) -> join a b = c.
  Proof.
    move => Ha Hb H.
    move : (upb' a b) => [Ha' Hb'].
    move : (sup' Ha Hb) => H'.
    apply antisym; auto.
  Qed.

  Lemma join_meet (a b : L) :
    a ≺ b <-> join a b = b.
  Proof.
    split.
    - move => <-.
      rewrite joinC.
      rewrite meetC.
      rewrite meetK; auto.
    - move => <- .
      move : (upb' a b); case; auto.
  Qed.


  (* about operator *)

  Lemma antimono_compose_mono {L1 L2 L3 : lattice}(f : L1 -> L2)(g : L2 -> L3) :
    antimono f -> antimono g -> mono (g ∘ f).
  Proof. 
    move => Hf Hg x y H; eauto.
  Qed.

  Lemma mono_antimono_constant (f : L -> L) :
    mono f -> antimono f -> forall x y, f x = f y.
  Proof.
    move => Hm Ha x y.
    apply antisym.
    - move : (lowb' x y) => [low_x low_y].
      apply trans with (f (meet x y)).      
      - apply Ha; auto.
      - apply Hm; auto.      
    - move : (upb' x y) => [up_x up_y].
      apply trans with (f (join x y)).
      - apply Hm; auto.
      - apply Ha; auto.
  Qed.


End latticeTheory.

Module complat.
  Section ClassDef.

    Record mixin_of T (ops_ : lattice.ops T ):= Mixin {   
      meetc := lattice.meet_ ops_;
      joinc := lattice.join_ ops_;
      lec := fun a b => meetc a b = a;

      sup : Ensemble T -> T;
      inf : Ensemble T -> T;
      
      is_upb : forall (A : Ensemble T) a, a \in A -> lec a (sup A);
      is_sup : forall (A : Ensemble T) a,
              (forall b, b \in A -> lec b a) -> lec (sup A) a;
      is_lowb : forall (A : Ensemble T) a, a \in A -> lec (inf A)a;
      is_inf : forall (A : Ensemble T) a,
              (forall b, b \in A -> lec a b) -> lec a (inf A);    
    }.


    Record class_of T (ops_ : lattice.ops T) := Class {
      base : lattice.class_of ops_;
      mixin : mixin_of ops_
    }.

    Structure type := Pack {
      sort : Type; 
      ops_ : lattice.ops sort;  
      _ : class_of ops_
    }.

    Variables  (cT : type).
    Definition class := let: Pack _ _ c := cT return class_of (ops_ cT) in c.
    Definition lattice := @lattice.Pack (sort cT) (ops_ cT) (base class).    

  End ClassDef.  

  Module  Exports.
    Coercion base : class_of >-> lattice.class_of.
    Coercion mixin : class_of >-> mixin_of.
    Coercion sort : type >-> Sortclass.
    Coercion lattice : type >-> lattice.type.
    Canonical lattice.
    Notation complat := type.
    Notation complatMixin := mixin_of.    

    Definition sup T := sup (class T).
    Definition inf T := inf (class T).
    Definition lec T := lec (class T).
    Definition bot {T} := @inf T (Full_set T).
    Definition top {T} := @sup T (Full_set T).    
    Notation "⊤" := top.
    Notation "⊥" := bot.    

    Lemma is_upb (T : complat) : forall (A : Ensemble T) a, a \in A -> a ≺ (sup A).
    Proof. apply is_upb. Qed.
    Lemma is_sup ( T : complat) : forall (A : Ensemble T) a,
            (forall b, b \in A -> b ≺ a) -> (sup A) ≺ a.
    Proof. apply is_sup. Qed.
    Lemma is_lowb (T : complat) : forall (A : Ensemble T) a, a \in A -> (inf A) ≺ a.
    Proof. apply is_lowb. Qed.
    Lemma is_inf (T : complat) : forall (A : Ensemble T) a,
            (forall b, b \in A -> a ≺ b) -> a ≺ (inf A).
    Proof. apply is_inf. Qed.

  End Exports.
End complat.

Export complat.Exports.

Section complatTheory.

  Definition continuous  {L : complat}(f : L -> L) :=
      forall X : {set L}, directed X -> f (sup X) = sup (Im _ _ X f).

  Definition is_lfp  {L : lattice}(f : L -> L) a :=
    f a = a /\ forall b, f b = b -> a ≺ b.

  Definition is_gfp  {L : lattice}(f : L -> L) a :=
    f a = a /\ forall b, f b = b -> b ≺ a.

  Definition lfp {L : complat}(f : L -> L) (Hf : mono f) :=
    (inf (fun x => f x ≺ x)).

  Definition gfp {L : complat}(f : L -> L) (Hf : mono f) :=
    (sup (fun x => x ≺ f x)).

  Fixpoint pow {L : complat}(f : L -> L) (n : nat) : L -> L :=
    fun X => match n with
    | 0 => X
    | S n' => f (pow f (n') X)
    end.

  Definition chain {L : complat }(f : L -> L) : {set L} :=
    fun X => exists n, X = pow f n ⊥.

  Definition klfp {L : complat}(f : L -> L) := sup (chain f).

  Variable L : complat.
  Section misc.
    Variable X X' : {set L}.
    Hypotheses H : Included _ X X'.

    Theorem inf_antimono :
      inf X' ≺ inf X.
    Proof.
      apply is_inf => b Hb.
      apply is_lowb; auto.
    Qed.

    Theorem sup_mono :
      sup X ≺ sup X'.
    Proof.
      apply is_sup => b Hb.
      apply is_upb; auto.
    Qed.

    Theorem inf_le_sup :
      X <> (Empty_set _) -> inf X ≺ sup X.
    Proof.
      move /not_empty_Inhabited => HX.
      inversion HX.
      eapply trans with x.
      - apply is_lowb; auto.
      - apply is_upb; auto.
    Qed.
  End misc.

  (* tarski's fixpoint theorem *)

  Lemma tarski_lfp (f : L -> L) (Hf : mono f):
    is_lfp f (lfp Hf).
  Proof.
    remember (fun x => f x ≺ x) as G.
    remember (inf G) as g.
    have HG : inf G \in G. {
      subst.
      apply is_inf => y Hy.
      apply trans with (f y); auto.
      apply Hf.
      apply is_lowb; auto.
    }
    have Hg : f g ≺ g by subst.
    split.
    - subst g G; apply antisym; auto.
      apply is_lowb; simpl.
      apply Hf; auto.
    - move => b Hb.
      subst g G.
      apply is_lowb.
      unfold In.
      rewrite Hb.
      apply refl.
  Qed.


  Lemma tarski_lfp_gg (f : L -> L) (Hf : mono f) :
    inf (fun x => f x ≺ x) = inf (fun x => f x = x).
  Proof.
    remember (fun x => f x ≺ x) as G.
    remember (inf G) as g.
    have : f g = g /\ forall b : L, f b = b -> g ≺ b. {
      move : (tarski_lfp Hf); case; subst G g; auto.
    }
    move => [H1 H2].
    apply antisym.
    - apply is_inf => b; auto.
    - apply is_lowb; auto.
  Qed.

  Lemma tarski_gfp (f : L -> L) (Hf : mono f):
    is_gfp f (gfp Hf).
  Proof.
    remember (fun x => x ≺ f x) as G.
    remember (sup G) as g.
    have HG : g \in G. {
      subst.
      unfold In.
      apply is_sup => b Hb.
      apply trans with (f b); auto.
      apply Hf.
      apply is_upb; auto.
    }
    have Hg : g ≺ f g by subst.
    split.
    - subst g G; apply antisym; auto.
      apply is_upb.
      apply Hf; auto.
    - move => b Hb.
      subst g.
      apply is_upb.
      subst G.
      unfold In.
      rewrite  Hb.
      apply refl.
  Qed.

  Lemma tarski_gfp_gg (f : L -> L) (Hf : mono f) :
    sup (fun x => x ≺ f x) = sup (fun x => x = f x).
  Proof.
    move : (tarski_gfp Hf) => [H1 H2].
    remember (fun x => x ≺ f x) as G.
    remember (sup G) as g.
    apply antisym.
    - subst G g.
      apply is_upb.
      unfold In; auto.
    - apply is_sup => x; auto.
  Qed.

  Lemma sup_join (x y : L) :
    sup (Couple _ x y) = join x y.
  Proof.
    apply antisym.
    - move : (upb' x y) => [Hx Hy].
      apply is_sup => z.
      case; auto.
    - apply sup'; apply is_upb; constructor.
  Qed.

  Lemma counti_mono (f : L -> L) :
    continuous f -> mono f.
  Proof.
    unfold continuous, mono => H a b Hab.
    pose AB := (Couple _ a b).
    have HAB : directed AB. {
      move => x y Hx Hy.
      move : (upb' x y) => [H1 H2].
      exists (join x y); repeat split; auto.

      inversion Hx; inversion Hy; subst x y; unfold AB.
      - rewrite joinI.
        apply Couple_l.
      - rewrite <- Hab.
        rewrite joinC meetC meetK.
        constructor.
      - rewrite <- Hab, meetC, meetK; constructor.
      - rewrite joinI; constructor.
    }
    move /H : HAB.
    simpl.
    have : Im L L AB f = (Couple _ (f a) (f b)) . {
      apply Extensionality_Ensembles; split => x.
      - move => H0.
        inversion H0; subst.
        inversion H1; subst; constructor.
      - case; econstructor; auto; constructor.
    }
    move => ->.
    repeat rewrite sup_join.
    have : join a b = b. {
      rewrite <- Hab.
      rewrite meetC joinC meetK; auto.
    }
    repeat move => ->.
    move : (upb' (f a) (f b)); case; auto.
  Qed.

  Lemma bot_min (X : L) : ⊥ ≺ X.
  Proof.
    apply is_lowb; constructor.

  Qed.

  Lemma top_max (X : L) : X ≺ ⊤.
  Proof.
    apply is_upb; constructor.
  Qed.

  (* kleene's fixpoint theorem *)

  Lemma powS (f : L -> L) (Hf : mono f) n :
    pow f n ⊥ ≺ pow f (n + 1) ⊥.
  Proof.
    induction n.
    - apply /bot_min.
    - apply Hf; auto.
  Qed.

  Lemma powLe (f : L -> L) (Hf : mono f) n m :
    pow f n ⊥ ≺ pow f (n + m) ⊥.
  Proof.
    induction m.
    - rewrite PeanoNat.Nat.add_0_r.
      apply refl.
    - apply trans with (pow f (n + m) ⊥); auto.
      rewrite PeanoNat.Nat.add_succ_r.
      rewrite <- PeanoNat.Nat.add_1_r.
      apply powS; auto.
    Qed.
    
  Lemma dir_chain (f : L -> L) (Hf : mono f) :
    directed (chain f).
  Proof.
    move => x y.
    move  => [n ->] [m ->].
    exists (pow f (n + m) ⊥); repeat split.
    - exists (n + m); auto.
    - apply powLe; auto.
    - rewrite PeanoNat.Nat.add_comm.
      apply powLe; auto.
  Qed.

  Theorem kleene  (f : L -> L):
    continuous f -> is_lfp f (klfp f).
  Proof.
    unfold continuous.
    move => Hc.
    move : (counti_mono Hc) => Hf.
    move : (Hc _ (dir_chain Hf)) => Hd; clear Hc.
    split.
    { unfold klfp.
      apply antisym.
      - rewrite Hd.
        apply is_sup.
        move => x H.
        inversion H; subst.
        apply is_upb.
        inversion H0; subst.
        exists (1 + x); auto.
      - apply is_sup => x [n ->].
        apply trans with (f (pow f n ⊥)).
        - move : (powS Hf n).
          rewrite PeanoNat.Nat.add_comm; auto.
        - apply Hf.
          apply is_upb.
          exists n; auto.
    }
    {
      move => x Hx.
      unfold klfp.
      apply is_sup => y [n Hn].
      subst y.
      induction n.
      - apply bot_min.
      - rewrite <- Hx.
        apply Hf; auto.
    }
  Qed.

End complatTheory.  


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
    Definition bott T := @bot (complatt T).
    Definition topt T := @top (complatt T).
    Definition botk T := @bot (complatk T).
    Definition topk T := @top (complatk T).

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
  ¬ (TRUE L) = FALSE L.
Proof.
  apply antisym.
  - rewrite <- (NN (FALSE L)).
    apply letN.
    unfold TRUE,top.
    apply is_upb.
    constructor.
  - unfold FALSE, bot.
    apply is_lowb.
    constructor.
Qed.

Lemma neg_FALSE :  
  ¬ (FALSE L) = TRUE L.
Proof.
  apply antisym; first last.
  - rewrite <- (NN (TRUE L)).
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
    apply inf'.
    * rewrite  <- (NN x). 
      apply letN.
      rewrite NN.
      move : (upb' (¬ x) (¬ y)); case; auto.
    * rewrite <- (NN y).
      apply letN.
      rewrite NN.
      move : (upb' (¬ x) (¬ y)); case; auto.
  - move : (lowb' x y) => [H1 H2].
    apply sup'; apply letN; auto.
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

    
