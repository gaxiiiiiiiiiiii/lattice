Require Export Lattice.


Global Notation "a == b" := (eqset a b) (at level 70, no associativity).
Definition singleton {T : hSet} (x : T) : {set : T} := fun y => y == x.
Definition couple {T : hSet} (x y : T) : {set : T} := (singleton x ∪ singleton y) % subtype.



Definition isComplatOp {T : hSet} (L : lattice T) (sup inf : {set : T} -> T) :=
  (∏ (A : {set : L}) (a : L), a ∈ A ->  a ≺ sup A) × 
  (∏ (A : {set : L}) (a : L), (∏ (b : L), b ∈ A -> b ≺ a) -> sup A ≺ a) ×
  (∏ (A : {set : L}) (a : L), a ∈ A -> inf A ≺ a) ×  
  (∏ (A : {set : L}) (a : L), (∏ (b : L), b ∈ A -> a ≺ b) -> a ≺ inf A).

Lemma isaprop_isComplatOp {T : hSet} {L : lattice T} (sup inf : {set : T} -> T) :
  isaprop (isComplatOp L sup inf).
Proof.
  repeat apply isapropdirprod;
  (apply impred => X; apply impred => x; apply impred => H);
  apply propproperty.
Defined.

Definition complat (T : hSet) : UU :=
  ∑ (L : lattice T)(sup inf : {set : T} -> T), isComplatOp L sup inf.

Definition make_complat {T : hSet} {L : lattice T} (sup inf : {set : L} -> L) 
  (H : isComplatOp L sup inf) : complat L := L,, sup,, inf,, H.


Coercion complatToLattice (T : hSet) : complat T -> lattice T := pr1.
Coercion complatToSetOp (T : hSet) : complat T -> hSet := fun L => latticeToSet (pr1 L).


Definition sup {T : hSet} {L : complat T} (A : {set : L}) : L := pr1 (pr2 L) A.
Definition inf {T : hSet} {L : complat T} (A : {set : L}) : L := pr1 (pr2 (pr2 L)) A.

Definition bot {T : hSet} {L : complat T} : L := inf fullset.
Definition top {T : hSet} {L : complat T} : L := sup fullset.
Global Notation "⊥" := bot.
Global Notation "⊤" := top.

Definition is_upb {T : hSet} {L : complat T} :
  ∏ A a, a ∈ A -> a ≺ sup A := pr1 (pr2 (pr2 (pr2 L))).
Definition is_sup {T : hSet} {L : complat T} :
  ∏ A a, (∏ b, b ∈ A -> b ≺ a) -> sup A ≺ a := pr1 (pr2 (pr2 (pr2 (pr2 L)))).
Definition is_lowb {T : hSet} {L : complat T} :
  ∏ A a, a ∈ A -> inf A ≺ a := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 L))))).
Definition is_inf {T : hSet} {L : complat T} :
  ∏ A a, (∏ b, b ∈ A -> a ≺ b) -> a ≺ inf A := pr2 (pr2 (pr2 (pr2 (pr2 (pr2 L))))).


Section complatTheory.
  
  Definition continuous  {T : hSet}{L : complat T}(f : L -> L) :=
    ∏ X, directed X -> f (sup X) = sup (image_hsubtype X f).
  

  Definition is_lfp  {T : hSet}{L : lattice T}(f : L -> L) a : Type :=
    (f a = a) × (∏ b, f b = b -> a ≺ b).
  
  
  Definition is_gfp  {T : hSet}{L : lattice T}(f : L -> L) a : Type :=
    (f a = a) × (∏ b, f b = b -> b ≺ a).

  Definition lfp {T : hSet}{L : complat T}(f : L -> L) (Hf : mono f) :=
    (inf (fun x => f x ≺ x)).

  Definition gfp {T : hSet}{L : complat T}(f : L -> L) (Hf : mono f) :=
    (sup (fun x => x ≺ f x)).

  Definition pow {T : hSet} {L : complat T} (f : L -> L)  (n : nat) : L -> L.
  Proof.
    move => x.
    apply (nat_rect (fun _ => L) x (fun _ acc => f acc ) n).
  Defined.

  Definition chain {X : hSet} {L : complat X} (f : L -> L) : {set : L} :=
    fun x => (∃ n, x = pow f n ⊥).

  Definition kleene_lfp {T : hSet}{L : complat T}(f : L -> L) (Hf : mono f) :=
    sup (chain f).
  
  Variable T : hSet.
  Variable L : complat T.
  Section misc.
    Variable X X' : {set : L}.
    Hypotheses H : (X ⊆ X')%subtype.

    Theorem inf_antimono :
      inf X' ≺ inf X.
    Proof.
      apply is_inf => b Hb.
      apply is_lowb.      
      apply (H b) => //.      
    Qed.

    Theorem sup_mono :
      sup X ≺ sup X'.
    Proof.
      apply is_sup => b Hb.
      apply is_upb; auto.
      apply (H b); auto.
    Qed.

    (* Theorem nonempty_has_ellm :
      X != ∅ -> ∃ x, x ∈ X.
    Proof.
    Abort. *)


    (* Theorem inf_le_sup :
      X != ∅ -> inf X ≺ sup X.
    Proof.
      Search (∅).
      move /not_empty_Inhabited => HX.
      inversion HX.
      eapply trans with x.
      - apply is_lowb; auto.
      - apply is_upb; auto.
    Qed. *)
  End misc.

  (* tarski's fixpoint theorem *)

  Lemma tarski_lfp (f : L -> L) (Hf : mono f):
    is_lfp f (lfp f Hf).
  Proof.
    remember ((fun x => f x ≺ x) : {set : L}) as G.
    remember (inf G) as g.
    have HG : inf G ∈ G. {
      subst.
      apply is_inf => y Hy.
      apply transL with (f y); auto.
      apply Hf.
      apply is_lowb; auto.
    }
    have Hg : f g ≺ g by subst.
    unfold is_lfp.
    split.
    - subst g G; apply antisymL; auto.
      apply is_lowb; simpl.
      apply Hf; auto.
    - 
      move => b Hb.
      subst g G. simpl in *.
      apply is_lowb.
      unfold In.
      rewrite Hb.
      apply reflL.
  Qed.


  Lemma tarski_lfp_gg (f : L -> L) (Hf : mono f) :
    inf (fun x => f x ≺ x) = inf (fun x => f x == x).
  Proof.
    remember (fun x => f x ≺ x) as G.
    remember (inf G) as g.
    have : f g == g × ∏ b : L, f b = b -> g ≺ b. {
      move : (tarski_lfp f Hf) => H.
      induction H.
      split; subst G g; auto.
    }
    move => [H1 H2].
    apply antisymL.
    - apply is_inf => b; auto.
    - apply is_lowb; auto.
  Qed.

  Lemma tarski_gfp (f : L -> L) (Hf : mono f):
    is_gfp f (gfp f Hf).
  Proof.
    remember (fun x => x ≺ f x) as G.
    remember (sup G) as g.
    have HG : g ∈ G. {
      subst.
      unfold In.
      apply is_sup => b Hb.
      apply transL with (f b); auto.
      apply Hf.
      apply is_upb; auto.
    }
    have Hg : g ≺ f g by subst.
    split.
    - subst g G; apply antisymL; auto.
      apply is_upb.
      apply Hf; auto.
    - move => b Hb.
      subst g.
      apply is_upb.
      subst G.
      unfold In.
      rewrite  Hb.
      apply reflL.
  Qed.

  Lemma tarski_gfp_gg (f : L -> L) (Hf : mono f) :
    sup (fun x => x ≺ f x) = sup (fun x => x == f x).
  Proof.
    move : (tarski_gfp f Hf) => [H1 H2].
    remember (fun x => x ≺ f x) as G.
    remember (sup G) as g.
    apply antisymL.
    - apply is_upb. simpl.
      subst G g.
      unfold gfp in *; auto.
      apply pathsinv0; auto.
    - apply is_sup => x H.
      simpl in H.
      subst g G.
      apply is_upb.
      unfold In.
      rewrite <- H.
      apply reflL.      
  Qed.

  Lemma sup_join (x y : L) :
    sup (couple x y)= join x y.
  Proof.
    apply antisymL.
    - move : (join_upb x y) => [Hx Hy].
      apply is_sup => z.
      unfold In => H.
      simpl in H.      
      unfold ishinh_UU in H.
      eapply H => Hz.
      induction Hz as [Hz |Hz]; induction Hz; auto .
    - apply join_sup; apply is_upb; simpl;
      unfold ishinh_UU => P; apply; [left|right]; auto.
  Qed.

  Lemma counti_mono (f : L -> L) :
    continuous f -> mono f.
  Proof.
    unfold continuous, mono => H a b Hab.
    pose AB := (couple a b).
    have HAB : directed AB. {
      move => x y Hx Hy.
      move : (join_upb x y) => [H1 H2].
      move => P; apply; clear P.       
      exists (join x y).
      unfold AB, couple in Hx, Hy ; simpl in Hx, Hy.
      apply Hx; clear Hx => Hx.
      apply Hy; clear Hy => Hy.
      repeat split; auto.
      simpl => P; apply.
      induction Hx as [Hx'|Hx'], Hy as [Hy'|Hy'];
      induction Hx', Hy'.
      - left. apply joinI.
      - right. apply meet_join; auto.
      - right. rewrite joinC. apply meet_join; auto.
      - right; apply joinI.
    }
    move /H : HAB.
    simpl.
    have : image_hsubtype  AB f = (couple (f a) (f b)). {
      apply hsubtype_univalence => x; split => H0;
      simpl in H0; apply H0; clear H0 => H0.
      - induction H0 as [x0 H0].
        induction H0 as [Hf H0].
        apply H0; clear H0 => H0.
        induction H0 as [H0|H0]; induction H0; induction Hf;
        simpl => P; apply; clear P; [left|right]; auto.
      - induction H0 as [H0|H0]; rewrite H0;
        move => P; apply; clear P;
        [exists a|exists b]; split; auto;
        unfold AB, couple; simpl => P; apply; clear P;
        [left|right]; auto.      
    }
    move => ->.
    repeat rewrite sup_join.
    have : join a b = b. {
      rewrite <- Hab.
      rewrite meetC joinC joinmeetK; auto.
    }
    repeat move => ->.
    move : (join_upb (f a) (f b)); case; auto.
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

  (* Lemma powS (f : L -> L) (Hf : mono f) n :
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
  Qed. *)

End complatTheory.  



  
  
  

  






  



