Require Export Lattice.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(****************************************************)
(* Definition of complete lattice *)
(****************************************************)


Class complat := CompLat {
  lat : lattice;
  sup : Ensemble lat -> lat;
  inf : Ensemble lat -> lat;
  is_upb : forall (A : Ensemble lat) a, a \in A -> a ≺ (sup A);
  is_sup : forall (A : Ensemble lat) a,
           (forall b, b \in A -> b ≺ a) -> (sup A) ≺ a;
  is_lowb : forall (A : Ensemble lat) a, a \in A -> (inf A) ≺ a;
  is_inf : forall (A : Ensemble lat) a,
           (forall b, b \in A -> a ≺ b) -> a ≺ (inf A);
  bot := inf (Full_set lat);
  top := sup (Full_set lat)
}.

Coercion complat_type (L : complat) :=
  let: CompLat L' _ _ _ _ _ _ := L in  L'.

Notation "⊥" := bot.
Notation "⊤" := top.

Definition bigcup {T} (X : {set {set T}}) : {set T} :=
  fun x => exists I, I \in X /\ x \in I.

Definition bigcap {T} (X : {set {set T}}) : {set T}:=
  fun x => forall I, I \in X -> x \in I.

Definition continuous  {L : complat}(f : L -> L) :=
    forall X : {set L}, directed X -> f (sup X) = sup (Im _ _ X f).

Definition is_lfp  {L : lattice}(f : L -> L) a :=
  f a = a /\ forall b, f b = b -> a ≺ b.

Definition is_gfp  {L : lattice}(f : L -> L) a :=
  f a = a /\ forall b, f b = b -> b ≺ a.

Definition lfp {L : complat}(f : L -> L) (Hf : mono f) :=
  (inf (fun x => f x ≺ x)).

Definition gpf {L : complat}(f : L -> L) (Hf : mono f) :=
  (sup (fun x => x ≺ f x)).

Fixpoint pow {L : complat}(f : L -> L) (n : nat) : L -> L :=
  fun X => match n with
  | 0 => X
  | S n' => f (pow f (n') X)
  end.

Definition chain {L : complat }(f : L -> L) : {set L} :=
  fun X => exists n, X = pow f n ⊥.

Definition klfp {L : complat}(f : L -> L) := sup (chain f).


(****************************************************)
(* theorems *)
(****************************************************)

Section theorem.
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
    is_lfp f (inf (fun x => f x ≺ x)).
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


  Lemma tarski_lfp_gg f (Hf : mono f) :
    inf (fun x => f x ≺ x) = inf (fun x => f x = x).
  Proof.
    remember ([set x | f x ≺ x]) as G.
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
    is_gfp f (sup (fun x => x ≺ f x)).
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

  Lemma tarski_gfp_gg f (Hf : mono f) :
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

  Lemma sup_join x y :
    sup (Couple _ x y) = join x y.
  Proof.
    apply antisym.
    - move : (upb' x y) => [Hx Hy].
      apply is_sup => z.
      case; auto.
    - apply sup'; apply is_upb; constructor.
  Qed.

  Lemma counti_mono f :
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

  Lemma powS f (Hf : mono f) n :
    pow f n ⊥ ≺ pow f (n + 1) ⊥.
  Proof.
    induction n.
    - apply /bot_min.
    - apply Hf; auto.
  Qed.

  Lemma powLe f (Hf : mono f) n m :
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
    
  Lemma dir_chain f (Hf : mono f) :
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

End theorem.




