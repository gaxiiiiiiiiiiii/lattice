Require Import AlgeblaLattice.
From mathcomp Require Export ssreflect.
Require Import FunctionalExtensionality.



Definition mu {L : complat} (f : L -> L) : L := @inf L (fun x => f x = x).
Definition nu {L : complat} (f : L -> L) : L := @sup L (fun x => f x = x).
Notation "[mu  X => P ]" := (mu (fun X => P)).
Notation "[nu  X => P ]" := (nu (fun X => P)).
Notation "A × B" := (prodcomplat A B)(at level 5).
Notation "A → B" := (funccomplat A B)(at level 10).

Definition monol {L1 L2 L: complat} (f : L1 × L2 -> L) :=
   forall y, mono (fun x => f (x,y)).

Definition monor {L1 L2 L: complat} (f : L1 × L2 -> L) :=
   forall x, mono (fun y => f (x,y)).

Theorem monolr {L1 L2 L: complat} (f : L1 × L2 -> L) :
  monol f -> monor f -> mono f.
Proof.
  move => Hl Hr [x1 y1] [x2 y2] H.
  unfold le, meet in H; simpl in H.
  apply pair_equal_spec in H; inversion_clear H.
  apply trans with (f (x2, y1)).
  - apply Hl; auto.
  - apply Hr; auto.
Qed.

Definition mono_preserve {T : lattice}{L : complat}(h : T → L -> T → L) :=
  forall f, mono f -> mono (h f).

Theorem fp_mono  {T : lattice}{L : complat}(h : T → L -> T → L) :
   mono h -> mono_preserve h -> mono (mu h).
Proof.
  move => H1 H2 => x y H.
  unfold mu, inf => /=.
  apply is_inf => a Ha.
  inversion Ha; subst.
  rename x0 into f.
  unfold In in H0.

  have Hf : (mu h ≺ f). {
    unfold mu.
    rewrite  <- tarski_lfp_gg; auto.
    move : (tarski_lfp H1) => [_ Hh].
    apply Hh; auto.
  }
  unfold mu, inf in Hf.
  simpl in Hf.
  apply trans with ([set x | inf (Im (T -> L) L ([set x0 | h x0 = x0]) ([set f | f x]))] y); auto.
  unfold mu, inf => /= in Hf.



Theorem mono_mu_l {L1 L2: complat} (f : L1 × L2 → L1) :
  monol f -> monor f -> mono (@mu (L2 → L1)(fun g  => (fun y : L2 => f (g(y),y)))).
Proof.
  move => Hl Hr x y H.
  unfold mu.
  unfold mu, inf => /=.

  (* apply is_lowb. *)
  (* eapply Im_intro with  ( @mu (L2 → L1)(fun g  => (fun y : L2 => f (g(y),y)))). *)
  (* - unfold In. *)


  apply is_inf => a Ha.
  inversion Ha; subst.
  rename x0 into g.
  unfold In in H0.
  apply is_lowb.
  econstructor; unfold In; auto; subst.
  apply H1; auto.
  suff : (f(x0 y, y) = f(x0 x, x)). {
    move => ->.
    apply  (equal_f  H1 x).
  }





Axiom mono_mu_r : forall {L1 L2 : complat}(f : L1 × L2 -> L2),
  monol f -> monor f -> mono (fun x => mu (fun y => f (x,y) )).



Section bekic.
  Variable E1 E2 : complat.
  Variable f1 : E1 × E2 -> E1.
  Variable f2 : E1 × E2 -> E2.
  Hypotheses Hf1l : monol f1.
  Hypotheses Hf1r : monor f1.
  Definition Hf1 := monolr f1 Hf1l Hf1r.
  Hypotheses Hf2l : monol f2.
  Hypotheses Hf2r : monor f2.
  Definition Hf2 := monolr f2 Hf2l Hf2r.




  Definition f (x : E1 × E2) : E1 × E2 :=
    (f1 (fst x, snd x), f2 (fst x, snd x)).

  Theorem prodlat_le  (A B : complat) (x y : prodlat A B) :
    fst x ≺ fst y -> snd x ≺ snd y -> @le (prodlat A B) x y.
  Proof.
    destruct x as [x1 x2], y as [y1 y2] => /= H1 H2.
    unfold le, meet => /=.
    congr pair; auto.
  Qed.

  Theorem monof : mono f.
  Proof.
    unfold mono, base, complat_type, prodcomplat, prodlat.
    move => [a1 a2] [b1 b2] H.
    unfold f => /=.
    apply prodlat_le => /=; [apply Hf1 | apply Hf2]; auto.
  Qed.

  Theorem mu_fp {L : complat} (x : L)  (g : L -> L) (Hm : mono g):
    x = mu g -> x = g x.
  Proof.
    unfold mu.
    rewrite <- tarski_lfp_gg; auto => H.
    move : (tarski_lfp Hm); case; subst; auto.
  Qed.

  Theorem bakic_mu :
    mu (fun  X : E1 × E2 => (f1 (fst X, snd X), f2(fst X, snd X))) =
    (
      mu (fun x => f1(x, (mu (fun y => f2(x,y))))),
      mu (fun y => f2(mu (fun x => f1(x,y)), y))
    ).
  Proof.
    remember  (mu (fun  X : E1 × E2 => (f1 (fst X, snd X), f2(fst X, snd X)))) as p.
    destruct p as [a b].
    remember  (fun x => f1(x, (mu (fun y => f2(x,y))))) as f1'.
    remember (fun y => f2(mu (fun x => f1(x,y)), y)) as f2'.
    remember (mu f1') as a'.
    remember (mu f2') as b'.

    have : a' = f1' a'. {
      apply (mu_fp a' f1'); auto.
      subst f1'.
      move => x y H.
      subst f1'.
      apply Hf1.
      unfold le, meet => /=.
      congr pair; auto.
      suff : ([mu y0 => f2 (x, y0)] ≺ [mu y0 => f2 (y, y0)]); auto.
      unfold mu.
      apply is_lowb.
      unfold In.

      apply is_inf => z.
      unfold In => Hz.
      apply is_lowb.
      unfold In.


    }










