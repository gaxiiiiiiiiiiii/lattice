Require Export Ultimate.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Global Notation "{set : X }" := (subtype_set X).
Global Notation "∅" := (emptysubtype _).

Open Scope type_scope.
Open Scope logic.
Open Scope subtype.

Notation "A ∩ B" := (binary_intersection A B) (at level 40, left associativity) : subtype.



(*
** Logic Programming
*)




Section LogicProgram.

  Definition literal (A : Type) := A ⨿ A.
  Definition pos (A : Type) : A -> literal A := ii1.
  Definition neg (A : Type) : A -> literal A := ii2.
    

  Definition rule (A : Type) := A × {set : literal A}.
  Notation "a ← M" := ((a,, M) : rule _) (at level 70).

  Definition positives (A : Type) : {set : literal A} -> {set : A}.
  Proof.
    move => M a. exact (M (pos a)).
  Defined.

  Definition negatives (A : Type) : {set : literal A} -> {set : A}.
  Proof.
    move => M a. exact (M (neg a)).
  Defined.

  Definition is_definite_rule (A : Type) (r : rule A) :=
    negatives (pr2 r) = ∅.

  Definition program A := {set : rule A}.

  Definition is_definite_program (A : Type) (P : program A) :=
    ∏ r, P r -> is_definite_rule r.

  Definition definite_program A := ∑ P : program A, is_definite_program P.

  Definition approximate' (A : Type) (P : program A) (XY : {set : A} × {set : A}) : {set : A} :=
    fun a => ∃ M, 
      P (a ← M) ∧ 
      (positives M ⊆ (pr1 XY)) ∧
      ( (∅ : {set : A}) = (negatives M) ∩ (pr2 XY) ).

  Definition approximate (A : Type) (P : program A) (XY : {set : A} × {set : A}) : {set : A} × {set : A} :=
    approximate' P XY,, approximate' P (pr2 XY,, pr1 XY).

End LogicProgram.

Section AF.

  Definition AF := ∑ A : Type, {set : A × A}.

  Definition conflict_free (F : AF) (S : {set : pr1 F}) := 
    ∏ a b, S a -> S b -> ¬ ((pr2 F) (a,,b)).

  Definition attackers (F : AF) (a : pr1 F) : {set : pr1 F} :=
    fun b => (pr2 F) (b,,a).

  Definition attacked (F : AF) (S : {set : pr1 F}) :=
    fun b => ∃ a, S a ∧ (pr2 F) (a,,b).

  Definition defends (F : AF) (S : {set : pr1 F}) (a : pr1 F) :=
    attackers a ⊆ attacked S.

End AF.

Section ADF.

  Definition par (A : Type) (L : {set : A × A}) (s : A) : {set : A} := fun r => L (r,,s).

  Definition ADF := ∑ (A : Type) (L : {set : A × A}), (∏ (s : A), {set : (∑ S, S ⊆ par L s)}).
  
  (* 
    ADF := (A, par, {Cₛⁱⁿ})
    par(s) : {set : A} repreesnts parents of s
    Cₛⁱⁿ : {set : par(s)}  represents accept condition for s. 

  *)
  Definition ADF := 
    ∑ (A : Type) 
      (par : A -> {set : A}), 
      (∏ (s : A), {set : ∑ S : {set : A}, S ⊆ par s}).
     (* (∏ (s : A) (H : ∑ S : {set : A}, S ⊆ (par s)), hProp). *)

  Section Example.

    Inductive S_ := a | b | c | d.

    Definition state : hSet.
    Proof.
      exists S_.
      apply isasetifdeceq.
      unfold isdeceq.
      move => x y.
      unfold decidable.
      destruct x, y; auto.
      all : try solve [left; auto].
      all : right => F; inversion F.
    Defined.


    Definition par : state -> {set : state} :=
      fun s t  => match s with
      | a => t = c
      | b => t = b ∨ t = c ∨ t = d
      | c => hfalse
      | d => hfalse
      end.

    Definition C (s : state) :  (∑ S : {set : state}, S ⊆ (par s)) -> hProp.
    Proof.
      move => [S HS].
      remember s as s_.
      induction s.
      - exact (S = ∅).
      - exact (S = fun t => t = b).
      - exact (S = fun t => t = a ∨ t = b).
      - exact (S = ∅).
    Defined.

    Definition example : ADF.
    Proof.
      split with state.
      split with par.
      exact C.
    Defined.

End ADF.

