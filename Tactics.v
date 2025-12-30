(* ========================================================================= *)
(*                             Tactics.v                                     *)
(*                                                                           *)
(*  Custom tactics for the regional associativity development.               *)
(*  These automate common proof patterns in lattice theory and algebra.      *)
(* ========================================================================= *)

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.
Require Import Coq.omega.Omega.
Require Import Coq.micromega.Lia.

(** * Lattice Tactics *)

(** Simplify lattice expressions using the lattice laws *)

Ltac lattice_simpl :=
  repeat match goal with
  (* Idempotence *)
  | |- context[meet ?R ?R] => rewrite meet_idem
  | |- context[join ?R ?R] => rewrite join_idem
  (* Identity elements *)
  | |- context[meet ?R empty] => rewrite meet_empty
  | |- context[meet empty ?R] => rewrite (meet_comm empty R); rewrite meet_empty
  | |- context[join ?R empty] => rewrite join_empty
  | |- context[join empty ?R] => rewrite join_comm; rewrite join_empty
  | |- context[meet ?R top] => rewrite meet_top
  | |- context[meet top ?R] => rewrite meet_comm; rewrite meet_top
  | |- context[join ?R top] => rewrite join_top
  | |- context[join top ?R] => rewrite join_comm; rewrite join_top
  (* Absorption *)
  | |- context[join ?R (meet ?R ?S)] => rewrite absorb_join_meet
  | |- context[meet ?R (join ?R ?S)] => rewrite absorb_meet_join
  end.

(** Prove lattice inclusion goals *)

Ltac prove_incl :=
  unfold incl;
  lattice_simpl;
  try reflexivity;
  try (rewrite meet_assoc; reflexivity);
  try (rewrite <- meet_assoc; reflexivity);
  try (rewrite meet_comm; reflexivity).

(** Normalize lattice expressions to a canonical form *)

Ltac lattice_normalize :=
  repeat (rewrite ?meet_assoc, ?join_assoc);
  repeat match goal with
  | |- context[meet ?S ?R] => 
      match goal with
      | |- context[meet ?R ?S] => fail 1
      | _ => rewrite (meet_comm S R)
      end
  | |- context[join ?S ?R] =>
      match goal with  
      | |- context[join ?R ?S] => fail 1
      | _ => rewrite (join_comm S R)
      end
  end.

(** * Algebra Tactics *)

(** Simplify algebra expressions *)

Ltac alg_simpl :=
  repeat match goal with
  | |- context[@alg_plus _ ?A (@alg_zero _ ?A) ?x] => 
      rewrite (alg_plus_comm (@alg_zero _ A) x); rewrite alg_plus_zero
  | |- context[@alg_plus _ ?A ?x (@alg_zero _ ?A)] =>
      rewrite alg_plus_zero
  | |- context[@alg_mult _ ?A (@alg_one _ ?A) ?x] =>
      rewrite alg_mult_one_l
  | |- context[@alg_mult _ ?A ?x (@alg_one _ ?A)] =>
      rewrite alg_mult_one_r
  | |- context[@alg_plus _ ?A ?x (@alg_neg _ ?A ?x)] =>
      rewrite alg_plus_neg
  | |- context[@alg_plus _ ?A (@alg_neg _ ?A ?x) ?x] =>
      rewrite alg_plus_comm; rewrite alg_plus_neg
  end.

(** Prove algebra equalities by ring-like reasoning *)

Ltac alg_ring :=
  alg_simpl;
  repeat (rewrite ?alg_plus_assoc, ?alg_mult_assoc);
  repeat (rewrite ?alg_distrib_l, ?alg_distrib_r);
  try reflexivity.

(** * Support Tactics *)

(** Prove that an element is supported on a region *)

Ltac prove_supported :=
  unfold supported_on, is_supported_on;
  eexists; 
  try reflexivity;
  try (apply structure_map_id).

(** * Bilinearity Tactics *)

(** Expand bilinear maps *)

Ltac bilin_expand :=
  repeat match goal with
  | |- context[bilin_map _ _ _ _ (alg_plus _ _) _] =>
      rewrite bilin_linear_l_plus
  | |- context[bilin_map _ _ _ _ _ (alg_plus _ _)] =>
      rewrite bilin_linear_r_plus
  | |- context[bilin_map _ _ _ _ (alg_scale _ _) _] =>
      rewrite bilin_linear_l_scale
  | |- context[bilin_map _ _ _ _ _ (alg_scale _ _)] =>
      rewrite bilin_linear_r_scale
  end.

(** * Trilinearity Tactics *)

Ltac trilin_expand :=
  repeat match goal with
  | |- context[trilin_map _ _ _ _ _ (alg_plus _ _) _ _] =>
      rewrite trilin_linear_l
  | |- context[trilin_map _ _ _ _ _ _ (alg_plus _ _) _] =>
      rewrite trilin_linear_m
  | |- context[trilin_map _ _ _ _ _ _ _ (alg_plus _ _)] =>
      rewrite trilin_linear_r
  end.

(** * Gluing Tactics *)

(** Expand gluing operations using the decomposition formula *)

Ltac glue_expand :=
  unfold glue;
  (* Apply the decomposition if available *)
  try rewrite glue_decomposition.

(** * Associator Tactics *)

(** Compute the associator for specific terms *)

Ltac compute_assoc :=
  unfold assoc, associator, left_assoc, right_assoc;
  glue_expand;
  alg_simpl;
  alg_ring.

(** * Čech Tactics *)

(** Simplify Čech coboundary calculations *)

Ltac cech_simpl :=
  unfold coboundary_2_3;
  repeat match goal with
  | |- context[restrict_quad_to_triple _ _ _ _ _ _] =>
      (* Unfold restriction when possible *)
      try unfold restrict_quad_to_triple
  end;
  alg_simpl.

(** Prove cocycle conditions *)

Ltac prove_cocycle :=
  cech_simpl;
  (* The terms should cancel pairwise *)
  repeat match goal with
  | |- @alg_plus _ _ ?x (@alg_neg _ _ ?x) = _ =>
      rewrite alg_plus_neg
  | |- @alg_plus _ _ (@alg_neg _ _ ?x) ?x = _ =>
      rewrite alg_plus_comm; rewrite alg_plus_neg
  end;
  try reflexivity.

(** * Automation *)

(** General-purpose tactic for this development *)

Ltac regional_auto :=
  intros;
  try lattice_simpl;
  try alg_simpl;
  try prove_incl;
  try reflexivity;
  auto.

(** Tactic for goals involving structure maps *)

Ltac struct_map_auto :=
  repeat match goal with
  | |- alg_hom_map _ _ (structure_map _ _ _) _ = _ =>
      try rewrite structure_map_id;
      try rewrite structure_map_comp
  end;
  try reflexivity.

(** * Decidability Tactics *)

(** For finite lattices, many properties are decidable *)

Ltac decide_incl R S :=
  (* For concrete regions, compute meet and check equality *)
  let M := eval compute in (meet R S) in
  match M with
  | R => left; reflexivity
  | _ => right; discriminate
  end.

(** * Debugging Tactics *)

(** Print the current goal with type information *)

Ltac show_goal :=
  match goal with
  | |- ?G => idtac "Goal:" G
  end.

(** Print hypotheses *)

Ltac show_hyps :=
  repeat match goal with
  | H : ?T |- _ => idtac H ":" T; fail
  end.

(** * Notation for Readable Proofs *)

(** These tactics are designed to make proofs more readable *)

Tactic Notation "by" "lattice" := lattice_simpl; reflexivity.
Tactic Notation "by" "algebra" := alg_ring.
Tactic Notation "by" "inclusion" := prove_incl.
Tactic Notation "by" "support" := prove_supported.
Tactic Notation "by" "cocycle" := prove_cocycle.

(** * Lemmas for Tactic Support *)

Section TacticLemmas.
  Context `{k : CommRing}.
  
  (** Double negation *)
  Lemma alg_neg_neg : forall `{A : Algebra} (x : @alg_carrier k A),
    @alg_neg k A (@alg_neg k A x) = x.
  Proof.
    intros.
    (* -(-x) + (-x) = 0, so -(-x) = x *)
    assert (H : @alg_plus k A (@alg_neg k A (@alg_neg k A x)) (@alg_neg k A x) = 
                @alg_zero k A).
    { rewrite alg_plus_neg. reflexivity. }
    (* Also: x + (-x) = 0 *)
    assert (H' : @alg_plus k A x (@alg_neg k A x) = @alg_zero k A).
    { rewrite alg_plus_neg. reflexivity. }
    (* By cancellation, -(-x) = x *)
    admit.
  Admitted.
  
  (** Negation distributes over plus *)
  Lemma alg_neg_plus : forall `{A : Algebra} (x y : @alg_carrier k A),
    @alg_neg k A (@alg_plus k A x y) = 
    @alg_plus k A (@alg_neg k A x) (@alg_neg k A y).
  Proof.
    intros.
    (* (x + y) + ((-x) + (-y)) = x + (y + (-y)) + (-x) = x + (-x) = 0 *)
    (* So -(x + y) = (-x) + (-y) *)
    admit.
  Admitted.
  
  (** Zero times anything is zero *)
  Lemma alg_mult_zero_l : forall `{A : Algebra} (x : @alg_carrier k A),
    @alg_mult k A (@alg_zero k A) x = @alg_zero k A.
  Proof.
    intros.
    (* 0 * x = (0 + 0) * x = 0*x + 0*x, so 0*x = 0 *)
    admit.
  Admitted.
  
  Lemma alg_mult_zero_r : forall `{A : Algebra} (x : @alg_carrier k A),
    @alg_mult k A x (@alg_zero k A) = @alg_zero k A.
  Proof.
    intros.
    admit.
  Admitted.

End TacticLemmas.

(** * Hint Databases *)

Create HintDb regional_lattice.
Create HintDb regional_algebra.
Create HintDb regional_gluing.

#[export] Hint Rewrite meet_idem join_idem : regional_lattice.
#[export] Hint Rewrite meet_empty join_empty : regional_lattice.
#[export] Hint Rewrite meet_top join_top : regional_lattice.
#[export] Hint Rewrite absorb_join_meet absorb_meet_join : regional_lattice.

#[export] Hint Rewrite @alg_plus_zero @alg_mult_one_l @alg_mult_one_r : regional_algebra.
#[export] Hint Rewrite @alg_plus_neg : regional_algebra.

(** * Example Usage *)

Section TacticExamples.
  Context `{RL : RegionLattice}.
  
  (** Example: prove a lattice identity *)
  Example meet_join_absorb : forall R S,
    meet R (join R S) = R.
  Proof.
    intros.
    by lattice.
  Qed.
  
  (** Example: prove an inclusion *)
  Example meet_incl_left : forall R S,
    incl (meet R S) R.
  Proof.
    intros.
    by inclusion.
  Qed.

End TacticExamples.
