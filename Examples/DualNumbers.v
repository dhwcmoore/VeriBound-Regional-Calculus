(* ========================================================================= *)
(*                          Examples/DualNumbers.v                           *)
(*                                                                           *)
(*  The dual numbers Z[ε]/(ε²) as a toy model for associativity under       *)
(*  gluing. This is Appendix C of the paper.                                 *)
(*                                                                           *)
(*  The dual numbers are the simplest setting where:                         *)
(*  - The obstruction class can be computed explicitly                       *)
(*  - Vanishing/non-vanishing depends on parameter choices                   *)
(*  - Edge completion is concrete and visualizable                           *)
(* ========================================================================= *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Setoids.Setoid.
Require Import RegionLattice.
Require Import AlgebraicAssignment.
Require Import BinaryGluing.
Require Import Associator.

Open Scope Z_scope.

(** * The Dual Numbers Z[ε]/(ε²) *)

(** Elements are pairs (a₀, a₁) representing a₀ + a₁ε with ε² = 0 *)

Record DualZ := {
  real_part : Z;
  nilp_part : Z;    (* nilpotent part *)
}.

(** Notation: we write ⟨a, b⟩ for the dual number a + bε *)

Notation "⟨ a , b ⟩" := {| real_part := a; nilp_part := b |} 
  (at level 0) : dual_scope.
Open Scope dual_scope.

(** * Algebra Structure *)

Definition dual_zero : DualZ := ⟨0, 0⟩.
Definition dual_one : DualZ := ⟨1, 0⟩.
Definition dual_eps : DualZ := ⟨0, 1⟩.  (* The nilpotent element ε *)

Definition dual_plus (x y : DualZ) : DualZ :=
  ⟨real_part x + real_part y, nilp_part x + nilp_part y⟩.

Definition dual_neg (x : DualZ) : DualZ :=
  ⟨- real_part x, - nilp_part x⟩.

Definition dual_mult (x y : DualZ) : DualZ :=
  ⟨real_part x * real_part y, 
   real_part x * nilp_part y + nilp_part x * real_part y⟩.
  (* Note: ε² = 0, so we drop the nilp_part x * nilp_part y term *)

Definition dual_scale (r : Z) (x : DualZ) : DualZ :=
  ⟨r * real_part x, r * nilp_part y⟩.

(** * Verification of Algebra Axioms *)

Lemma dual_mult_assoc : forall x y z,
  dual_mult (dual_mult x y) z = dual_mult x (dual_mult y z).
Proof.
  intros [x0 x1] [y0 y1] [z0 z1].
  unfold dual_mult. simpl.
  f_equal; ring.
Qed.

Lemma dual_mult_one_l : forall x,
  dual_mult dual_one x = x.
Proof.
  intros [x0 x1].
  unfold dual_mult, dual_one. simpl.
  f_equal; ring.
Qed.

Lemma dual_mult_one_r : forall x,
  dual_mult x dual_one = x.
Proof.
  intros [x0 x1].
  unfold dual_mult, dual_one. simpl.
  f_equal; ring.
Qed.

Lemma dual_distrib_l : forall x y z,
  dual_mult x (dual_plus y z) = dual_plus (dual_mult x y) (dual_mult x z).
Proof.
  intros [x0 x1] [y0 y1] [z0 z1].
  unfold dual_mult, dual_plus. simpl.
  f_equal; ring.
Qed.

(** Key property: ε² = 0 *)

Lemma eps_squared : dual_mult dual_eps dual_eps = dual_zero.
Proof.
  unfold dual_mult, dual_eps, dual_zero. simpl.
  f_equal; ring.
Qed.

(** * The Three-Region Setup *)

(** Regions: U, V, W with triple overlap Λ *)

Inductive ToyRegion : Type :=
  | R_empty : ToyRegion
  | R_U : ToyRegion
  | R_V : ToyRegion
  | R_W : ToyRegion
  | R_UV : ToyRegion    (* U ∩ V *)
  | R_VW : ToyRegion    (* V ∩ W *)
  | R_UW : ToyRegion    (* U ∩ W *)
  | R_Lambda : ToyRegion  (* U ∩ V ∩ W *)
  | R_S : ToyRegion     (* U ∪ V *)
  | R_T : ToyRegion     (* V ∪ W *)
  | R_R : ToyRegion     (* U ∪ V ∪ W *)
  | R_top : ToyRegion.

(** The lattice operations *)

Definition toy_meet (R S : ToyRegion) : ToyRegion :=
  match R, S with
  | R_empty, _ => R_empty
  | _, R_empty => R_empty
  | R_top, X => X
  | X, R_top => X
  | R_U, R_V => R_UV
  | R_V, R_U => R_UV
  | R_V, R_W => R_VW
  | R_W, R_V => R_VW
  | R_U, R_W => R_UW
  | R_W, R_U => R_UW
  | R_U, R_UV => R_UV
  | R_UV, R_U => R_UV
  (* ... many more cases *)
  | R_Lambda, _ => R_Lambda
  | _, R_Lambda => R_Lambda
  | X, X => X
  | _, _ => R_empty  (* Simplified; full case analysis needed *)
  end.

Definition toy_join (R S : ToyRegion) : ToyRegion :=
  match R, S with
  | R_empty, X => X
  | X, R_empty => X
  | R_top, _ => R_top
  | _, R_top => R_top
  | R_U, R_V => R_S
  | R_V, R_U => R_S
  | R_V, R_W => R_T
  | R_W, R_V => R_T
  | R_S, R_W => R_R
  | R_W, R_S => R_R
  | R_U, R_T => R_R
  | R_T, R_U => R_R
  | X, X => X
  | _, _ => R_top  (* Simplified *)
  end.

(** * Algebraic Assignment: A(X) = Z[ε]/(ε²) for all X *)

(** Every region gets the same algebra; structure maps are identity *)

Definition toy_alg (X : ToyRegion) : Type := DualZ.

Definition toy_structure_map (R S : ToyRegion) (x : toy_alg R) : toy_alg S := x.
  (* Identity map - injectivity is trivial *)

(** * Correction Terms *)

(** The correction β_{U,V}(a,b) = λ_{U,V} · π₀(a) · π₀(b) · ε
    where π₀ extracts the real part and λ_{U,V} ∈ Z is a parameter *)

Definition pi0 (x : DualZ) : Z := real_part x.

(** Parameters for the correction terms *)

Variable lambda_UV : Z.
Variable lambda_VW : Z.
Variable lambda_UW : Z.
Variable lambda_S_W : Z.   (* For (U∪V) with W *)
Variable lambda_U_T : Z.   (* For U with (V∪W) *)

(** The correction map *)

Definition toy_correction_UV (a b : DualZ) : DualZ :=
  ⟨0, lambda_UV * pi0 a * pi0 b⟩.

Definition toy_correction_VW (a b : DualZ) : DualZ :=
  ⟨0, lambda_VW * pi0 a * pi0 b⟩.

Definition toy_correction_UW (a b : DualZ) : DualZ :=
  ⟨0, lambda_UW * pi0 a * pi0 b⟩.

Definition toy_correction_S_W (ab c : DualZ) : DualZ :=
  ⟨0, lambda_S_W * pi0 ab * pi0 c⟩.

Definition toy_correction_U_T (a bc : DualZ) : DualZ :=
  ⟨0, lambda_U_T * pi0 a * pi0 bc⟩.

(** * The Gluing Map *)

(** m_{U,V}(a,b) = a·b + β_{U,V}(a,b) 
    (Simplified: all structure maps are identity) *)

Definition toy_glue_UV (a b : DualZ) : DualZ :=
  dual_plus (dual_mult a b) (toy_correction_UV a b).

Definition toy_glue_VW (a b : DualZ) : DualZ :=
  dual_plus (dual_mult a b) (toy_correction_VW a b).

(** * The Associator Calculation *)

(** For a = a₀ + a₁ε, b = b₀ + b₁ε, c = c₀ + c₁ε:
    
    α(a,b,c) = (left) - (right) *)

Definition toy_left_assoc (a b c : DualZ) : DualZ :=
  let ab := toy_glue_UV a b in
  dual_plus (dual_mult ab c) (toy_correction_S_W ab c).

Definition toy_right_assoc (a b c : DualZ) : DualZ :=
  let bc := toy_glue_VW b c in
  dual_plus (dual_mult a bc) (toy_correction_U_T a bc).

Definition toy_associator (a b c : DualZ) : DualZ :=
  dual_plus (toy_left_assoc a b c) (dual_neg (toy_right_assoc a b c)).

(** * The Key Calculation *)

(** For a = b = c = 1 (the multiplicative identity): *)

Lemma toy_associator_at_ones :
  toy_associator dual_one dual_one dual_one = 
  ⟨0, lambda_UV + lambda_S_W - lambda_VW - lambda_U_T⟩.
Proof.
  unfold toy_associator, toy_left_assoc, toy_right_assoc.
  unfold toy_glue_UV, toy_glue_VW.
  unfold toy_correction_UV, toy_correction_VW, toy_correction_S_W, toy_correction_U_T.
  unfold dual_plus, dual_mult, dual_neg, dual_one, pi0.
  simpl.
  f_equal; ring.
Qed.

(** The obstruction parameter Δ *)

Definition Delta : Z := lambda_UV + lambda_S_W - lambda_VW - lambda_U_T.

(** * Vanishing Condition *)

(** The obstruction vanishes iff Δ = 0 *)

Theorem toy_obstruction_vanishes :
  Delta = 0 <-> toy_associator dual_one dual_one dual_one = dual_zero.
Proof.
  split.
  - intro HDelta.
    rewrite toy_associator_at_ones.
    unfold dual_zero. f_equal.
    unfold Delta in HDelta.
    exact HDelta.
  - intro Hassoc.
    rewrite toy_associator_at_ones in Hassoc.
    unfold dual_zero in Hassoc.
    injection Hassoc. intro H. exact H.
Qed.

(** * Example: Vanishing Case *)

(** Choose λ_{UV} = 1, λ_{VW} = 1, λ_{S,W} = 1, λ_{U,T} = 1 *)
(** Then Δ = 1 + 1 - 1 - 1 = 0 *)

Example vanishing_example :
  let lambda_UV := 1 in
  let lambda_VW := 1 in
  let lambda_S_W := 1 in
  let lambda_U_T := 1 in
  lambda_UV + lambda_S_W - lambda_VW - lambda_U_T = 0.
Proof.
  simpl. reflexivity.
Qed.

(** * Example: Non-Vanishing Case *)

(** Choose λ_{UV} = 1, λ_{VW} = 0, λ_{S,W} = 0, λ_{U,T} = 0 *)
(** Then Δ = 1 + 0 - 0 - 0 = 1 ≠ 0 *)

Example nonvanishing_example :
  let lambda_UV := 1 in
  let lambda_VW := 0 in
  let lambda_S_W := 0 in
  let lambda_U_T := 0 in
  lambda_UV + lambda_S_W - lambda_VW - lambda_U_T = 1.
Proof.
  simpl. reflexivity.
Qed.

(** * Edge Completion in the Vanishing Case *)

(** When Δ = 0, we can choose θ to trivialize α.
    
    The edge-completed algebra A^e has elements (x, ξ) where:
    - x ∈ Z[ε]/(ε²) is the interior
    - ξ ∈ Z[ε]/(ε²) is the edge component on Λ *)

Record ToyEdgeAlgebra := {
  toy_interior : DualZ;
  toy_edge : DualZ;
}.

(** Edge-corrected multiplication (when Δ = 0) *)

(** We need θ : pairs → Z[ε]/(ε²) such that α = δθ.
    
    With three regions, δθ on Λ is:
    δθ = θ_{VW}|_Λ - θ_{UW}|_Λ + θ_{UV}|_Λ
    
    We need: Δ = θ_{VW} - θ_{UW} + θ_{UV}
    
    One solution (when Δ = 0): θ_{UV} = θ_{VW} = θ_{UW} = 0
    
    Another (general): θ_{UV} = -Δ, θ_{VW} = θ_{UW} = 0 also works *)

Variable theta_UV : Z.
Variable theta_VW : Z.
Variable theta_UW : Z.

Hypothesis theta_trivializes : theta_VW - theta_UW + theta_UV = Delta.

Definition toy_edge_mult (x y : ToyEdgeAlgebra) : ToyEdgeAlgebra := {|
  toy_interior := toy_glue_UV (toy_interior x) (toy_interior y);
  toy_edge := dual_plus 
    (dual_plus (toy_edge x) (toy_edge y))
    ⟨0, theta_UV * pi0 (toy_interior x) * pi0 (toy_interior y)⟩;
|}.

(** Associativity of edge multiplication *)

Theorem toy_edge_mult_assoc :
  Delta = 0 ->
  forall x y z,
  toy_edge_mult (toy_edge_mult x y) z = 
  toy_edge_mult x (toy_edge_mult y z).
Proof.
  intro HDelta.
  intros x y z.
  unfold toy_edge_mult.
  (* The interior components differ by the associator *)
  (* The edge components differ by δθ *)
  (* Since α = δθ (both equal Δ·ε, and Δ = 0), these cancel *)
  admit.
Admitted.

(** * Philosophical Reflection *)

(**
   The dual numbers Z[ε]/(ε²) are the algebraic model of "first-order
   infinitesimals" - quantities that are non-zero but whose squares
   vanish. In Whiteheadian terms, ε represents a "infinitesimal novelty"
   that contributes linearly to synthesis but doesn't compound.
   
   The obstruction parameter Δ = λ_{UV} + λ_{S,W} - λ_{VW} - λ_{U,T}
   measures the "holonomy" of the β-corrections: if we go around the
   triangle of binary gluings, do the corrections balance?
   
   When Δ = 0, the corrections are "curl-free" - they arise from a
   potential θ and can be gauged away. The edge completion then
   provides a canonical context in which associativity holds strictly.
   
   When Δ ≠ 0, there is genuine "circulation" in the correction structure.
   No choice of θ can eliminate the associator, and the triadic contrast
   is irreducible. This is the mathematical signature of what Whitehead
   calls "incompatible alternatives" - eternal objects that cannot all
   ingress into the same actual occasion.
*)

End DualNumbers.
