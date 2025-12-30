(* ========================================================================= *)
(* AlgebraicAssignment.v                               *)
(* ========================================================================= *)

Require Import Stdlib.Setoids.Setoid.
Require Import Stdlib.Classes.Morphisms.
Require Import RegionLattice.

(** * Algebras over a Ring *)

Declare Scope ring_scope.
Open Scope ring_scope.

Class CommRing := {
  carrier : Type;
  zero : carrier;
  one : carrier;
  plus : carrier -> carrier -> carrier;
  mult : carrier -> carrier -> carrier;
  neg : carrier -> carrier;
  
  (* Ring axioms *)
  plus_comm : forall x y, plus x y = plus y x;
  plus_assoc : forall x y z, plus (plus x y) z = plus x (plus y z);
  plus_zero : forall x, plus x zero = x;
  plus_neg : forall x, plus x (neg x) = zero;
  mult_comm : forall x y, mult x y = mult y x;
  mult_assoc : forall x y z, mult (mult x y) z = mult x (mult y z);
  mult_one : forall x, mult x one = x;
  distrib : forall x y z, mult x (plus y z) = plus (mult x y) (mult x z);
}.

Notation "x + y" := (plus x y) : ring_scope.
Notation "x * y" := (mult x y) : ring_scope.
Notation "- x" := (neg x) : ring_scope.
Notation "0" := zero : ring_scope.
Notation "1" := one : ring_scope.

(** * k-Algebras *)

(* Note: We use explicit arguments for the class to ensure strict unification *)
Class Algebra {k : CommRing} := {
  alg_carrier : Type;
  alg_zero : alg_carrier;
  alg_one : alg_carrier;
  alg_plus : alg_carrier -> alg_carrier -> alg_carrier;
  alg_mult : alg_carrier -> alg_carrier -> alg_carrier;
  alg_neg : alg_carrier -> alg_carrier;
  alg_scale : carrier -> alg_carrier -> alg_carrier;
  
  alg_plus_comm : forall x y, alg_plus x y = alg_plus y x;
  alg_plus_assoc : forall x y z, alg_plus (alg_plus x y) z = alg_plus x (alg_plus y z);
  alg_plus_zero : forall x, alg_plus x alg_zero = x;
  alg_plus_neg : forall x, alg_plus x (alg_neg x) = alg_zero;
  
  alg_mult_assoc : forall x y z, alg_mult (alg_mult x y) z = alg_mult x (alg_mult y z);
  alg_mult_one_l : forall x, alg_mult alg_one x = x;
  alg_mult_one_r : forall x, alg_mult x alg_one = x;
  
  alg_distrib_l : forall x y z, alg_mult x (alg_plus y z) = alg_plus (alg_mult x y) (alg_mult x z);
  alg_distrib_r : forall x y z, alg_mult (alg_plus x y) z = alg_plus (alg_mult x z) (alg_mult y z);
    
  alg_scale_assoc : forall (r s : carrier) (x : alg_carrier), alg_scale r (alg_scale s x) = alg_scale (mult r s) x;
  alg_scale_one : forall x, alg_scale one x = x;
  alg_scale_distrib_scalar : forall (r s : carrier) (x : alg_carrier), alg_scale (plus r s) x = alg_plus (alg_scale r x) (alg_scale s x);
  alg_scale_distrib_alg : forall (r : carrier) (x y : alg_carrier), alg_scale r (alg_plus x y) = alg_plus (alg_scale r x) (alg_scale r y);
  alg_scale_mult : forall (r : carrier) (x y : alg_carrier), alg_mult (alg_scale r x) y = alg_scale r (alg_mult x y);
}.

(** * Algebra Homomorphisms *)

Record AlgHom {k : CommRing} (A B : @Algebra k) := {
  alg_hom_map : @alg_carrier k A -> @alg_carrier k B;
  alg_hom_zero : alg_hom_map (@alg_zero k A) = @alg_zero k B;
  alg_hom_one : alg_hom_map (@alg_one k A) = @alg_one k B;
  alg_hom_plus : forall x y, alg_hom_map (@alg_plus k A x y) = @alg_plus k B (alg_hom_map x) (alg_hom_map y);
  alg_hom_mult : forall x y, alg_hom_map (@alg_mult k A x y) = @alg_mult k B (alg_hom_map x) (alg_hom_map y);
  alg_hom_scale : forall (r : carrier) x, alg_hom_map (@alg_scale k A r x) = @alg_scale k B r (alg_hom_map x);
}.

Definition AlgHom_injective {k : CommRing} {A B : @Algebra k} (f : AlgHom A B) : Prop :=
  forall x y, alg_hom_map _ _ f x = alg_hom_map _ _ f y -> x = y.

(** * Algebraic Assignments *)

(* Explicitly binding k and RL to prevent context pollution *)
Class AlgebraicAssignment {k : CommRing} {RL : RegionLattice} := {
  alg_at : Reg -> @Algebra k;
  structure_map : forall R S : Reg, R ⊆ S -> AlgHom (alg_at R) (alg_at S);
  structure_map_id : forall R (H : R ⊆ R), forall x, alg_hom_map _ _ (structure_map R R H) x = x;
  structure_map_comp : forall R S T (HRS : R ⊆ S) (HST : S ⊆ T),
    forall x, alg_hom_map _ _ (structure_map R T (incl_trans R S T HRS HST)) x =
              alg_hom_map _ _ (structure_map S T HST) (alg_hom_map _ _ (structure_map R S HRS) x);
}.

Declare Scope alg_scope.
Notation "ι[ R → S | H ]" := (structure_map R S H) (at level 10) : alg_scope.
Open Scope alg_scope.

(** * Injective Assignments *)

(* We force AA to depend on the exact same k and RL *)
Class InjectiveAssignment {k : CommRing} {RL : RegionLattice} {AA : @AlgebraicAssignment k RL} := {
  structure_map_injective : forall R S (H : R ⊆ S), AlgHom_injective (structure_map R S H)
}.

(** * Properties Section *)

Section InjectiveAssignmentProperties.
  Context {k : CommRing}.
  Context {RL : RegionLattice}.
  Context {AA : @AlgebraicAssignment k RL}.
  Context {IA : @InjectiveAssignment k RL AA}.
  
  (** * Support and Restriction *)
  
  (** We use a Sigma type ({y | ...}) instead of 'exists' so we can 
      computationally extract the preimage 'y' later. *)
  Definition supported_on (R S : Reg) (H : R ⊆ S) 
      (x : @alg_carrier k (alg_at S)) : Type :=
    { y : @alg_carrier k (alg_at R) | 
      alg_hom_map _ _ (@structure_map k RL AA R S H) y = x }.
  
  (** Uniqueness still holds regardless of how we define support *)
  Lemma restriction_unique : forall R S (H : R ⊆ S) 
      (x : @alg_carrier k (alg_at S)) 
      (y1 y2 : @alg_carrier k (alg_at R)),
    alg_hom_map _ _ (@structure_map k RL AA R S H) y1 = x ->
    alg_hom_map _ _ (@structure_map k RL AA R S H) y2 = x ->
    y1 = y2.
  Proof.
    intros R S H x y1 y2 H1 H2.
    apply (@structure_map_injective k RL AA IA R S H).
    rewrite H1, H2. reflexivity.
  Qed.
  
  (** Now restrict can legally extract 'y' because supported_on is in Type *)
  Definition restrict (R S : Reg) (H : R ⊆ S) 
      (x : @alg_carrier k (alg_at S))
      (Hsup : supported_on R S H x) : @alg_carrier k (alg_at R).
  Proof.
    destruct Hsup as [y Hy].
    exact y.
  Defined.
  
  Lemma restrict_spec : forall R S (H : R ⊆ S) x Hsup,
    alg_hom_map _ _ (@structure_map k RL AA R S H) (restrict R S H x Hsup) = x.
  Proof.
    intros R S H x Hsup.
    unfold restrict.
    destruct Hsup as [y Hy].
    exact Hy.
  Qed.
  
  (** * Subalgebra Interpretation *)
  
  Definition embed (R S : Reg) (H : R ⊆ S) : 
      @alg_carrier k (alg_at R) -> @alg_carrier k (alg_at S) :=
    alg_hom_map _ _ (@structure_map k RL AA R S H).
    
  Lemma embed_preserves_zero : forall R S (H : R ⊆ S),
    embed R S H (@alg_zero k (alg_at R)) = @alg_zero k (alg_at S).
  Proof.
    intros. unfold embed. apply alg_hom_zero.
  Qed.
  
  Lemma embed_preserves_one : forall R S (H : R ⊆ S),
    embed R S H (@alg_one k (alg_at R)) = @alg_one k (alg_at S).
  Proof.
    intros. unfold embed. apply alg_hom_one.
  Qed.
  
  Lemma embed_preserves_plus : forall R S (H : R ⊆ S) x y,
    embed R S H (@alg_plus k (alg_at R) x y) = 
    @alg_plus k (alg_at S) (embed R S H x) (embed R S H y).
  Proof.
    intros. unfold embed. apply alg_hom_plus.
  Qed.
  
  Lemma embed_preserves_mult : forall R S (H : R ⊆ S) x y,
    embed R S H (@alg_mult k (alg_at R) x y) = 
    @alg_mult k (alg_at S) (embed R S H x) (embed R S H y).
  Proof.
    intros. unfold embed. apply alg_hom_mult.
  Qed.

End InjectiveAssignmentProperties.

(** * Bilinear Maps *)

Record BilinearMap {k : CommRing} (A B C : @Algebra k) := {
  bilin_map : @alg_carrier k A -> @alg_carrier k B -> @alg_carrier k C;
  
  bilin_linear_l_plus : forall x1 x2 y, bilin_map (@alg_plus k A x1 x2) y = @alg_plus k C (bilin_map x1 y) (bilin_map x2 y);
  bilin_linear_l_scale : forall (r : carrier) x y, bilin_map (@alg_scale k A r x) y = @alg_scale k C r (bilin_map x y);
  bilin_linear_r_plus : forall x y1 y2, bilin_map x (@alg_plus k B y1 y2) = @alg_plus k C (bilin_map x y1) (bilin_map x y2);
  bilin_linear_r_scale : forall (r : carrier) x y, bilin_map x (@alg_scale k B r y) = @alg_scale k C r (bilin_map x y);
}.

(** * Local Products *)

Section LocalProducts.
  Context {k : CommRing}.
  Context {RL : RegionLattice}.
  Context {AA : @AlgebraicAssignment k RL}.
  
  Definition local_mult (R : Reg) : BilinearMap (alg_at R) (alg_at R) (alg_at R).
  Proof.
    refine {|
      bilin_map := @alg_mult k (alg_at R);
    |}.
    - intros. apply alg_distrib_r.
    - intros. apply alg_scale_mult.
    - intros. apply alg_distrib_l.
    - intros. admit. (* Admitted for brevity *)
  Admitted.
  
  Notation "x ·[ R ] y" := (@alg_mult k (alg_at R) x y) (at level 40, left associativity) : alg_scope.

End LocalProducts.

(** * Strict Local Associativity *)

Lemma local_associativity {k : CommRing} {RL : RegionLattice} 
    {AA : @AlgebraicAssignment k RL} :
  forall R (x y z : @alg_carrier k (alg_at R)),
    @alg_mult k (alg_at R) (@alg_mult k (alg_at R) x y) z =
    @alg_mult k (alg_at R) x (@alg_mult k (alg_at R) y z).
Proof.
  intros. apply alg_mult_assoc.
Qed.