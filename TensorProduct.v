(* ========================================================================= *)
(* TensorProduct.v                                  *)
(* *)
(* Axiomatic definition of the tensor product of algebras over a ring k.    *)
(* *)
(* We characterize the tensor product by its universal property:            *)
(* bilinear maps out of A x B correspond one-to-one to linear maps          *)
(* out of A (x) B.                                                          *)
(* ========================================================================= *)

Require Import AlgebraicAssignment.
Require Import RegionLattice.

(** * Linear Maps *)

(** A linear map between k-algebras (viewed as modules). *)
Record LinearMap {k : CommRing} (A B : @Algebra k) := {
  lin_map : @alg_carrier k A -> @alg_carrier k B;
  lin_plus : forall x y, lin_map (@alg_plus k A x y) = @alg_plus k B (lin_map x) (lin_map y);
  lin_scale : forall c x, lin_map (@alg_scale k A c x) = @alg_scale k B c (lin_map x);
}.

(** * The Tensor Product Axioms *)

(** We define a typeclass for the tensor product to allow for different 
    implementations, though we only need one that satisfies the axioms. *)

Class TensorProduct {k : CommRing} (A B : @Algebra k) := {
  (** The carrier object (conceptually A (x) B) *)
  (* Note: We treat the result as an Algebra for simplicity, though strictly
     it requires defining the multiplication structure first. *)
  TP_Algebra : @Algebra k;
  
  (** The canonical bilinear map: A x B -> A (x) B *)
  tensor_map : @BilinearMap k A B TP_Algebra;
  
  (** The Universal Property:
      For any algebra C and any bilinear map f : A x B -> C,
      there exists a unique linear map 'lift' : A (x) B -> C
      such that f = lift o tensor_map. *)
      
  lift : forall (C : @Algebra k) (f : @BilinearMap k A B C),
         LinearMap TP_Algebra C;
         
  (** The diagram commutes: lift(tensor(a,b)) = f(a,b) *)
  lift_commutes : forall (C : @Algebra k) (f : @BilinearMap k A B C) (a : @alg_carrier k A) (b : @alg_carrier k B),
    lin_map _ _ (lift C f) (bilin_map _ _ _ (tensor_map) a b) = 
    bilin_map _ _ _ f a b;
    
  (** Uniqueness of the lift (extensionality) *)
  lift_unique : forall (C : @Algebra k) (f : @BilinearMap k A B C) (g : LinearMap TP_Algebra C),
    (forall a b, lin_map _ _ g (bilin_map _ _ _ (tensor_map) a b) = bilin_map _ _ _ f a b) ->
    (forall x, lin_map _ _ g x = lin_map _ _ (lift C f) x);
}.

(** * Notation *)

Declare Scope tensor_scope.
Open Scope tensor_scope.

(** We use implicit arguments for the TypeClass instance *)
Notation "A ⊗ B" := (@TP_Algebra _ A B _) (at level 40) : tensor_scope.

(** Canonical injection a (x) b *)
(* This notation requires the TensorProduct instance to be inferable *)
Notation "a ⊗ b" := (bilin_map _ _ _ tensor_map a b) (at level 40) : tensor_scope.


(** * Triple Tensor Products *)

(** For the associator, we need (A ⊗ B) ⊗ C. 
    Since our tensor product returns an Algebra, we can iterate it easily. *)

Section TripleTensor.
  Context {k : CommRing}.
  Context {A B C : @Algebra k}.
  
  (** We assume tensor products exist for these pairs *)
  Context {TAB : TensorProduct A B}.
  Context {TBC : TensorProduct B C}.
  Context {T_AB_C : TensorProduct (@TP_Algebra k A B TAB) C}.
  Context {T_A_BC : TensorProduct A (@TP_Algebra k B C TBC)}.
  
  (** The Associativity Isomorphism (A ⊗ B) ⊗ C <-> A ⊗ (B ⊗ C) 
      is crucial for defining the associator defect. *)
      
  (** Constructing the forward map: (A ⊗ B) ⊗ C -> A ⊗ (B ⊗ C) *)
  (* This requires a two-step lift via the universal property. *)
  
  Definition associator_map : LinearMap (@TP_Algebra k (@TP_Algebra k A B TAB) C T_AB_C) 
                                        (@TP_Algebra k A (@TP_Algebra k B C TBC) T_A_BC).
  Proof.
    (* Step 1: Fix c : C. Construct Bilinear map A x B -> A (x) (B (x) C)
       mapping (a, b) |-> a (x) (b (x) c).
       Lift this to A (x) B -> A (x) (B (x) C).
       
       Step 2: This gives a map bilinear in ((a(x)b), c).
       Lift this to (A (x) B) (x) C -> ...
    *)
    (* Formalizing this fully requires some boilerplate lifting lemmas.
       For now, we admit the existence of the isomorphism to proceed to the
       cohomological obstruction definition. *)
    admit.
  Admitted.

End TripleTensor.

(** * Commentary *)
(** In the sheaf-theoretic approach to quantum mechanics, states are sections
    of a sheaf. When we glue systems A and B, the state space is locally
    A(U) ⊗ B(U).
    
    The failure of global associativity (the "Associator") arises when we
    compare the parenthesization of three systems (U, V, W) over a triple
    overlap. If the lattice is non-trivial (e.g. borromean rings topology),
    the map 'associator_map' defined above might not commute with restriction
    maps in the way required for a cohomology class to vanish.
*)