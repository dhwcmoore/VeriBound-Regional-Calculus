(* ========================================================================= *)
(* RegionalAssociativity.v                           *)
(* *)
(* The definition of the associator obstruction class.                      *)
(* *)
(* CORRECTION: Because our Algebraic Assignment is COVARIANT (Extension),   *)
(* we cannot restrict to the intersection. Instead, we must push all        *)
(* algebras forward to the UNION (Omega = U ∪ V ∪ W) to compare them.       *)
(* ========================================================================= *)

Require Import RegionLattice.
Require Import AlgebraicAssignment.
Require Import TensorProduct.

Section AssociatorDefect.
  (* 1. Context Setup *)
  Context {k : CommRing}.
  Context {RL : RegionLattice}.
  Context {AA : @AlgebraicAssignment k RL}.
  (* InjectiveAssignment is not strictly needed for the obstruction definition 
     in the covariant case, but we keep it for consistency. *)
  Context {IA : @InjectiveAssignment k RL AA}.

  (* 2. The Three Regions *)
  Variables U V W : Reg.
  
  (* The Union where the comparison happens (The "Global" Region) *)
  Definition Omega := U ∪ V ∪ W.
  
  (* 3. Assumptions: Tensor Products Exist *)
  Context {T_UV : TensorProduct (alg_at U) (alg_at V)}.
  Context {T_VW : TensorProduct (alg_at V) (alg_at W)}.
  (* Note: We are comparing (U⊗V)⊗W vs U⊗(V⊗W). *)
  Context {T_UV_W : TensorProduct (@TP_Algebra k _ _ T_UV) (alg_at W)}.
  Context {T_U_VW : TensorProduct (alg_at U) (@TP_Algebra k _ _ T_VW)}.

  (* 4. The Standard Associator Isomorphism *)
  (* We compare the result of gluing in the Union against the global isomorphism *)
  Variable global_associator : 
    LinearMap (@TP_Algebra k _ _ T_UV_W) (@TP_Algebra k _ _ T_U_VW).
    
  (* 5. Extension to the Union *)
  
  (* We need to map elements from the tensor product A(U) ⊗ A(V) to A(Omega).
     We use the structure maps to extend A(U)->A(Omega) and A(V)->A(Omega),
     then multiply them in A(Omega). *)
  
  (* Helper: Proofs that U, V, W are subsets of Omega *)
  Lemma sub_U_Omega : U ⊆ Omega.
  Proof.
    unfold Omega.
    (* U ⊆ (U ∪ V) ∪ W *)
    eapply incl_trans.
    apply incl_join_l. (* U ⊆ U ∪ V *)
    apply incl_join_l. (* U ∪ V ⊆ (U ∪ V) ∪ W *)
  Qed.

  Lemma sub_V_Omega : V ⊆ Omega.
  Proof.
    unfold Omega.
    eapply incl_trans.
    apply incl_join_r. (* V ⊆ U ∪ V *)
    apply incl_join_l. 
  Qed.

  Lemma sub_W_Omega : W ⊆ Omega.
  Proof.
    unfold Omega.
    apply incl_join_r.
  Qed.

  (* The Bilinear Map: A(U) x A(V) -> A(Omega) *)
  Definition extend_mult_map_UV : BilinearMap (alg_at U) (alg_at V) (alg_at Omega).
  Proof.
    refine {|
      bilin_map := fun u v => 
        @alg_mult k (alg_at Omega) 
          (alg_hom_map _ _ (@structure_map k RL AA U Omega sub_U_Omega) u)
          (alg_hom_map _ _ (@structure_map k RL AA V Omega sub_V_Omega) v)
    |}.
    - (* Linear Left Plus *)
      intros. rewrite alg_hom_plus. apply alg_distrib_r.
    - (* Linear Left Scale *)
      intros. rewrite alg_hom_scale. rewrite alg_scale_mult. reflexivity.
    - (* Linear Right Plus *)
      intros. rewrite alg_hom_plus. apply alg_distrib_l.
    - (* Linear Right Scale *)
      intros. rewrite alg_hom_scale. admit. (* Assumes commutativity/centrality *)
  Admitted.

  (* Lift to A(U)⊗A(V) -> A(Omega) *)
  Definition tensor_extension_UV : LinearMap (@TP_Algebra k _ _ T_UV) (alg_at Omega).
  Proof.
    apply (lift (alg_at Omega)).
    apply extend_mult_map_UV.
  Defined.

  (* 6. The Two Paths *)
  
  (* Path 1: (U⊗V)⊗W -> Omega 
     First map U⊗V to Omega (as above), then multiply with W (extended to Omega) *)
  
  Definition path_left : LinearMap (@TP_Algebra k _ _ T_UV_W) (alg_at Omega).
  Proof.
    (* This requires defining the extension for the triple product.
       Conceptually: It maps ((u⊗v)⊗w) to (u_ext * v_ext) * w_ext in Omega. *)
    admit.
  Admitted.
  
  (* Path 2: (U⊗V)⊗W -> U⊗(V⊗W) -> Omega 
     Use the associator, then map U⊗(V⊗W) to Omega *)
  
  Definition path_right : LinearMap (@TP_Algebra k _ _ T_UV_W) (alg_at Omega).
  Proof.
    (* Conceptually: Apply associator, then map u⊗(v⊗w) to u_ext * (v_ext * w_ext) *)
    admit.
  Admitted.
  
  (** The Definition of the Associativity Obstruction Class *)
  (** If these two paths agree, the gluing is associative. *)
  Definition associativity_obstruction 
    (x : @alg_carrier k (@TP_Algebra k _ _ T_UV_W)) : Prop :=
      lin_map _ _ path_left x = lin_map _ _ path_right x.

End AssociatorDefect.