Axiom TODO : forall {A}, A. (* <- remove this line once your are done *)
From Stdlib Require Import Utf8.

(* ================================================================ *)
(*                       Defining the Syntax                        *)
(* ================================================================ *)

(* Define the abstract syntax of FCPLang *)

Inductive FCPTerm : Type :=
(* TODO *).

(* Check (boolT true).
Check (iteT (boolT true) (natT 1) (boolT false)).
Check (iteT (iteT (natT 1) (boolT true) (boolT false)) (natT 2) (natT 3)). *)

(* ================================================================ *)
(*                 Defining Semantics as a Relation                 *)
(* ================================================================ *)

(* Single-Step *)
Inductive Eval_1 : FCPTerm -> FCPTerm -> Prop :=
  | E_If_True : forall ta tb,
      Eval_1 (iteT (boolT true) ta tb) ta 
  (* ... TODO *).

Notation "ta '→1' tb" := (Eval_1 ta tb) (at level 60).

(* Multi-Step: define the reflexive and transitive closure *)
Inductive Eval_n : FCPTerm -> FCPTerm -> Prop := 
  (* TODO *).

Notation "t1 '→n' t2" := (Eval_n t1 t2) (at level 60).

(* Prove the transitivity theorem *)
Theorem Eval_n_trans: forall t1 t2 t3,
  t1 →n t2 ->
  t2 →n t3 ->
  t1 →n t3.
Proof. 
  (* TODO *)
Admitted.

(* ================================================================ *)
(*                           Normal Forms                           *)
(* ================================================================ *)

(* Define an isNF predicate on FCPLang terms *)

Definition isNF (t : FCPTerm) : Prop :=
  TODO.

(* Uniqueness and Termination
 *
 * Prove that every FCPLang term has at most one normal form *)
Corollary single_step_deterministic: forall t t1 t2,
  t →1 t1 ->
  t →1 t2 ->
  t1 = t2.
Proof. 
  (* TODO *)
Admitted.

Theorem NF_unique: ∀ t nf1 nf2,
  t →n nf1 ->
  t →n nf2 ->
  isNF nf1 ->
  isNF nf2 ->
  nf1 = nf2.
Proof. 
  (* TODO *)
Admitted.



(* Termination (optional): prove that our evaluation terminates
 * Caution: This one is hard!
 *)
Theorem Eval_n_has_NF :
  ∀ t, ∃ nf,
    t →n nf /\
    isNF nf.
Proof. 
  (* TODO *)
Admitted.

(* ================================================================ *)
(*                              Values                              *)
(* ================================================================ *)

(* Values (optional): define the notion of 'values'
 * Decide to either use a definition or an Inductive
 *)
Inductive isVal : FCPTerm -> Prop :=
  (* TODO *).

Definition isVal (t : FCPTerm) : Prop :=
  TODO.

(* Values (optional): show that all values are normal forms *)
Theorem isVal_isNF :
  ∀ t, isVal t -> isNF t.
Proof. 
  (* TODO *)
Admitted.

(* Values (optional): show some normal forms are not values *)
Theorem isNF_isVal_neg :
  ¬ (∀ t, isNF t -> isVal t).
Proof. 
  (* TODO *)
Admitted.