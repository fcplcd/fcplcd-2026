Axiom TODO : forall {A}, A. (* <- remove this line once your are done *)
(* ================================================================ *)
(*                       Inductive Data Types                       *)
(* ================================================================ *)

(* Natural Numbers *)

(* Define the type `MyNat`, and the terms
 * `one`, `two`, `three` and `four` *)
Inductive MyNat : Set := 
  (* TODO *).

Definition one: MyNat := TODO.
Definition two: MyNat := TODO.
Definition three: MyNat := TODO.
Definition four: MyNat := TODO.

(* Define an addition and a multiplication
 * function for <MyNat> *)

Fixpoint add (n m : MyNat) : MyNat := 
  TODO.

(*
 * You can define your own notations e.g. opertor symbols for function application.
 * Infix notations will require you to define operator precedence and assosiativity.
 * If you are realy curious about Notations, you can read more about it here in our indepth turorial :
 * https://gitlab.barkhauseninstitut.org/versa/learning/-/blob/main/code/demos/notations.v?ref_type=heads
 *)
(* Define the notation `+'` for `add` (at level 50) *)
(* TODO *)

(* You can use the Vernacular command `Compute ...`,
 * to evaluate expressions. Test it with your definitions of
 * addition and two natural numbers you defined
 *)
(* Compute one +' two. *)

(* repeat for multiplication *)

Fixpoint mult (n m : MyNat) : MyNat := 
  TODO.

(* Define the notation `*'` for `mult` (at level 40) *)
(* TODO *)
(* Compute one *' three. *)

(* Trees *)

(* Define a type `NatTree` representing binary trees that store a natural
 * number in each inner node, i.e. a tree is either
 * - an empty leaf `leaf`, or
 * - a node `node l n r` with a left subtree `l`, a value `n` and a right
 *   subtree `r`.
 *)

Inductive NatTree : Set := 
  (* TODO *).

(* An example tree:
 *
 *        two
 *       /   \
 *     one   three
 *              \
 *              four
 *)

(* Example exampleTree : NatTree :=
  node (node leaf one leaf) two (node leaf three (node leaf four leaf)). *)


(* Now define functions on `NatTree` for
 * - calculating its `size`, i.e. the number of nodes
 * - calculating the `sum` of all values stored in the tree
 * - `mirror`ing a tree, i.e. recursively swapping all left and right subtrees
 *)

(* Size function *)
Fixpoint size (t : NatTree) : MyNat := 
  TODO.

(* Sum function *)
Fixpoint sum (t : NatTree) : MyNat := 
  TODO.

(* Mirror function *)
Fixpoint mirror (t : NatTree) : NatTree := 
  TODO.

(* Test your functions on the example tree *)

(* Compute size exampleTree.
Compute sum exampleTree.
Compute mirror exampleTree. *)



(* ================================================================ *)
(*                         Inductive Proofs                         *)
(* ================================================================ *)

(* Rocq derives an induction principle for each inductive type, named after
 * the type with `_ind` appended: *)
Print MyNat_ind.
Print NatTree_ind.

(* Induction on Natural Numbers
 *
 * Prove the following properties of your
 * addition and multiplication functions
 *)

(* Associativity *)

Theorem add_assoc a b c : a +' (b +' c) = (a +' b) +' c.
Proof. 
  (* TODO *)
Admitted.


(* Commutativity *)

(* Hint: If you get stuck, think about establishing some helper lemmas first.
 *   For instance, the definition of addition may give you the equality
 *   `mZero +' m = m`, but what about `n +' mZero = n`?
 *)

Theorem add_comm a b : a +' b = b +' a.
Proof. 
  (* TODO *)
Admitted.


(* Associativity of Multiplication (optional) *)

Theorem mult_assoc a b c : a *' (b *' c) = (a *' b) *' c.
Proof. 
  (* TODO *)
Admitted.



(* Induction on Trees *)

(* Mirror: mirroring is self-inverse
 *
 * Note: Each node has *two* subtrees, so you get *two* induction
 *   hypotheses in the recursive case.
 *)
Theorem mirror_mirror (t : NatTree) :
  mirror (mirror t) = t.
Proof. 
  (* TODO *)
Admitted.

(* Size and Sum (optional): mirroring preserves the size of a tree
 *
 * Hint: The theorems on addition may come in handy.
 *)
Theorem size_mirror (t : NatTree) :
  size (mirror t) = size t.
Proof. 
  (* TODO *)
Admitted.

(* Size and Sum (optional): mirroring preserves the sum of a tree *)
Theorem sum_mirror (t : NatTree) :
  sum (mirror t) = sum t.
Proof. 
  (* TODO *)
Admitted.
