Require Import Utf8.
Require Import List.
Import ListNotations.

From stdpp Require Import prelude.

(* flip involutive flip_involutive foldlr foldrl *)

Definition involutive {A} (f : A -> A) := ∀ a, f (f a) = a.

About rev.

Lemma rev_helper {A} (x : A) (xs : list A) :
  rev (xs ++ [x]) = x :: rev xs.
Proof.
  induction xs.
  easy.
  cbn.
  rewrite IHxs.
  cbn.
  easy.
Qed.

Lemma rev_involutive {A} : ∀ (a : list A), rev (rev a) = a.
Proof.
  intro.
  induction a.
  reflexivity.
  cbn.
  rewrite rev_helper.
  rewrite IHa.
  cbn.
  easy.
Qed.

Inductive tree :=
  | Leaf (v : nat) : tree
  | Node (c : list tree) : tree.

Fixpoint size' t : nat :=
  match t with
  | Leaf _ => 1
  | Node ts => foldl Nat.add 0 (map size' ts)
  end.

Fixpoint mirror t :=
  match t with
  | Leaf x => Leaf x
  | Node ts => Node (rev ts)
  end.

Print list_ind.

Lemma size_node t : size' t = size' (mirror t).
Proof.
  induction t.
  easy.
  admit.
Admitted.


