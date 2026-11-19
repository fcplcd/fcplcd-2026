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
  - reflexivity.
  - cbn.
    rewrite rev_helper.
    rewrite IHa.
    cbn.
    easy.
Qed.

Inductive tree :=
  | Leaf (v : nat) : tree
  | Node (c : list tree) : tree.

Check tree_ind.

Inductive tree2 :=
 | leaf : tree2
 | node (left : tree2) (n : nat) (right : tree2) : tree2.

Check tree2_ind.

Fixpoint size' t : nat :=
  match t with
  | Leaf _ => 1
  | Node ts => list_sum (map size' ts)
  end.

Definition subtract_1 (n : nat) (H : n >= 1) : nat.
  destruct n as [| n'].
  - lia.
  - exact n'.
Defined.

From Corelib Require Extraction.

(* note how the proof is completely removed from the extracted ocaml *)
Extraction subtract_1.

(* Compute (subtract_1 5 (ltac:(lia) : 5 >= 1)). *)

(* Print subtract_1. *)

(* Definition subtract_1 (n : nat) (H : n >= 1) : nat :=
  match n with
  | 0 => ... contradiction
  | S n => n
  end. *)


Definition example (A B : Prop) : A ∧ B -> A :=
  fun Hab =>
    match Hab with
    | conj a b => a
    end.

Fixpoint mirror (t : tree) : tree :=
  match t with
  | Leaf x => Leaf x
  | Node ts => Node (rev (map mirror ts))
  end.

Definition mirror' (t : tree) : tree.
  destruct t as [x | ts].
  - exact (Leaf x).
  - exact (Node (rev ts)).
Defined.

Print mirror'.

Check tree_ind.

(* A stronger induction principle which
 * gives the induction hypothesis an additional assumption
 *)
Lemma tree_ind_full (P : tree -> Prop) :
  (∀ v, P (Leaf v)) ->
  (∀ c, (∀ t, In t c -> P t) -> P (Node c)) ->
  ∀ t, P t.
Proof.
  intros Hleaf Hnode.
  fix IH 1.
  intro t.
  destruct t as [v | c].
  - apply Hleaf.
  - apply Hnode.
    induction c as [|t' c' IHc]; intros t Hin.
    + contradict Hin.
    + destruct Hin as [<- | Hin].
      * apply IH.
      * apply IHc. exact Hin.
Qed.

Fixpoint tree_ind_full_fixpoint (P : tree -> Prop)
  (Hleaf : ∀ v, P (Leaf v))
  (Hnode : ∀ c, (∀ t, In t c -> P t) -> P (Node c))
  : ∀ t, P t.
Proof.
  specialize (tree_ind_full_fixpoint P Hleaf Hnode).
  destruct t as [v | c].
  - apply Hleaf.
  - apply Hnode.
    induction c as [|t' c' IHc]; intros t Hin.
    + contradict Hin.
    + destruct Hin as [<- | Hin].
      * apply tree_ind_full_fixpoint.
      * apply IHc. exact Hin.
Qed.

(* a more general version
 * with an arbitrary proposition over tree-lists `Pl`
 *)
Lemma tree_list_ind (P : tree -> Prop) (Pl : list tree -> Prop) :
  (∀ v, P (Leaf v)) →
  (∀ c, Pl c -> P (Node c)) ->

  (Pl []) ->
  (∀ t l, P t -> Pl l -> Pl (t :: l)) ->

  ((∀ t, P t) ∧ (∀ tl, Pl tl)).
Proof.
  intros Hleaf Hnode Hnil Hcons.
  assert (Hlist : (∀ t, P t) -> (∀ tl, Pl tl)).
  { intros H tl.
    induction tl as [| t tl' IHl].
    - easy.
    - apply Hcons. apply H. apply IHl. }
  assert (Htree : ∀ t, P t).
  { fix IH 1; intros t.
    destruct t as [v | c].
    - easy.
    - apply Hnode, Hlist, IH. }
  split.
  - apply Htree.
  - apply Hlist, Htree.
Qed.



Lemma list_sum_cons a l :
  list_sum (a :: l) = a + list_sum l.
Proof. reflexivity. Qed.

Lemma foldr_add_const m n l :
  foldr Nat.add (m + n) l = m + foldr Nat.add n l.
Proof.
  induction l as [| a l' IH]; first easy.
  cbn. rewrite IH.
  lia.
Qed.

Lemma list_sum_rev l :
  list_sum (rev l) = list_sum l.
Proof.
  unfold list_sum. generalize 0.
  induction l as [| a l' IH]; intros n; first easy.
  cbn. rewrite foldr_snoc, IH.
  rewrite foldr_add_const.
  lia.
Qed.

(* with this induction principle we need to specify
  the list property ourself (i.e.
    Pl :=
      fun tl => map size' tl = map size' (map mirror tl)
  ) however, as a result the proof feels a bit easier *)
Lemma size_mirror :
  (∀ t, size' t = size' (mirror t)) ∧
  (∀ tl, map size' tl = map size' (map mirror tl)).
Proof.
  apply tree_list_ind.
  (* tree base case *)
  - easy.
  (* tree induction case *)
  - intros c Htl. cbn.
    rewrite map_rev, list_sum_rev, <- Htl.
    reflexivity.
  (* list base case *)
  - easy.
  (* list induction case *)
  - intros t tl' Ht Htl'. cbn.
    rewrite <- Ht, <- Htl'.
    reflexivity.
Qed.

Lemma size_mirror_again t : size' t = size' (mirror t).
Proof.
  induction t using tree_ind_full.
  (* tree base case *)
  - easy.
  (* here the list induction is not build into the
      induction principle so we need to do it manually
      in the proof *)
  (* tree induction case *)
  - induction c.
    (* list base case *)
    + easy.
    (* list induction case *)
    + cbn -[list_sum]; rewrite list_sum_cons. (* cautious reduction to keep `list_sum` *)
      rewrite map_app, list_sum_app. cbn.
      rewrite map_rev, list_sum_rev. (* notice: this part is identical to the proof above*)
      rewrite <- H by apply in_eq. (* this corresponds to `rewrite <- Ht` above *)
      (* `rewrite <- Htl'` is hard in this proof as we need to establish the
          necessary tree-list property first *)
      (* the problem here is that the tree-list property we need and the one that we've got
          (from our induction principle) are logically equivalent but not identical.
          Thus we need to derive the one we need first.

        we need: map size' c = map size' (map mirror c)
        we got : ∀ t, In t (a :: c) → size' t = size' (mirror t) *)
      assert (Htl : map size' c = map size' (map mirror c)).
      { clear IHc. (* we dont need that here - bacially this assertion could be a separate lemma *)
        induction c.
        - easy.
        - cbn. rewrite H, IHc. reflexivity.
          + intros t Hin. apply H. clear H IHc.
            cbn [In] in *. (* look at the definition of `In` the element is either the first or `In` the tail *)
            destruct Hin.
            * left. assumption.
            * right. right. assumption.
          + cbn [In]. right. left. reflexivity. }
      (* not that we have derived Htl, we can finish the proof similar to `size_mirror` *)
      rewrite <- Htl.
      lia. (* add commutativity and associativity is handled automatically by `lia` *)
Qed.

