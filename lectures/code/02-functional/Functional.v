(* Every Rocq snippet shown in lecture 2 (functional programming).
   Compile: nix develop -c rocq compile rocq/Functional.v *)
From Coq Require Import String List.
Import ListNotations.
Open Scope string_scope.

(* Values and functions *)
Check 5.
Check true.
Check "fcplcd".
Check tt.
Definition add (x y : nat) : nat := x + y.
Check add.
Check (fun x y => x + y).
Check (fun (x y : nat) => x + y).

(* Bindings *)
Print add.
Compute add 2 3.
Compute let x := 5 in x.
Compute let add := fun x y => x + y in add 2 3.
Compute let add x y := x + y in add 2 3.

(* Application and currying *)
Check add 2.
Compute add 2.
Compute (fun x => fun y => x + y) 1 2.

(* Products, sums, lists *)
Check (1, "one").
Check (inl 1 : nat + string).
Check (inr "one" : nat + string).
Check [1; 2; 3].
Definition add_pair (p : nat * nat) : nat := let (x, y) := p in x + y.
Definition add_curried := fun x => fun y => add_pair (x, y).
Compute add_curried 1 2.
Check (fun '(x, y) => x + y).
Check (fun x => fun y => x + y).

(* Polymorphism: types are arguments *)
Definition id (A : Type) (x : A) : A := x.
Compute id nat 5.
Definition id' {A : Type} (x : A) : A := x.
Compute id' 5.
Definition swap {A B : Type} (p : A * B) : B * A :=
  let (x, y) := p in (y, x).
Check @swap.
Compute swap (1, "one").

(* Inductive types *)
Module Defs.
  Inductive bool : Type := true | false.
  Inductive sum (A B : Type) : Type :=
  | inl : A -> sum A B
  | inr : B -> sum A B.
  Inductive list (A : Type) : Type :=
  | nil : list A
  | cons : A -> list A -> list A.
  Check cons.
End Defs.

(* Pattern matching and recursion *)
Fixpoint zeros (l : list nat) : nat :=
  match l with
  | [] => 0
  | x :: xs => (if Nat.eqb x 0 then 1 else 0) + zeros xs
  end.
Compute zeros [0; 3; 0; 7].

Fixpoint zeros' (l : list nat) : nat :=
  match l with
  | [] => 0
  | x :: xs => (match Nat.eqb x 0 with
                | true => 1
                | false => 0
                end) + zeros' xs
  end.

(* Totality *)
Fail Fixpoint loop (n : nat) : nat := loop n.
Fail Definition pred (n : nat) : nat := match n with S m => m end.
Fail Fixpoint bad (n : nat) : False := bad n.

(* Type inference *)
Check (fun (x : nat) => x + 1) : nat -> nat.
Check (fun x => x + 1).
Check (fun x => x).

Close Scope string_scope.

(* Proving about programs: equational reasoning *)
Fixpoint rev {A : Type} (l : list A) : list A :=
  match l with
  | [] => []
  | x :: xs => rev xs ++ [x]
  end.

Lemma rev_singleton : forall (A : Type) (x : A), rev [x] = [x].
Proof. reflexivity. Qed.

Search (_ + 0 = _).

(* Structural induction *)
Check list_ind.

Lemma app_nil_r' : forall (A : Type) (l : list A), l ++ [] = l.
Proof.
  intros A l. induction l as [| x xs IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma app_assoc' : forall (A : Type) (l1 l2 l3 : list A),
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros A l1 l2 l3. induction l1 as [| x xs IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma rev_app : forall (A : Type) (l1 l2 : list A),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros A l1 l2. induction l1 as [| x xs IH].
  - simpl. rewrite app_nil_r'. reflexivity.
  - simpl. rewrite IH. rewrite app_assoc'. reflexivity.
Qed.

Theorem rev_involutive : forall (A : Type) (l : list A), rev (rev l) = l.
Proof.
  intros A l. induction l as [| x xs IH].
  - reflexivity.
  - simpl. rewrite rev_app. simpl. rewrite IH. reflexivity.
Qed.

(* As written on the slides: rev without a return type, and a type of terms. *)
Module SlideVersions.
  Fixpoint rev {A : Type} (l : list A) :=
    match l with
    | []      => []
    | x :: xs => rev xs ++ [x]
    end.
  Inductive term := Zero | Succ (t : term) | Add (t1 t2 : term).
  Check term_ind.
End SlideVersions.
