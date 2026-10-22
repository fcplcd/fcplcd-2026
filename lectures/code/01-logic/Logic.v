(* Every Rocq snippet shown in lecture 1 (logic). Compile: rocq compile Logic.v *)

Section Minimal_propositional_logic.
  Variables P Q R : Prop.

  Theorem imp_trans : (P -> Q) -> (Q -> R) -> P -> R.
  Proof.
    intros H H' p.
    apply H'.
    apply H.
    assumption.
  Qed.

  Theorem and_or : P /\ Q -> P \/ Q.
  Proof.
    intros H.
    left.
    destruct H as [p q].
    assumption.
  Qed.

  Theorem or_comm : P \/ Q -> Q \/ P.
  Proof.
    intros H.
    destruct H as [p | q].
    - right. assumption.
    - left. assumption.
  Qed.
End Minimal_propositional_logic.

(* The induction principle Rocq generates for nat. *)
Check nat_ind
  : forall P : nat -> Prop,
      P 0 -> (forall n : nat, P n -> P (S n)) -> forall n : nat, P n.

(* By induction, with tactics. *)
Theorem add_0_r : forall n : nat, n + 0 = n.
Proof.
  induction n as [| n' IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

(* The same proof, written as a recursive function. *)
Fixpoint add_0_r' (n : nat) : n + 0 = n :=
  match n with
  | O    => eq_refl
  | S n' => f_equal S (add_0_r' n')
  end.

(* The note on the Fixpoint slide: congruence, and the reduction it relies on. *)
Check f_equal
  : forall (A B : Type) (f : A -> B) (x y : A), x = y -> f x = f y.
Example add_S_l : forall n m : nat, S n + m = S (n + m).
Proof. reflexivity. Qed.
