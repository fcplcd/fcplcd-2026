


Inductive boolLang :=
  | TTrue
  | FFalse
  | If (t1 t2 t3 : boolLang).

Notation "'if' x 'then' y 'else' z" := (If x y z) (at level 70, right associativity).

Definition prog1 := TTrue.
Definition prog2 := if TTrue then FFalse else TTrue.
Definition prog3 := if prog2 then TTrue else prog1.

Fixpoint eval (t:boolLang) : bool :=
  match t with
  | TTrue => true
  | FFalse => false
  | If t1 t2 t3 => match eval t1 with
                  | true => eval t2
                  | false => eval t3
                  end
  end.

Fixpoint eval1 (t:boolLang) : boolLang :=
  match t with
  | TTrue => TTrue
  | FFalse => FFalse
  | If TTrue t2 t3 => t2
  | If FFalse t2 t3 => t3
  | If t1 t2 t3 => If (eval1 t1) t2 t3
  end.

Fixpoint termSize (t:boolLang) : nat :=
  match t with
  | TTrue | FFalse => 1
  | If t1 t2 t3 => 1 + (termSize t1) + (termSize t2) + (termSize t3)
  end.

Compute (termSize prog1).
Print prog2.
Compute (termSize prog2).

Lemma decr : forall t, termSize (eval1 t) < termSize t .
Admitted.

Variant option {T} :=
  | None
  | Some (x:T).

Fixpoint eval2 (t:boolLang) : @option boolLang :=
  match t with
  | TTrue => None
  | FFalse => None
  | If TTrue t2 t3 => Some t2
  | If FFalse t2 t3 => Some t3
  | If t1 t2 t3 => Some (If (eval1 t1) t2 t3)
  end.

Inductive step : boolLang -> boolLang -> Type :=
| EIfTrue: forall t2 t3,
  (*--------------------------------*)
  step (If TTrue t2 t3) t2
| EIfFalse: forall t2 t3,
  (*--------------------------------*)
  step (If FFalse t2 t3) t3
| EIf: forall t1 t1' t2 t3,
    step t1 t1' ->
  (*--------------------------------*)
  step (If t1 t2 t3) (If t1' t2 t3).


Definition is_value (t:boolLang) : Prop :=
  match t with
  | TTrue | FFalse => True
  | _ => False
  end.

Variant isVal : boolLang -> Prop :=
  | trueIsVal : isVal TTrue
  | falseISVal : isVal FFalse.

Definition s:= if TTrue then FFalse else FFalse.
Definition t := if s then TTrue else TTrue.
Definition u := if FFalse then TTrue else TTrue.

Notation "x '--->' y" := (step x y) (at level 70).

Lemma red1 :
  (if t then FFalse else FFalse) ---> (if u then FFalse else FFalse).
Proof.
  unfold t.
  unfold u.
  unfold s.
  (* Unset Printing Notations. *)
  apply EIf.
  apply EIf.
  apply EIfTrue.
Qed.

(** * 1. try: proof by induction on the source term [t] *)
Lemma det: forall t1 t1' t1'', t1 ---> t1' -> t1 ---> t1'' -> t1' = t1''.
Proof.
  intro t1.
  induction t1; intros.
  - exfalso. inversion H.
  - inversion H.
  - inversion H; inversion H0; subst; try reflexivity.
    -- inversion H6.
    -- inversion H9.
    -- inversion H6.
    -- inversion H9.
    -- inversion H5.
    -- inversion H5.
    -- specialize (IHt1_1 t1'0 t1'1 H5 H10).
       rewrite IHt1_1.
       reflexivity.
Qed.

(** * 2. try: proof by induction on the first step relation *)
Lemma det': forall t1 t1' t1'', t1 ---> t1' -> t1 ---> t1'' -> t1' = t1''.
Proof.
  intros t1 t1' t1'' H.
  revert t1''.
  induction H.
  - intros. inversion H; try reflexivity. inversion H4.
  - intros. inversion H; try reflexivity. inversion H4.
  - intros.
    inversion H0.
    -- subst. inversion H.
    -- subst. inversion H.
    -- subst. specialize (IHstep _ H5). rewrite IHstep. reflexivity.
Qed.

Require Import Coq.Logic.JMeq.

(** * 3rd try: no inversion *)
Lemma det'': forall t1 t1' t1'', t1 ---> t1' -> t1 ---> t1'' -> t1' = t1''.
Proof.
  intro t1.
  induction t1; intros.
  - (* the idea is to generate equalities which can be used to
       extract facts via injectivity (i.e., the [injection] tactic)
     *)
    generalize_eqs H; intros.
    (* I have just bound the first parameter to [step] to a fresh variable [gen_x]
       and use an equality to state the association. *)
    destruct H.
    (* now I still have the equality but refined. *)
    -- discriminate H1.
    -- (* Here is what [discriminate] does: *)
       Check eq_ind.
       set (P (e:boolLang) :=
              match e with
              | TTrue => True
              | _ => False
              end).
       assert (P_true : P TTrue).
       1:{ unfold P. exact I. }
       set (XXX := @eq_ind boolLang TTrue P P_true).
       symmetry in H1.
       specialize (XXX _ H1).
       unfold P in XXX.
       Check False_ind.
       exact (False_ind _ XXX).
  -- discriminate H1.
  - (* Check out how [destruct H eqn:E] gives you something very different!
       [destruct] does not look at the type, i.e., its current indices, carefull enough!
     *)
    generalize_eqs H; intros.
    destruct H; discriminate H1.
  - generalize_eqs H; intros.
    destruct H; injection H1; intros.
    -- subst. generalize_eqs H0; intros.
       destruct H0; injection H; intros.
       --- symmetry; assumption.
       --- discriminate H3.
       --- subst. generalize_eqs H0; intros.
           destruct H0.
           ---- discriminate H2.
           ---- discriminate H2.
           ---- discriminate H2.
    -- subst. generalize_eqs H0; intros.
       destruct H0; injection H; intros.
       --- discriminate H3.
       --- symmetry; assumption.
       --- subst. generalize_eqs H0; intros.
           destruct H0; try discriminate H2.
    -- subst. generalize_eqs H0; intros.
       destruct H0; injection H2; intros.
       --- subst. generalize_eqs H; intros.
           destruct H; try discriminate H0.
       --- subst. generalize_eqs H; intros.
           destruct H; try discriminate H0.
       --- subst; clear H1 H2.
           rewrite (IHt1_1 _ _ H H0).
           reflexivity.
Qed.
