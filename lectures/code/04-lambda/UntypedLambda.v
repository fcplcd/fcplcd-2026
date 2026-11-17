From stdpp Require Import strings fin_sets list.

Module UntypedLambda.


  Instance str_list_elem : Elements string (list string) := id.

  (* TODO I need to sort this list by string length.
          Then, adding just a character to a recursive call,
          is guaranteed to be a new string.

          Check out this implementation:
          https://plv.mpi-sws.org/coqdoc/stdpp/stdpp.stringmap.html#lab80
   *)

  Fixpoint str_list_fresh ls :=
    match ls with
    | nil => "a"
    | x :: xs =>
        let x' := str_list_fresh xs in
        if  (x =? x')%string
        then x' +:+ "a"
        else x'
    end.

  Instance str_list_fresh' : Fresh string (list string) := str_list_fresh.

  Definition var : Type := string.

  (**
     The untyped lambda calculus
   *)

  Inductive Term :=
  | Var: var -> Term
  | Lambda: var -> Term -> Term
  | App: Term -> Term -> Term.


  Compute (Lambda "x" (Var "x")).

  Fixpoint subst (t:Term) (x:string) (v:Term) : Term :=
    match t with
    | Var n       => if (x =? n)%string
                    then v
                    else Var n
    | Lambda n t1 => if (x =? n)%string
                    then Lambda n t1
                    else Lambda n (subst t1 x v)
    | App t1 t2   => App (subst t1 x v) (subst t2 x v)
    end.


  Compute (subst (Lambda "x" (Var "y")) ("y") (Var "z")).
  Compute (subst (Lambda "x" (Var "y")) "y" (Var "x")).

  Fixpoint fvars' (t:Term) (bv: list string) : list string :=
    match t with
    | Var n => if existsb (String.eqb n) bv
              then nil
              else cons n nil
    | Lambda n t1 => fvars' t1 (cons n bv)
    | App t1 t2 =>  app (fvars' t1 bv) (fvars' t2 bv)
    end.

  Definition fvars (t:Term) : list string := fvars' t [].

  Fixpoint alpha (t:Term) (fvar: list string) (f: string -> string) : Term :=
    match t with
    | Var n => Var (f n)
    | Lambda n t1 =>
        let fvar' := cons n fvar in
        let n' := stdpp.base.fresh fvar' in
        Lambda n' $ alpha t1 fvar'
          (fun n'' =>
             if (n'' =? n)%string
             then n'
             else f n'')
    | App t1 t2 => App (alpha t1 fvar f) (alpha t2 fvar f)
    end.

  Definition subst' (t:Term) (x:string) (t':Term) : Term :=
    if length (fvars t') =? 0
    then subst t x t'
    else subst (alpha t (fvars t') id) x t'.

  Notation "'[' x '↦' v ']' t" := (subst' t x v) (at level 0).

  Compute ( ["y" ↦ (Var "z")](Lambda "x" (Var "y"))  ).

  Inductive Eval : Term -> Term -> Prop :=

  | EApp1 :
    forall t1 t1' t2,
      Eval t1 t1' ->
  (* ---------------------------------------*)
      Eval (App t1 t2) (App t1' t2)

   | EApp2 :
    forall t12 t2 t2' x,
      Eval t2 t2' ->
  (* ---------------------------------------*)
      Eval (App (Lambda x t12) t2) (App (Lambda x t12) t2')

   | EAppAbs :
    forall t12 t22 x x',
  (* ---------------------------------------*)
      Eval (App (Lambda x t12) (Lambda x' t22)) [x ↦ (Lambda x' t22)]t12.

  Notation "t1 '⟶' t2" := (Eval t1 t2) (at level 70).

  Definition tru := Lambda "t" $ Lambda "f" $ Var "t".
  Definition tru' := Lambda "t" (Lambda "f" (Var "t")).

  Check tru.
  Definition fls := Lambda "t" $ Lambda "f" $ Var "f".
  Definition test :=
    Lambda "l" $ Lambda "m" $ Lambda "n" $
      App (App (Var "l") (Var "m")) (Var "n").

  Definition and :=
    Lambda "b" $ Lambda "c" $
      App (App (App test (Var "b"))
             (App (App (App test (Var "c")) tru) fls))
                          fls.

  Require Import Coq.Relations.Relation_Operators.

  Print clos_refl_trans.
  Notation "t1 '⟶⋆' t2" := (clos_refl_trans _ Eval t1 t2) (at level 70).

  Lemma test_ttf: (App (App (App test tru) tru) fls) ⟶⋆ tru.
  Proof.
    (* step 1: *)
    eapply rt_trans.
    apply rt_step.
    do 2! apply EApp1.
    apply EAppAbs.
    cbn; fold tru fls.

    eapply rt_trans.
    apply rt_step.
    do 1! apply EApp1.
    apply EAppAbs.
    cbn; fold tru fls.

    eapply rt_trans.
    apply rt_step.
    apply EAppAbs.
    cbn; fold tru fls.

    eapply rt_trans.
    apply rt_step.
    do 1! apply EApp1.
    apply EAppAbs.
    cbn; fold tru fls.

    eapply rt_trans.
    apply rt_step.
    apply EAppAbs.
    cbn; fold tru fls.

    apply rt_refl.
  Qed.

  Lemma tru_and_tru: (App (App and tru) tru) ⟶⋆ tru.
  Proof.
    (* step 1: *)
    eapply rt_trans.
    apply rt_step.
    apply EApp1.
    apply EAppAbs.
    cbn; fold tru fls.

    (* step 2: HOMEWORK
       hint: try to automate the execution via Ltac
     *)

  Admitted.


  Fixpoint factorial x :=
    match x with
    | 0 =>  1
    | S x' => x * factorial x'
    end.

  Print factorial.

  Definition factorial' f x :=
    match x with
    | 0 =>  1
    | S x' => x * f x'
    end.

  Definition factorial'' :=
    fix factorial''' (x:nat) : nat
      := factorial' factorial''' x.

End UntypedLambda.

(*
  We have seen that tinkering with the substitution
  is not necessarily an easy task.

  Here is an approach to encode the untyped lambda calculus
  in Coq, while exploiting Coq's substitution.
 *)

Module HigherOrderAbstractSyntax.

  Parameter var : Set. (* Some set of variables exists. *)

  Inductive Term :=
  | Var: var -> Term
  | Lambda: (var -> Term) -> Term (* Note this minor but super-important detail. *)
  | App: Term -> Term -> Term.

  Inductive Eval : Term -> Term -> Type :=

  | EApp1 :
    forall t1 t1' t2,
      t1 --> t1' ->
  (* ---------------------------------------*)
      App t1 t2 --> App t1' t2

   | EApp2 :
    forall l t2 t2',
      t2 --> t2' ->
  (* ---------------------------------------*)
      App (Lambda l) t2 --> App (Lambda l) t2'

   | EAppAbs1 :
    forall t11 n,
  (* ---------------------------------------*)
      App (Lambda t11) (Var n) --> t11 n

  (* | EAppAbs2 : *)
  (*   forall t11 t21 n, *)
  (* (* ---------------------------------------*) *)
  (*     App (Lambda t11) (Lambda t21) --> (t11 t21) *)

  where "t '-->' t'" := (Eval t t').


  (*
    To unify variables, please use the [inversion] tactic.
   *)
  Ltac isc H := inversion H; subst; clear H.

  Lemma det:
    forall t t' t'',
      t --> t'  ->
      t --> t'' ->
      t' = t''.
  Proof.
    intro t.
    induction t; intros t' t'' H1 H2.
    - inversion H1.
    - inversion H2.
    - isc H1; isc H2.
      + specialize (IHt1 t1' t1'0 H4 H3).
        rewrite IHt1; done.
      + inversion H4.
      + inversion H4.
      + inversion H3.
      + specialize (IHt2 t2' t2'0 H4 H3).
        rewrite IHt2; done.
      + inversion H4.
      + inversion H3.
      + inversion H3.
      + done.
  Qed.

  Ltac noeval :=
    match goal with
    | H : Var _    --> _ |- _ => inversion H
    | H : Lambda _ --> _ |- _ => inversion H
    end.

  Lemma det':
    forall t t' t'',
      t --> t'  ->
      t --> t'' ->
      t' = t''.
  Proof.
    intro t.
    induction t; intros t' t'' H1 H2; try noeval.
    - isc H1; isc H2; try (noeval || done).
      + specialize (IHt1 t1' t1'0 H4 H3).
        rewrite IHt1; done.
      + specialize (IHt2 t2' t2'0 H4 H3).
        rewrite IHt2; done.
  Qed.


End HigherOrderAbstractSyntax.
