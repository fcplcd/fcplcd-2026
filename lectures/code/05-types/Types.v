(* Lecture 5: types. Every snippet on the slides is here. *)
From Stdlib Require Import Relations.

(* ---------- The language: booleans and natural numbers ---------- *)

Inductive tm : Type :=
| TTrue  : tm
| TFalse : tm
| If     : tm -> tm -> tm -> tm
| Zero   : tm
| Succ   : tm -> tm
| Pred   : tm -> tm
| IsZero : tm -> tm.

Variant bvalue : tm -> Prop :=
| bv_true  : bvalue TTrue
| bv_false : bvalue TFalse.

Inductive nvalue : tm -> Prop :=
| nv_zero : nvalue Zero
| nv_succ : forall t, nvalue t -> nvalue (Succ t).

Definition value (t : tm) : Prop := bvalue t \/ nvalue t.

Reserved Notation "t '-->' t'" (at level 40).

Inductive step : tm -> tm -> Prop :=
| E_IfTrue     : forall t2 t3, If TTrue t2 t3 --> t2
| E_IfFalse    : forall t2 t3, If TFalse t2 t3 --> t3
| E_If         : forall t1 t1' t2 t3,
    t1 --> t1' -> If t1 t2 t3 --> If t1' t2 t3
| E_Succ       : forall t1 t1', t1 --> t1' -> Succ t1 --> Succ t1'
| E_PredZero   : Pred Zero --> Zero
| E_PredSucc   : forall nv, nvalue nv -> Pred (Succ nv) --> nv
| E_Pred       : forall t1 t1', t1 --> t1' -> Pred t1 --> Pred t1'
| E_IsZeroZero : IsZero Zero --> TTrue
| E_IsZeroSucc : forall nv, nvalue nv -> IsZero (Succ nv) --> TFalse
| E_IsZero     : forall t1 t1', t1 --> t1' -> IsZero t1 --> IsZero t1'
where "t '-->' t'" := (step t t').

Notation "t '-->*' t'" := (clos_refl_trans tm step t t') (at level 40).

Definition normal_form (t : tm) : Prop := ~ exists t', t --> t'.
Definition stuck (t : tm) : Prop := normal_form t /\ ~ value t.

(* succ true is stuck *)
Example succ_true_stuck : stuck (Succ TTrue).
Proof.
  split.
  - intros [t' H]. inversion H; subst. inversion H1.
  - intros [H | H]; inversion H; inversion H1.
Qed.

(* ---------- Types and the typing relation ---------- *)

Variant ty : Type :=
| Bool : ty
| Nat  : ty.

Reserved Notation "'⊢' t '∈' T" (at level 40).

Inductive has_type : tm -> ty -> Prop :=
| T_True   : ⊢ TTrue ∈ Bool
| T_False  : ⊢ TFalse ∈ Bool
| T_If     : forall t1 t2 t3 T,
    ⊢ t1 ∈ Bool -> ⊢ t2 ∈ T -> ⊢ t3 ∈ T -> ⊢ If t1 t2 t3 ∈ T
| T_Zero   : ⊢ Zero ∈ Nat
| T_Succ   : forall t1, ⊢ t1 ∈ Nat -> ⊢ Succ t1 ∈ Nat
| T_Pred   : forall t1, ⊢ t1 ∈ Nat -> ⊢ Pred t1 ∈ Nat
| T_IsZero : forall t1, ⊢ t1 ∈ Nat -> ⊢ IsZero t1 ∈ Bool
where "'⊢' t '∈' T" := (has_type t T).

(* A typing derivation *)
Example typed_if : ⊢ If TTrue Zero (Succ Zero) ∈ Nat.
Proof.
  apply T_If.
  - apply T_True.
  - apply T_Zero.
  - apply T_Succ. apply T_Zero.
Qed.

(* ... and the same derivation as a proof term *)
Example typed_if' : ⊢ If TTrue Zero (Succ Zero) ∈ Nat :=
  T_If _ _ _ _ T_True T_Zero (T_Succ _ T_Zero).

(* The stuck term has no type *)
Example succ_true_untyped : ~ exists T, ⊢ Succ TTrue ∈ T.
Proof.
  intros [T H]. inversion H; subst. inversion H1.
Qed.

(* Types are conservative: this term evaluates fine, yet has no type. *)
Example conservative : If TTrue Zero TFalse --> Zero /\ ~ exists T, ⊢ If TTrue Zero TFalse ∈ T.
Proof.
  split.
  - apply E_IfTrue.
  - intros [T H]. inversion H; subst. inversion H5; subst. inversion H6.
Qed.

Theorem type_unique : forall t T T',
  ⊢ t ∈ T -> ⊢ t ∈ T' -> T = T'.
Proof.
  intros t T T' H. generalize dependent T'.
  induction H; intros T' H'; inversion H'; subst; auto.
Qed.

(* ---------- Safety = progress + preservation ---------- *)

Lemma bool_canonical : forall t, ⊢ t ∈ Bool -> value t -> bvalue t.
Proof.
  intros t HT [Hb | Hn]; [exact Hb |].
  destruct Hn; inversion HT.
Qed.

Lemma nat_canonical : forall t, ⊢ t ∈ Nat -> value t -> nvalue t.
Proof.
  intros t HT [Hb | Hn]; [| exact Hn].
  destruct Hb; inversion HT.
Qed.

Theorem progress : forall t T,
  ⊢ t ∈ T -> value t \/ exists t', t --> t'.
Proof.
  intros t T H.
  induction H.
  - (* T_True *)   left. left. constructor.
  - (* T_False *)  left. left. constructor.
  - (* T_If *)     right. destruct IHhas_type1 as [V | [t1' S]].
    + destruct (bool_canonical _ H V).
      * exists t2. apply E_IfTrue.
      * exists t3. apply E_IfFalse.
    + exists (If t1' t2 t3). apply E_If. exact S.
  - (* T_Zero *)   left. right. constructor.
  - (* T_Succ *)   destruct IHhas_type as [V | [t1' S]].
    + left. right. constructor. apply nat_canonical; assumption.
    + right. exists (Succ t1'). apply E_Succ. exact S.
  - (* T_Pred *)   right. destruct IHhas_type as [V | [t1' S]].
    + destruct (nat_canonical _ H V) as [| nv NV].
      * exists Zero. apply E_PredZero.
      * exists nv. apply E_PredSucc. exact NV.
    + exists (Pred t1'). apply E_Pred. exact S.
  - (* T_IsZero *) right. destruct IHhas_type as [V | [t1' S]].
    + destruct (nat_canonical _ H V) as [| nv NV].
      * exists TTrue. apply E_IsZeroZero.
      * exists TFalse. apply E_IsZeroSucc. exact NV.
    + exists (IsZero t1'). apply E_IsZero. exact S.
Qed.

Theorem preservation : forall t t' T,
  ⊢ t ∈ T -> t --> t' -> ⊢ t' ∈ T.
Proof.
  intros t t' T HT.
  generalize dependent t'.
  induction HT; intros t' HE.
  all: inversion HE; subst.
  - (* T_If, E_IfTrue  *) assumption.
  - (* T_If, E_IfFalse *) assumption.
  - (* T_If, E_If      *) apply T_If; [apply IHHT1 |..]; assumption.
  - (* T_Succ, E_Succ  *) apply T_Succ. apply IHHT. assumption.
  - (* T_Pred, E_PredZero *) apply T_Zero.
  - (* T_Pred, E_PredSucc *) inversion HT. assumption.
  - (* T_Pred, E_Pred     *) apply T_Pred. apply IHHT. assumption.
  - (* T_IsZero, E_IsZeroZero *) apply T_True.
  - (* T_IsZero, E_IsZeroSucc *) apply T_False.
  - (* T_IsZero, E_IsZero     *) apply T_IsZero. apply IHHT. assumption.
Qed.

(* Safety: a well-typed term never gets stuck, however long it runs. *)
Corollary soundness : forall t t' T,
  ⊢ t ∈ T -> t -->* t' -> ~ stuck t'.
Proof.
  intros t t' T HT HM. apply clos_rt_rt1n in HM.
  induction HM as [t | t t1 t' S _ IH]; intros [NF NV].
  - destruct (progress _ _ HT) as [V | E]; auto.
  - apply IH; [eapply preservation; eassumption | split; assumption].
Qed.

(* ---------- A type checker ---------- *)

Definition ty_eqb (T1 T2 : ty) : bool :=
  match T1, T2 with
  | Bool, Bool | Nat, Nat => true
  | _, _ => false
  end.

Fixpoint typeof (t : tm) : option ty :=
  match t with
  | TTrue | TFalse => Some Bool
  | Zero => Some Nat
  | Succ t1 | Pred t1 =>
      match typeof t1 with Some Nat => Some Nat | _ => None end
  | IsZero t1 =>
      match typeof t1 with Some Nat => Some Bool | _ => None end
  | If t1 t2 t3 =>
      match typeof t1, typeof t2, typeof t3 with
      | Some Bool, Some T2, Some T3 => if ty_eqb T2 T3 then Some T2 else None
      | _, _, _ => None
      end
  end.

Compute typeof (If TTrue Zero (Succ Zero)).   (* = Some Nat *)
Compute typeof (Succ TTrue).                  (* = None *)

Theorem typeof_sound : forall t T, typeof t = Some T -> ⊢ t ∈ T.
Proof.
  induction t as [| | t1 IH1 t2 IH2 t3 IH3 | | t1 IH1 | t1 IH1 | t1 IH1];
    intros T H; simpl in H.
  - injection H as <-. constructor.
  - injection H as <-. constructor.
  - destruct (typeof t1) as [[|] |]; try discriminate.
    destruct (typeof t2) as [T2 |]; try discriminate.
    destruct (typeof t3) as [T3 |]; try discriminate.
    destruct T2, T3; simpl in H; try discriminate;
      injection H as <-; constructor; auto.
  - injection H as <-. constructor.
  - destruct (typeof t1) as [[|] |]; try discriminate.
    injection H as <-. constructor. auto.
  - destruct (typeof t1) as [[|] |]; try discriminate.
    injection H as <-. constructor. auto.
  - destruct (typeof t1) as [[|] |]; try discriminate.
    injection H as <-. constructor. auto.
Qed.

Theorem typeof_complete : forall t T, ⊢ t ∈ T -> typeof t = Some T.
Proof.
  intros t T H. induction H; simpl;
    repeat match goal with H : typeof _ = _ |- _ => rewrite H end;
    try reflexivity.
  destruct T; reflexivity.
Qed.
