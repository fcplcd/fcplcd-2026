(*---- FCPLCD Assignment 1 - Getting started -----*)
From Stdlib Require Import Utf8.
From Stdlib Require Import Logic.
From Stdlib Require Decidable.
From Stdlib Require Import Basics.

(*
 * These are the facts that you've proven on Pen&Paper before, stated as
 * lemmata.
 *
 * You can use the following analogies between the inference rules you've
 * seen in the lecture and Rocq tactics
 *
 * ax   | assumption / exact / easy
 * =>I  | intro
 * =>E  | eapply (Basics.apply)
 * /\El | eapply (proj1)
 * /\Er | eapply (proj2)
 * /\I  | split
 * \/E  | eapply (or_ind)
 * \/Il | left
 * \/Ir | right
 * ⊥E   | exfalso
 * ¬E   | absurd A1
 * ¬I   | intro
 * ⊤I   | apply (I)
 *)

Lemma modus_ponens A B (Himp : A -> B) (Ha : A) : B.
Proof.
  (* TODO: fill in the proof *)
Admitted.

Lemma and_commutative A B:
  A /\ B -> B /\ A.
Proof.
  (* TODO: fill in the proof *)
Admitted.

Lemma or_commutative A B:
  A \/ B -> B \/ A.
Proof.
  (* TODO: fill in the proof *)
Admitted.

Lemma and_associative A B C:
  A /\ (B /\ C) -> (A /\ B) /\ C.
Proof.
  (* TODO: fill in the proof *)
Admitted.

(* Hint: To see what is going on with the negation here,
 * you may wish to `unfold not` in the goal and/or in the
 * hypothesis you introduced.
 *)

Lemma de_morgan_1 A B:
  ~(A \/ B) -> ~A /\ ~B.
Proof.
  (* TODO: fill in the proof *)
Admitted.

(*Bonus Exercises*)

Lemma de_morgan_2 A B:
  ~A /\ ~B -> ~(A \/ B).
Proof.
  (* TODO: fill in the proof *)
Admitted.


(*
 * Define the type `temperature`, and a conversion
 * function from temperature to nat, converting
 * celsius or kelvin to degree kelvin.
 *)


(* Quick practical detour - Searching in Coq/Roqc
 *
 * If you need to find lemmas/theorems about a particular term in Coq/Roqc or
 * want to see the definition of a particular notation, lemma, type etc. you can use the commands
 * Locate and Search.
 * We have a tutorial on this topic in our leaning repo at [1].
 * But just as a quick demo checkput the what the following Search commands do.
 *
 * [1]: https://gitlab.barkhauseninstitut.org/versa/learning/-/blob/main/code/demos/searching_info.v
 *)

(* The `_` is a wildcard. So this will give you all definitions in scope that contain
 * the pattern `_ + _`
 *)
Search (_ + _).

(* You can also search for particular substrings in the names of definitions *)
Search "and".

(* Negation is a Notation.
 * You can check where it is defined
 * and Search for terms and lemmata using it
 *)
Locate "~".
Search "~".

(* Extra:
 * Try to find a stdlib lemma for each of the statements from exercise 1
 *)