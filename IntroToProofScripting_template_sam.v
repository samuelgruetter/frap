Require Import Frap.

Set Implicit Arguments.


(** * Ltac Programming Basics *)

Theorem hmm : forall (a b c : bool),
  if a
    then if b
      then True
      else True
    else if c
      then True
      else True.
Proof.
Admitted.

Theorem hmm2 : forall (a b : bool),
  (if a then 42 else 42) = (if b then 42 else 42).
Proof.
Admitted.


(** * Automating the two-thread locked-increment example from TransitionSystems *)

(* Let's experience the process of gradually automating the proof we finished
 * the last lecture with.  Here's the system-definition code, stripped of
 * comments. *)

(* BEGIN copied *)

Inductive increment_program :=
| Lock
| Read
| Write (local : nat)
| Unlock
| Done.

Record inc_state := {
  Locked : bool;
  Global : nat
}.

Record threaded_state shared private := {
  Shared : shared;
  Private : private
}.

Definition increment_state := threaded_state inc_state increment_program.

Inductive increment_init : increment_state -> Prop :=
| IncInit :
  increment_init {| Shared := {| Locked := false; Global := O |};
                    Private := Lock |}.

Inductive increment_step : increment_state -> increment_state -> Prop :=
| IncLock : forall g,
  increment_step {| Shared := {| Locked := false; Global := g |};
                    Private := Lock |}
                 {| Shared := {| Locked := true; Global := g |};
                    Private := Read |}
| IncRead : forall l g,
  increment_step {| Shared := {| Locked := l; Global := g |};
                    Private := Read |}
                 {| Shared := {| Locked := l; Global := g |};
                    Private := Write g |}
| IncWrite : forall l g v,
  increment_step {| Shared := {| Locked := l; Global := g |};
                    Private := Write v |}
                 {| Shared := {| Locked := l; Global := S v |};
                    Private := Unlock |}
| IncUnlock : forall l g,
  increment_step {| Shared := {| Locked := l; Global := g |};
                    Private := Unlock |}
                 {| Shared := {| Locked := false; Global := g |};
                    Private := Done |}.

Definition increment_sys := {|
  Initial := increment_init;
  Step := increment_step
|}.

Inductive parallel1 shared private1 private2
  (init1 : threaded_state shared private1 -> Prop)
  (init2 : threaded_state shared private2 -> Prop)
  : threaded_state shared (private1 * private2) -> Prop :=
| Pinit : forall sh pr1 pr2,
  init1 {| Shared := sh; Private := pr1 |}
  -> init2 {| Shared := sh; Private := pr2 |}
  -> parallel1 init1 init2 {| Shared := sh; Private := (pr1, pr2) |}.

Inductive parallel2 shared private1 private2
          (step1 : threaded_state shared private1 -> threaded_state shared private1 -> Prop)
          (step2 : threaded_state shared private2 -> threaded_state shared private2 -> Prop)
          : threaded_state shared (private1 * private2)
            -> threaded_state shared (private1 * private2) -> Prop :=
| Pstep1 : forall sh pr1 pr2 sh' pr1',
  step1 {| Shared := sh; Private := pr1 |} {| Shared := sh'; Private := pr1' |}
  -> parallel2 step1 step2 {| Shared := sh; Private := (pr1, pr2) |}
               {| Shared := sh'; Private := (pr1', pr2) |}
| Pstep2 : forall sh pr1 pr2 sh' pr2',
  step2 {| Shared := sh; Private := pr2 |} {| Shared := sh'; Private := pr2' |}
  -> parallel2 step1 step2 {| Shared := sh; Private := (pr1, pr2) |}
               {| Shared := sh'; Private := (pr1, pr2') |}.

Definition parallel shared private1 private2
           (sys1 : trsys (threaded_state shared private1))
           (sys2 : trsys (threaded_state shared private2)) := {|
  Initial := parallel1 sys1.(Initial) sys2.(Initial);
  Step := parallel2 sys1.(Step) sys2.(Step)
|}.

Definition increment2_sys := parallel increment_sys increment_sys.

Definition contribution_from (pr : increment_program) : nat :=
  match pr with
  | Unlock => 1
  | Done => 1
  | _ => 0
  end.

Definition has_lock (pr : increment_program) : bool :=
  match pr with
  | Read => true
  | Write _ => true
  | Unlock => true
  | _ => false
  end.

Definition shared_from_private (pr1 pr2 : increment_program) :=
  {| Locked := has_lock pr1 || has_lock pr2;
     Global := contribution_from pr1 + contribution_from pr2 |}.

Definition instruction_ok (self other : increment_program) :=
  match self with
  | Lock => True
  | Read => has_lock other = false
  | Write n => has_lock other = false /\ n = contribution_from other
  | Unlock => has_lock other = false
  | Done => True
  end.

Inductive increment2_invariant :
  threaded_state inc_state (increment_program * increment_program) -> Prop :=
| Inc2Inv : forall pr1 pr2,
  instruction_ok pr1 pr2
  -> instruction_ok pr2 pr1
  -> increment2_invariant {| Shared := shared_from_private pr1 pr2; Private := (pr1, pr2) |}.

Lemma Inc2Inv' : forall sh pr1 pr2,
  sh = shared_from_private pr1 pr2
  -> instruction_ok pr1 pr2
  -> instruction_ok pr2 pr1
  -> increment2_invariant {| Shared := sh; Private := (pr1, pr2) |}.
Proof.
  simplify.
  rewrite H.
  apply Inc2Inv; assumption.
Qed.

(* END copied *)

(* OK, HERE is where prove the main theorem. *)

Set Printing Projections.

Theorem increment2_invariant_ok : invariantFor increment2_sys increment2_invariant.
Proof.
Admitted.


(** * Implementing some of [propositional] ourselves *)

Print True.
Print False.
Locate "/\".
Print and.
Locate "\/".
Print or.
(* Implication ([->]) is built into Coq, so nothing to look up there. *)

Ltac my_propositional := idtac.

Section propositional.
  Variables P Q R : Prop.

  Theorem propositional : (P \/ Q \/ False) /\ (P -> Q) -> True /\ Q.
  Proof.
    my_propositional.
  Admitted.
End propositional.

(* Backtracking example #1 *)

Theorem m1 : True.
Proof.
  match goal with
    | [ |- _ ] => intro
    | [ |- True ] => constructor
  end.
Qed.

(* Backtracking example #2 *)

Theorem m2 : forall P Q R : Prop, P -> Q -> R -> Q.
Proof.
  intros. match goal with
            | [ H : _ |- _ ] => idtac H; exact H
          end.
Admitted.

(* Let's try some more ambitious reasoning, with quantifiers.  We'll be
 * instantiating quantified facts heuristically.  If we're not careful, we get
 * in a loop repeating the same instantiation forever. *)

(* Spec: ensure that [P] doesn't follow trivially from hypotheses. *)
Ltac notHyp P := idtac.

Goal 1 = 1 -> 2 = 2 -> 3 = 3.
Proof.
  intros.
Abort.


(* Spec: add [pf] as hypothesis only if it doesn't already follow trivially. *)
Ltac extend pf := idtac.

Goal forall (P: nat -> Prop), 1 = 1 -> 3 = 2 -> 3 = 3.
Proof.
  intros. extend (eq_sym H0).
Abort.

(* Spec: add all simple consequences of known facts, including
 * [forall]-quantified. *)
Ltac completer := idtac.

Section firstorder.
  Variable A : Set.
  Variables P Q R S : A -> Prop.

  Hypothesis H1 : forall x, P x -> Q x /\ R x.
  Hypothesis H2 : forall x, R x -> S x.

  Theorem fo : forall (y x : A), P x -> S x.
  Proof.
    completer.
  Admitted.

End firstorder.


(** * Functional Programming in Ltac *)

(* Spec: return length of list. *)
Ltac length ls := idtac.

Goal False.
(*  let n := length (1 :: 2 :: 3 :: nil) in
    pose n. *)
Abort.

(* Spec: map Ltac function over list. *)
Ltac map f l := l.

Goal False.
  let ls := map ltac:(fun x => constr:((x, x))) (1 :: 2 :: 3 :: nil) in
    pose ls.
Abort.

(*
Goal False.
  let ls := map (nat * nat)%type ltac:(fun x => constr:((x, x))) (1 :: 2 :: 3 :: nil) in
    pose ls.
Abort.
*)

(* Now let's revisit [length] and see how we might implement "printf debugging"
 * for it. *)

Ltac length ls ::= idtac.

(*
Goal False.
  let n := length (1 :: 2 :: 3 :: nil) in
    pose n.
Abort.
*)


(** * Creating Unification Variables *)

(* A final useful ingredient in tactic crafting is the ability to allocate new
 * unification variables explicitly.  Before we are ready to write a tactic, we
 * can try out its ingredients one at a time. *)

Theorem t5 : (forall x : nat, S x > x) -> 2 > 1.
Proof.
  intros.

  evar (y : nat).

  let y' := eval unfold y in y in
    clear y; specialize (H y').

  apply H.
Qed.

(* Spec: create new evar of type [T] and pass to [k]. *)
Ltac newEvar T k := idtac.

Theorem t50 : (forall x : nat, S x > x) -> 2 > 1.
Proof.
  intros.

Abort.

(* Spec: instantiate initial [forall]s of [H] with new evars. *)
Ltac insterU H := idtac.

Theorem t5' : (forall x : nat, S x > x) -> 2 > 1.
Proof.
  intros.
  insterU H.
  apply H.
Qed.


(* This particular example is somewhat silly, since [apply] by itself would have
 * solved the goal originally.  Separate forward reasoning is more useful on
 * hypotheses that end in existential quantifications.  Before we go through an
 * example, it is useful to define a variant of [insterU] that does not clear
 * the base hypothesis we pass to it. *)

Ltac insterKeep H := idtac.

Section t6.
  Variables A B : Type.
  Variable P : A -> B -> Prop.
  Variable f : A -> A -> A.
  Variable g : B -> B -> B.

  Hypothesis H1 : forall v, exists u, P v u.
  Hypothesis H2 : forall v1 u1 v2 u2,
    P v1 u1
    -> P v2 u2
    -> P (f v1 v2) (g u1 u2).

  Theorem t6 : forall v1 v2, exists u1, exists u2, P (f v1 v2) (g u1 u2).
  Proof.
  Admitted.
End t6.

(* Here's an example where something bad happens. *)

(*Ltac insterU tac H ::= idtac.

Ltac insterKeep tac H ::=
*)

Section t7.
  Variables A B : Type.
  Variable Q : A -> Prop.
  Variable P : A -> B -> Prop.
  Variable f : A -> A -> A.
  Variable g : B -> B -> B.

  Hypothesis H1 : forall v, Q v -> exists u, P v u.
  Hypothesis H2 : forall v1 u1 v2 u2,
    P v1 u1
    -> P v2 u2
    -> P (f v1 v2) (g u1 u2).

  Theorem t7 : forall v1 v2, Q v1 -> Q v2 -> exists u1, exists u2, P (f v1 v2) (g u1 u2).
  Proof.
    intros.
    insterKeep H1.
    (* Oh, two trivial goals remain.
    Unshelve.
    assumption.
    assumption.*)
  Admitted.
End t7.

Theorem t8 : exists p : nat * nat, fst p = 3.
Proof.
  econstructor.
  instantiate (1 := (3, 2)).
  equality.
Qed.

(* A way that plays better with automation: *)

Theorem t9 : exists p : nat * nat, fst p = 3.
Proof.
  econstructor. match goal with
                  | [ |- fst ?x = 3 ] => unify x (3, 2)
                end. equality.
Qed.
