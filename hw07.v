(*
  The "Tm" type and the previously defined transition judgements.
  Do not modify these!

  The task starts at line 125.
*)

Require Import Nat.
Require Import Arith.

Inductive Tm : Set :=
  | num (n : nat)
  | plus (t t' : Tm)
  | isZero (t : Tm)
  | true
  | false
  | ifThenElse (t t' t'' : Tm)
.

Notation "t + t'" := (plus t t') : term_scope.
Notation
  "'If' t 'then' t' 'else' t''" :=
  (ifThenElse t t' t'')
  (at level 100)
  : term_scope
.

Delimit Scope term_scope with term.
(* Bind Scope term_scope with Tm. *)
Open Scope term_scope.

(* The set of Ty and the inductive typing relation. *)

Inductive Ty : Set := Nat | Bool.

Inductive TypeJudgement : Tm -> Ty -> Prop :=
  | TJ_num {n : nat} : (num n) :: Nat
  | TJ_plus {t t' : Tm} (j : t :: Nat) (j' : t' :: Nat) : (t + t') :: Nat
  | TJ_isZero {t : Tm} (j : t :: Nat) : (isZero t) :: Bool
  | TJ_true : true :: Bool
  | TJ_false : false :: Bool

  | TJ_ifThenElse
    {t t' t'' : Tm} {A : Ty}
    (j : t :: Bool) (j' : t' :: A) (j'' : t'' :: A)
    : (If t then t' else t'') :: A

where "tm :: ty" := (TypeJudgement tm ty) : term_scope.

(*
  2.3. Operációs szemantika
*)

(* val : 2.9. - 2.11. *)

Reserved Notation "t 'val'" (at level 1).

Inductive ValueJudgement : Tm -> Prop :=
  | VJ_num {n : nat} : (num n) val
  | VJ_true : true val
  | VJ_false : false val
where
  "t 'val'" :=
  (ValueJudgement t)
  : term_scope.

(*
  Transition judgements.
*)

Reserved Notation "t |-> t'" (at level 100).

(* One Step Transition : 2.14. - 2.22. *)

Inductive OneStepTransitionJudgement : Tm -> Tm -> Prop :=
  | OSTJ_sum {n1 n2 n : nat} :
    ((n1 + n2)%nat = n) ->
    num n1 + num n2 |-> num n

  | OSTJ_isZero_true :
    (isZero (num 0)) |-> true

  | OSTJ_isZero_false {n : nat} :
    (n > 0) ->
    isZero (num n) |-> false

  | OSTJ_ifThenElse_true {t t' : Tm} :
    If true then t else t' |-> t

  | OSTJ_ifThenElse_false {t t' : Tm} :
    If false then t else t' |-> t'

  | OSTJ_plus_left {t1 t1' t2 : Tm} :
    (t1 |-> t1') ->
    t1 + t2 |-> t1' + t2

  | OSTJ_plus_right {t1 t2 t2' : Tm} :
    t1 val -> (t2 |-> t2') ->
    t1 + t2 |-> t1 + t2'

  | OSTJ_isZero {t t' : Tm} :
    (t |-> t') ->
    isZero t |-> isZero t'

  | OSTJ_ifThenElse {t t' t1 t2 : Tm} :
    (t |-> t') ->
    If t then t1 else t2 |-> If t' then t1 else t2
where
  "t |-> t'" :=
  (OneStepTransitionJudgement t t')
  : term_scope.

(* Any Step Transition : 2.12. - 2.13. *)

Reserved Notation "t |->* t'" (at level 100).

Inductive AnyStepTransitionJudgement : Tm -> Tm -> Prop :=
  | ASTJ_refl {t : Tm} :
    t |->* t
  | ASTJ_trans {t t'' : Tm} (t' : Tm) : 
    (t |-> t') -> (t' |->* t'') ->
    t |->* t''
where "t |->* t'" := (AnyStepTransitionJudgement t t') : term_scope.

(* ------------------------------ *)

(*
  Prove the following theorem!
*)

Lemma progress_helper_Bool {t : Tm} :
  (t :: Bool) -> (t val) -> (t = true \/ t = false).
Proof.
  intros.
  inversion H0.
  + subst. inversion H.
  + left. trivial.
  + right. trivial.
Qed.