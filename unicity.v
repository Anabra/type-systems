(*
  Definitions of Tm, Ty and Judgement.
  Do not modify these!

  The task starts at line 38.
*)

Inductive Tm : Set :=
  | num (n : nat)
  | plus (t t' : Tm)
  | isZero (t : Tm)
  | true
  | false
  | ifThenElse (t t' t'' : Tm)
.

Notation "t + t'" := (plus t t').
Notation "'If' t 'then' t' 'else' t''" := (ifThenElse t t' t'') (at level 100).

Inductive Ty : Set := Nat | Bool.

Inductive Judgement : Tm -> Ty -> Prop :=
  | J_num {n : nat} : (num n) :: Nat
  | J_plus {t t' : Tm} (j : t :: Nat) (j' : t' :: Nat) : (t + t') :: Nat
  | J_isZero {t : Tm} (j : t :: Nat) : (isZero t) :: Bool
  | J_true : true :: Bool
  | J_false : false :: Bool

  | J_ifThenElse
    {t t' t'' : Tm} {A : Ty}
    (j : t :: Bool) (j' : t' :: A) (j'' : t'' :: A)
    : (If t then t' else t'') :: A

where "tm :: ty" := (Judgement tm ty).

(* ------------------------------ *)

(*
  Proove the unicity of the typing relation, meaning that every term can
  at most have one type! The theorem states the following:
  If the term "tm" is of type "ty" and "ty'" at the same time,
  then "ty" must be equal to "ty'".
*)

Theorem unicity : (
  forall tm : Tm, forall ty ty' : Ty,
  tm :: ty -> tm :: ty' -> ty = ty'
).
Proof.
  intros tm ty ty' H.
  induction H.
  1-5: (intros HN; inversion HN; reflexivity).
  + intros HN. inversion HN. apply IHJudgement2. exact j'.
Qed.