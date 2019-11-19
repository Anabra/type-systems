Require Import Nat.
Require Import Arith.


(*
  The "Tm" type and the previously defined typing relation.
*)

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

(*
  Value judgements.
*)

Inductive ValueJudgement : Tm -> Prop :=
  | VJ_num {n : nat} : (num n) val
  | VJ_true          : true val
  | VJ_false         : false val
where "t 'val'" := (ValueJudgement t).




(* |-> : 2.14. - 2.22. *)

Reserved Notation "t |-> t'" (at level 100).

(*
  One Step Transition judgements.
*)

Inductive OneStepTransitionJudgement : Tm -> Tm -> Prop :=
  | OSTJ_plus {n n1 n2 : nat} : 
    ((n1 + n2)%nat = n) -> 
    num n1 + num n2 |-> num n 
    
  | OSTJ_isZero_true : 
    isZero (num 0) |-> true
    
  | OSTJ_isZero_false {n : nat} : 
    (n > 0) -> 
    isZero (num n) |-> false
    
  | OSTJ_ifThenElse_true {t1 t2 : Tm} : 
    If true then t1 else t2 |-> t1
  
  | OSTJ_ifThenElse_false {t1 t2 : Tm} : 
    If false then t1 else t2 |-> t2
    
  | OSTJ_plus_left {t1 t2 t1' : Tm} : 
    (t1 |-> t1') -> 
    (t1 + t2 |-> t1' + t2)
    
  | OSTJ_plus_right {t1 t2 t2' : Tm} : 
    t1 val -> 
    (t2 |-> t2') -> 
    (t1 + t2 |-> t1 + t2')
    
  | OSTJ_isZero {t t' : Tm} : 
    (t |-> t') -> 
    (isZero t |-> isZero t')
  
  | OSTJ_ifThenElse {t t' t1 t2 : Tm} : 
    (t |-> t') -> 
    (If t then t1 else t2 |-> If t' then t1 else t2)
where "t |-> t'" := (OneStepTransitionJudgement t t').




(* |->* : 2.12. - 2.13. *)

Reserved Notation "t |->* t'" (at level 100).

(*
  Any Step Transition judgements.
*)

Inductive AnyStepTransitionJudegement : Tm -> Tm -> Prop :=
  | ASTJ_refl  {e : Tm} : 
    (e |->* e)
     
  | ASTJ_trans {e e' e'' : Tm} : 
    (e  |->  e') -> 
    (e' |->* e'') -> 
    (e  |->* e'')
where "t |->* t'" := (AnyStepTransitionJudegement t t').



Lemma p :
  (num 1 + num 2) + (num 3 + num 4) |-> num 3 + (num 3 + num 4).
Proof.
  apply OSTJ_plus_left.
  apply OSTJ_plus.
  trivial.
Qed.

Lemma q :
  num 3 + (num 3 + num 4) |-> num 3 + num 7.
Proof.
  apply OSTJ_plus_right.
  + apply VJ_num.
  + apply OSTJ_plus. trivial.
Qed.

Lemma r :
  num 3 + num 7 |-> num 10.
Proof.
  apply OSTJ_plus.
  trivial.
Qed.

Lemma TransitionTest1 :
  (num 1 + num 2) + (num 3 + num 4) |->* num 10.
Proof.
  eapply ASTJ_trans.
  + eapply OSTJ_plus_left. eapply OSTJ_plus. reflexivity.
  + eapply ASTJ_trans. 
    - simpl. eapply OSTJ_plus_right.
      * exact VJ_num.
      * eapply OSTJ_plus. reflexivity.
    - simpl. eapply ASTJ_trans.
      * eapply OSTJ_plus. reflexivity.
      * simpl. apply ASTJ_refl. 
Qed.


Lemma TransitionTest2 :
  If isZero (num 1 + num 2) then num 1 else (num 3 + num 1) |->* num 4.
Proof.
  eapply ASTJ_trans.
  + eapply OSTJ_ifThenElse. eapply OSTJ_isZero. eapply OSTJ_plus. reflexivity.
  + eapply ASTJ_trans. 
    - eapply OSTJ_ifThenElse. eapply OSTJ_isZero_false. auto.
    - eapply ASTJ_trans.
      * eapply OSTJ_ifThenElse_false.
      * eapply ASTJ_trans.
        ** eapply OSTJ_plus. reflexivity.
        ** simpl. eapply ASTJ_refl.
Qed.


(*
  2.19. Lemma.
  No transition exists from val.
*)



(*
  2.20. Lemma.
  Deterministicity.
*)




(*
  2.27. Tétel.
  Theorem of type preservation.
*)



(*
  2.29. Lemma
*)



(*
  2.28. Tétel.
  Theorem of progress.
*)

