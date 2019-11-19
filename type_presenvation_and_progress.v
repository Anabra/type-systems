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

(* Delimit Scope term_scope with term. *)
(* Bind Scope term_scope with Tm. *)
Open Scope term_scope.

(* Compute (plus (num 1) (num 2)). *)
Compute (num 1 + num (2 + 3)).
Compute (2 + 4)%nat.

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
  2.3. OperĂĄciĂłs szemantika
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


Lemma p :
  (num 1 + num 2) + (num 3 + num 4) |-> num 3 + (num 3 + num 4)
.
Proof.
  apply OSTJ_plus_left.
  apply OSTJ_sum.
  simpl. reflexivity.
Qed.

Lemma q :
  num 3 + (num 3 + num 4) |-> num 3 + num 7
.
Proof.
  apply OSTJ_plus_right.
  - apply VJ_num.
  - apply OSTJ_sum.
    simpl. reflexivity.
Qed.

Lemma r :
  num 3 + num 7 |-> num 10
.
Proof.
  apply OSTJ_sum.
  simpl. reflexivity.
Qed.

Lemma TransitionTest1 :
  (num 1 + num 2) + (num 3 + num 4) |->* num 10
.
Proof.
  refine (ASTJ_trans _ p _).
  - refine (ASTJ_trans _ q _).
    + refine (ASTJ_trans _ r _).
      * exact ASTJ_refl.
Qed.


Lemma TransitionTest2 :
  If isZero (num 1 + num 2) then num 1 else (num 3 + num 1) |->* num 4
.
Proof.
  eapply ASTJ_trans.
  {
    eapply OSTJ_ifThenElse.
    eapply OSTJ_isZero.
    eapply OSTJ_sum; reflexivity.
  }

  eapply ASTJ_trans.
  {
    eapply OSTJ_ifThenElse.
    eapply OSTJ_isZero_false.
    eapply gt_Sn_O.
  }

  eapply ASTJ_trans.
  {
    eapply OSTJ_ifThenElse_false.
  }

  eapply ASTJ_trans.
  {
    eapply OSTJ_sum; reflexivity.
  }

  eapply ASTJ_refl.
Qed.

(* Proof.
  refine (ASTJ_trans _ _ _).
  - refine (OSTJ_ifThenElse _).
    + refine (OSTJ_isZero _).
      * refine (OSTJ_sum _).
        -- simpl. reflexivity.
  - refine (ASTJ_trans _ _ _).
    + refine (OSTJ_ifThenElse _).
      * refine (OSTJ_isZero_false _).
        -- auto.
    + refine (ASTJ_trans _ _ _).
      * refine (OSTJ_ifThenElse_false).
      * refine (ASTJ_trans _ _ _).
        -- refine (OSTJ_sum _).
           simpl. reflexivity.
        -- exact ASTJ_refl.
Qed. *)

Ltac transition_solver :=
  repeat (
    (eapply ASTJ_refl)
    ||
    (eapply ASTJ_trans; repeat (
      (eapply OSTJ_sum; reflexivity) ||
      (eapply OSTJ_plus_right; (only 1: eapply VJ_num)) ||
      (eapply OSTJ_plus_left) ||
      (eapply OSTJ_isZero_true) ||
      (eapply OSTJ_isZero_false; eapply gt_Sn_O) ||
      (eapply OSTJ_isZero) ||
      (eapply OSTJ_ifThenElse_true) ||
      (eapply OSTJ_ifThenElse_false) ||
      (eapply OSTJ_ifThenElse)
    ))
  )
.

(*
  2.19. Lemma.
  No transition from val.
*)

Lemma no_val_transition :
  forall t t' : Tm, ~ ((t val) /\ (t |-> t'))
.
Proof.
  unfold not. intros. inversion H.
  induction H1; inversion H0.
Qed.


(*
  2.20. Lemma.
  Determinism.
*)

Lemma determinism {t t'} :
  (t |-> t') -> (forall t'' : Tm, (t |-> t'') -> (t' = t''))
.
Proof.
  intros H.
  induction H.

  (* sum *)
  - intros. inversion H0.
    + rewrite <- H. rewrite <- H4. reflexivity.
    + inversion H4.
    + inversion H5.

  (* isZero_true *)
  - intros. inversion H.
    + reflexivity.
    + inversion H1.
    + inversion H1.

  (* isZero_false *)
  - intros. inversion H0.
    + rewrite <- H2 in H. inversion H.
    + reflexivity.
    + inversion H2.

  (* ifThenElse_true *)
  - intros. inversion H.
    + reflexivity.
    + inversion H4.

  (* ifThenElse_false *)
  - intros. inversion H.
    + reflexivity.
    + inversion H4.

  (* plus_left *)
  - intros. inversion H0.
    + rewrite <- H1 in *. inversion H.
    + pose (ir := IHOneStepTransitionJudgement t1'0 H4).
      rewrite ir. reflexivity.
    + pose (nvt := no_val_transition t1 t1').
      unfold not in nvt.
      pose (f := nvt (conj H3 H)). inversion f.

  (* plus_right *)
  - intros. inversion H1.
    + rewrite <- H4 in *. inversion H0.
    + pose (nvt := no_val_transition t1 t1').
      unfold not in nvt.
      pose (f := nvt (conj H H5)). inversion f.
    + pose (ir := IHOneStepTransitionJudgement t2'0 H6).
      rewrite ir. reflexivity.

  (* isZero *)
  - intros. inversion H0.
    + rewrite <- H2 in *. inversion H.
    + rewrite <- H1 in *. inversion H.
    + pose (ir := IHOneStepTransitionJudgement t'0 H2).
      rewrite ir. reflexivity.

  (* ifThenElse *)
  - intros. inversion H0.
    + rewrite <- H2 in *. inversion H.
    + rewrite <- H2 in *. inversion H.
    + pose (ir := IHOneStepTransitionJudgement t'0 H5).
      rewrite ir. reflexivity.
Qed.

(*
  2.29. Lemma
*)
Lemma progress_helper_Nat {t : Tm} :
  (t :: Nat) -> (t val) -> (exists n : nat, t = num n)
.
Proof.
  intros. inversion H0.
  + refine (ex_intro _ _ _). reflexivity.
  + rewrite <- H1 in *. inversion H.
  + rewrite <- H1 in *. inversion H.
Qed.

Lemma progress_helper_Bool {t : Tm} :
  (t :: Bool) -> (t val) -> (t = true \/ t = false).
Proof.
  intros.
  inversion H0.
  + subst. inversion H.
  + left. trivial.
  + right. trivial.
Qed.

Theorem progress {t : Tm} {A : Ty} :
  (t :: A) -> t val \/ (exists t' : Tm, t |-> t').
Proof.
  intros. induction H.
  + left. apply VJ_num.
  + right. destruct IHTypeJudgement1; destruct IHTypeJudgement2.
    - pose (lhs := progress_helper_Nat H H1).
      pose (rhs := progress_helper_Nat H0 H2).
      inversion lhs. inversion rhs. subst.
      eapply (ex_intro ). eapply OSTJ_sum. trivial.
    - pose (lhs := progress_helper_Nat H H1).
      inversion lhs. subst.
      inversion H2. 
      (* all used variables must be in the context before applying ex_intro *)
      eapply ex_intro. eapply OSTJ_plus_right.
      * exact H1.
      * exact H3.
     - pose (rhs := progress_helper_Nat H0 H2).
       inversion rhs. subst.
       inversion H1.
       eapply ex_intro.
       eapply OSTJ_plus_left. exact H3.
     - inversion H1. inversion H2.
       eapply ex_intro. eapply OSTJ_plus_left. exact H3.
  
  (* isZero *)
  + right. destruct IHTypeJudgement.
    - pose (lem := progress_helper_Nat H H0). 
      inversion lem. subst. 
      destruct x; eapply ex_intro.
      * eapply OSTJ_isZero_true.
      * eapply OSTJ_isZero_false. apply gt_Sn_O.
    - inversion H0. eapply ex_intro. eapply OSTJ_isZero. exact H1.
  
  (* true *)  
  + left. apply VJ_true.
  
  (* false *)  
  + left. apply VJ_false.
  
  (* IfThenElse *)
  + destruct IHTypeJudgement1.
    - right. pose (lem := progress_helper_Bool H H2).
      destruct lem; subst.
      * eapply ex_intro. eapply OSTJ_ifThenElse_true.
      * eapply ex_intro. eapply OSTJ_ifThenElse_false.
    - right. inversion H2. eapply ex_intro. eapply OSTJ_ifThenElse. exact H3.
Qed.

Theorem type_preservation {t t' : Tm} :
  (t |-> t') -> (forall A : Ty, (t :: A) -> (t' :: A)).
Proof.
  intros H. induction H; intros.
  (* num *)
  + inversion H0. subst. apply TJ_num.
  (* true *)
  + inversion H. subst. apply TJ_true.
  (* false *)
  + inversion H0. apply TJ_false.
  (* IfThenElse *)
  + inversion H. subst. exact j'.
  + inversion H. subst. exact j''.
  (* Plus *)
  + inversion H0. subst. eapply TJ_plus.
    - apply IHOneStepTransitionJudgement. exact j.
    - exact j'.
  + inversion H1. subst. apply TJ_plus.
    - exact j.
    - apply IHOneStepTransitionJudgement. exact j'.
  (* isZero *)
  + inversion H0. subst. apply TJ_isZero.
    apply IHOneStepTransitionJudgement. exact j.
  (* IfThenElse condition rewrite *)
  + inversion H0. subst. apply TJ_ifThenElse.
    - apply IHOneStepTransitionJudgement. exact j.
    - exact j'.
    - exact j''.
Qed.










