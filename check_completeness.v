(*
  Definitions and proofs from previous classes.
  Do not modify these!

  The task starts at line 240.
*)

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

Notation "t + t'" := (plus t t').
Notation "'If' t 'then' t' 'else' t''" := (ifThenElse t t' t'') (at level 100).


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

where "tm :: ty" := (TypeJudgement tm ty).


(*
  2.10. / a
  The infer function!
*)

Inductive infer_result : Set := success (ty : Ty) | fail.

Fixpoint infer (tm : Tm) : infer_result :=
  match tm with
   | num n => success Nat
   | (t + t') =>
     match (infer t), (infer t') with
      | success Nat, success Nat => success Nat
      | _, _ => fail
     end
   | isZero t =>
     match (infer t) with
      | success Nat => success Bool
      | _ => fail
     end
   | true => success Bool
   | false => success Bool
   | (If t then t' else t'') =>
     match (infer t), (infer t'), (infer t'') with
      | success Bool, success Bool, success Bool => success Bool
      | success Bool, success Nat, success Nat => success Nat
      | _, _, _ => fail
     end
  end
.


(*
  2.10. / b
  The theorem of completeness for the infer function!
*)

Theorem infer_completeness : (
  forall tm : Tm, forall ty: Ty, tm :: ty -> infer tm = success ty
).
Proof.
  induction tm.

  (* num n *)
  - intros. simpl. inversion H. reflexivity.

  (* t + t' *)
  - intros. inversion H.
    pose (ir1 := IHtm1 Nat j).
    pose (ir2 := IHtm2 Nat j').
    simpl. rewrite ir1. rewrite ir2.
    reflexivity.

  (* isZero t *)
  - intros. inversion H.
    pose (ir := IHtm Nat j).
    simpl. rewrite ir.
    reflexivity.

  (* true *)
  - intros. simpl. inversion H. reflexivity.

  (* false *)
  - intros. simpl. inversion H. reflexivity.

  (* If t then t' else t'' *)
  - intros ty.
    case ty.

    (* Nat *)
    + intros. inversion H.
      pose (ir1 := IHtm1 Bool j).
      pose (ir2 := IHtm2 Nat j').
      pose (ir3 := IHtm3 Nat j'').
      simpl. rewrite ir1. rewrite ir2. rewrite ir3.
      reflexivity.

    (* Bool *)
    + intros. inversion H.
      pose (ir1 := IHtm1 Bool j).
      pose (ir2 := IHtm2 Bool j').
      pose (ir3 := IHtm3 Bool j'').
      simpl. rewrite ir1. rewrite ir2. rewrite ir3.
      reflexivity.
Qed.


(* Helper lemmas for soundness. *)

Lemma plus_helper {tm tm' : Tm} {ty : Ty} : (
  infer (tm + tm') = success ty -> 
  ty = Nat /\ (infer tm = success Nat) /\ (infer tm' = success Nat)
).
Proof.
  simpl. case (infer tm), (infer tm').

  (* success ty0, success ty1 *)
  - case ty0, ty1; intros; inversion H. refine (conj _ (conj _ _)); reflexivity.

  (* success ty0, fail *)
  - case ty0; intros; inversion H.

  (* fail, success ty0 *)
  - intros; inversion H.

  (* fail, fail *)
  - intros; inversion H.
Qed.

Lemma isZero_helper {tm : Tm} {ty : Ty} : (
  infer (isZero tm) = success ty -> 
  ty = Bool /\ (infer tm = success Nat)
).
Proof.
  simpl. case (infer tm).

  (* success ty0 *)
  - intros ty0; case ty0; intros; inversion H; refine (conj _ _); reflexivity.

  (* fail *)
  - intros; inversion H.
Qed.

Lemma ifThenElse_helper {tm tm' tm'' : Tm} {ty : Ty} : (
  infer (If tm then tm' else tm'') = success ty -> 
  infer tm = success Bool /\ (infer tm' = success ty) /\ (infer tm'' = success ty)
).
Proof.
  simpl. case (infer tm).
  - intros ty0. case ty0.
    + intros; inversion H.
    + case (infer tm'), (infer tm'').
      * case ty1, ty2; intros; inversion H; refine (conj _ (conj _ _)); reflexivity.
      * case ty1; intros; inversion H.
      * intros; inversion H.
      * intros; inversion H.
  - intros; inversion H.
Qed.


(*
  2.10. / c
  The theorem of soundness for the infer function.
*)

Theorem infer_soundness : (
  forall tm : Tm, forall ty: Ty, infer tm = success ty -> tm :: ty
).
Proof.
  induction tm.

  (* num n *)
  - simpl. intros. inversion H. exact (TJ_num).

  (* t + t' *)
  - intros.
    pose (H0 := plus_helper H); destruct H0; destruct H1.
    rewrite H0. exact (TJ_plus (IHtm1 _ H1) (IHtm2 _ H2)).

  (* isZero t *)
  - intros.
    pose (H0 := isZero_helper H); destruct H0.
    rewrite H0. exact (TJ_isZero (IHtm _ H1)).

  (* true *)
  - simpl; intros; inversion H; exact (TJ_true).

  (* false *)
  - simpl; intros; inversion H; exact (TJ_false).

  (* If t then t' else t'' *)
  - intros.
    pose (H0 := ifThenElse_helper H); destruct H0; destruct H1.
    exact (TJ_ifThenElse (IHtm1 _ H0) (IHtm2 _ H1) (IHtm3 _ H2)).
Qed.


(*
  2.11. / 2.12.
  Define a check : Tm x Ty -> {succes, fail} function
  that returns check(t,A) = success if and only if t :: A.
*)

Inductive check_result : Set := check_success | check_fail.

Definition check (tm : Tm) (ty : Ty) : check_result :=
  match (infer tm), ty with
   | success Nat, Nat => check_success
   | success Bool, Bool => check_success
   | _, _ => check_fail
  end
.


(* ------------------------------ *)

(*
  Proove the completeness of the check function!
  (If there exists a term "tm" and type "ty", for which the judgement "tm :: ty"
  can be constructed, then "check tm ty" returns with success.)
*)

Theorem check_completeness :
  forall tm : Tm, forall ty : Ty,
  tm :: ty -> check tm ty = check_success
.
Proof.
  intros tm ty H. unfold check.
  case_eq (infer tm).
  + intros. destruct ty; destruct ty0; (try trivial);
    (pose (H1 := infer_completeness _ _ H); rewrite H0 in H1; discriminate).
  + intros. pose (H1 := infer_completeness _ _ H). rewrite H0 in H1. discriminate.
Qed.