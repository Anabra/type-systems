Require Import Coq.Structures.Equalities.

(*
  Definitions of Tm, Ty and Judgement.
  Do not modify these!

  The task starts at line 38.
*)

Inductive Tm : Set :=
  | Num (n : nat)
  | Plus (t t' : Tm)
  | IsZero (t : Tm)
  | True
  | False
  | IfThenElse (t t' t'' : Tm)
.

Notation "t + t'" := (Plus t t').
Notation "'If' t 'then' t' 'else' t''" := (IfThenElse t t' t'') (at level 100).

Inductive Ty : Set := Nat | Bool.

Fixpoint eqTy (lhs rhs : Ty) : bool :=
  match lhs, rhs with
  | Nat, Nat   => true
  | Bool, Bool => true
  | _, _       => false
  end
. 

Inductive Judgement : Tm -> Ty -> Prop :=
  | JNum    {n : nat}                                   : (Num n)    :: Nat
  | JPlus   {t t' : Tm} (j : t :: Nat) (j' : t' :: Nat) : (t + t')   :: Nat
  | JIsZero {t : Tm}    (j : t :: Nat)                  : (IsZero t) :: Bool
  | JTrue                                               : True       :: Bool
  | JFalse                                              : False      :: Bool

  | JIfThenElse
    {t t' t'' : Tm} {A : Ty}
    (j : t :: Bool) (j' : t' :: A) (j'' : t'' :: A)
    : (If t then t' else t'') :: A

where "tm :: ty" := (Judgement tm ty).

Fixpoint infer (tm : Tm) : option Ty :=
  match tm with 
  | Num _ => Some Nat
  | Plus lhs rhs => match infer lhs, infer rhs with 
    | Some Nat, Some Nat => Some Nat
    | _, _ => None
    end
  | IsZero n => match infer n with
    | Some Nat => Some Bool
    | _ => None 
    end
  | True => Some Bool
  | False => Some Bool 
  | IfThenElse b thenBr elseBr => match infer b, infer thenBr, infer elseBr with
    | Some Bool, Some thenTy, Some elseTy => 
      if eqTy thenTy elseTy then Some thenTy else None
    | _, _, _ => None
    end
  end
.

Theorem infer_IsZero : forall (tm : Tm) (ty : Ty), infer (IsZero tm) = Some ty -> tm :: ty.
Proof.
  intros. induction tm.
Abort.

Theorem completeness : forall tm (ty : Ty), tm :: ty -> infer tm = Some ty.
Proof.
  induction tm.
  + intros. compute. inversion H. auto.
  + intros. inversion H. simpl. 
    pose (ir1 := IHtm1 Nat j).
    pose (ir2 := IHtm2 Nat j').
    rewrite ir1.
    rewrite ir2.
    trivial.
  + intros. inversion H. simpl.
    pose (ir1 := IHtm Nat j).
    rewrite ir1.
    trivial.
  + intros. inversion H. auto.
  + intros. inversion H. auto.
  + intros. destruct ty.
    - inversion H. simpl.
      rewrite (IHtm1 Bool j).
      rewrite (IHtm2 Nat j').
      rewrite (IHtm3 Nat j'').
      auto.
    - inversion H. simpl.
      rewrite (IHtm1 Bool j).
      rewrite (IHtm2 Bool j').
      rewrite (IHtm3 Bool j'').
      auto.
Qed.

Lemma infer_plus {lhs rhs : Tm} {ty : Ty} : 
  infer (lhs + rhs) = Some ty ->
  ty = Nat /\ infer lhs = Some Nat /\ infer rhs = Some Nat.
Proof.
  intros. simpl in H. destruct (infer lhs).
    +
  
  
  destruct (infer (lhs + rhs)).
  Focus 2. 
    intros. discriminate.
  Focus 1.
    intros. inversion H. apply conj.
    + 
Qed.

Theorem soundness : forall tm (ty : Ty), infer tm = Some ty -> tm :: ty.
Proof.
  intros.
  induction tm.
  Focus 1. unfold infer in H. injection H. intros. rewrite <- H0. apply JNum.
  Focus 3. unfold infer in H. injection H. intros. rewrite <- H0. apply JTrue.
  Focus 3. unfold infer in H. injection H. intros. rewrite <- H0. apply JFalse.
  Focus 2. destruct tm.
    + injection H. intros. rewrite <- H0. apply JIsZero. apply JNum.
    +  
    
     (* destruct. injection. compute. apply *)
  + destruct tm1; compute in H.
    - desctrut tm2; compute in H.
      * injection H. intros. 
        rewrite <- H0 in IHtm1.
        rewrite <- H0 in IHtm2.
        rewrite <- H0.
        apply JPlus.
        ** apply IHtm1. auto.
        ** apply IHtm2. auto.
      *  
Abort.