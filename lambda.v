(* Require Import String. *)
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Lists.ListSet.

Open Scope string_scope.
(* Open Scope list_scope. *)
Import ListNotations.


(* -=- Var -=- *)

Definition Var := string.
Definition Var_dec := string_dec.

Definition x := "x".
Definition y := "y".
Definition z := "z".

(* Opaque x y z. *)


(* -=- VarSet -=- *)

Module VarSet.

  Definition empty := empty_set Var.
  Definition add := set_add Var_dec.
  Definition mem := set_mem Var_dec.
  Definition remove := set_remove Var_dec.
  Definition inter := set_inter Var_dec.
  Definition union := set_union Var_dec.
  Definition diff := set_diff Var_dec.

  Definition singleton (v : Var) : set Var := add v empty.

  Definition Subset (s1 s2 : set Var) :=
    forall v : Var, In v s1 -> In v s2.

  Lemma union_subset1 :
    forall s1 s2 : set Var, Subset s1 (union s1 s2).
  Proof.
    unfold Subset. intros.
    eapply set_union_intro1.
    exact H.
  Qed.

  Lemma union_subset2 :
    forall s1 s2 : set Var, Subset s2 (union s1 s2).
  Proof.
    unfold Subset. intros.
    eapply set_union_intro2.
    exact H.
  Qed.

End VarSet.

(* -=- Tm -=- *)

Inductive Tm : Set :=
  | variable    (v : Var)          : Tm
  | lambda      (v : Var) (t : Tm) : Tm
  | application (t t' : Tm)        : Tm
.

Notation "' v" := (variable v) (at level 3).
Notation "\ v , t" := (lambda v t) (at level 5).
Notation "t $ t'" := (application t t') (at level 4).


(* -=- Free -=- *)

(*
Fixpoint free (tm : Tm) : set Var :=

.

Compute (free (\x , 'x $ 'y)). (* Should be {y} *)
Compute (free (\x , \y , 'x $ 'y)). (* Should be {} *)
Compute (free (\x , 'y $ (\y , 'y $ 'z))). (* Should be {y,z} *)
*)


(* -=- Rename -=- *)

Reserved Notation "t { x |-> y }" (at level 1).

Fixpoint rename (tm : Tm) (y z : Var) : Tm :=
match tm with
  | 'x     => if x =? y then 'z else 'x
  | \x, t  => if x =? y then \z,t {y |->z} else \x,t {y|-> z}
  | t $ t' => t{y |-> z} $ t'{y |-> z}
end
where "t { y |-> z }" := (rename t y z).

Compute (rename (\x,'x) x y).


(* -=- Substitute -=- *)

Reserved Notation "t [ x |-> t' ]" (at level 2).

Fixpoint substitute (tm : Tm) (x : Var) (tm' : Tm) : Tm :=

where "t [ x |-> t' ]" := (substitute t x t').

Compute (' x $ (\x, 'x $ ' x))[x |-> ' z].
Compute (\y,'z)[z |-> 'y].

(* -=- context -=- *)

Definition context := list Var.
Definition empty : context := nil.


(* -=- Closed -=- *)

Inductive Closed' : context -> Tm -> Prop :=

.

Definition Closed := Closed' empty.

(* Ltac proove_closed :=

.

Lemma closed_test1 : Closed (\x,'x$'x).
Proof.
  proove_closed.
Qed.

Lemma closed_test2 : Closed (\x,\y,'y$'x).
Proof.
  proove_closed.
Qed. *)



(* -=- One Step Transition Judgement -=- *)

Reserved Notation "t |--> t'" (at level 100).

Inductive OneStepTransitionJudgement : Tm -> Tm -> Prop :=

where "t |--> t'" := (OneStepTransitionJudgement t t').


(* -=- Any Step Transition Judgement -=- *)

Reserved Notation "t |-->* t'" (at level 100).

Inductive AnyStepTransitionJudgement : Tm -> Tm -> Prop :=
  | ASTJ_refl {t t' : Tm} :
    t |-->* t'
  | ASTJ_trans {t t'' : Tm} (t' : Tm) : 
    (t |--> t') -> (t' |-->* t'') ->
    t |-->* t''
where "t |-->* t'" := (AnyStepTransitionJudgement t t').


Definition true := \x,\y,'x.
Definition false := \x,\y,'y.
(* Definition and := . *)

Lemma and1 : and $ true $ true |-->* true.
Proof.
  
Qed.

Lemma and2 : and $ true $ false |-->* false.
Proof.
  
Qed.

Lemma and3 : and $ false $ true |-->* false.
Proof.
  
Qed.

Lemma and4 : and $ false $ false |-->* false.
Proof.
  
Qed.

