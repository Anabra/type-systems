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

  Fixpoint remove (v : Var) (s : set Var) : set Var :=
    match s with
    | nil => nil
    | v' :: s' =>
      match Var_dec v v' with
      | left _ => remove v s'
      | right _ => v' :: remove v s'
      end
    end
  .

  Definition inter := set_inter Var_dec.
  Definition union := set_union Var_dec.
  Definition diff := set_diff Var_dec.

  Definition singleton (v : Var) : set Var := add v empty.

  Definition Subset (s1 s2 : set Var) :=
    forall v : Var, In v s1 -> In v s2.

End VarSet.


(* -=- Tm -=- *)

Inductive Tm : Set :=
| variable (v : Var) : Tm
| lambda (v : Var) (t : Tm) : Tm
| application (t t' : Tm) : Tm
.

Notation "' v" := (variable v) (at level 3).
Notation "\ v , t" := (lambda v t) (at level 5).
Notation "t $ t'" := (application t t') (at level 4).


(* -=- Free -=- *)

Fixpoint free (tm : Tm) : set Var :=
  match tm with
  | ' v     => VarSet.singleton v
  | \ v , t => VarSet.remove v (free t)
  | t $ t'  => VarSet.union (free t) (free t')
  end
.

Compute (free (\x , 'x $ 'y)). (* Should be {y} *)
Compute (free (\x , \y , 'x $ 'y)). (* Should be {} *)
Compute (free (\x , 'y $ (\y , 'y $ 'z))). (* Should be {y,z} *)


(* -=- Rename -=- *)

Reserved Notation "t { x |-> y }" (at level 1).

Fixpoint rename (tm : Tm) (y z : Var) : Tm :=
  match tm with
  | ' x     => if x =? y then 'z else 'x
  | \ x , t => if x =? y then \z,t{y|->z} else \x,t{y|->z}
  | t $ t'  => t{y|->z} $ t'{y|->z}
  end
where "t { y |-> z }" := (rename t y z).

Compute (rename (\x,'x) x y).


(* -=- Substitute -=- *)

Reserved Notation "t [ x |-> t' ]" (at level 2).

Fixpoint substitute (tm : Tm) (x : Var) (tm' : Tm) : Tm :=
  match tm with
  | ' y     => if x =? y then tm' else ' y
  | \ y , t => if x =? y then \y,t else \y,t[x|->tm']
  | t $ t'  => t[x|->tm'] $ t'[x|->tm']
  end
where "t [ x |-> t' ]" := (substitute t x t').

Compute (' x $ (\x, 'x $ ' x))[x |-> ' z].
Compute (\y,'z)[z |-> 'y].

(* -=- context -=- *)

Definition context := list Var.
Definition empty : context := nil.


(* -=- Closed -=- *)

Inductive Closed' : context -> Tm -> Prop :=
| C_variable {c : context} {v : Var}           
  : In v c -> Closed' c ('v)
| C_lambda {c : context} {v : Var}  {t : Tm} 
  : Closed' (v :: c) t -> Closed' c (\v,t)
| C_application {c : context} {t t' : Tm}         
  : Closed' c t -> Closed' c t' -> Closed' c (t $ t')
.

(* Hint Constructors Closed'. *)

Definition Closed := Closed' empty.

Ltac prove_closed :=
  repeat (
    (
      eapply C_variable;
      simpl;
      repeat (
        (left; reflexivity) ||
        right
      )
    ) ||
    eapply C_lambda ||
    eapply C_application
  )
.

Lemma closed_test1 : Closed (\x,'x$'x).
Proof.
  prove_closed.
Qed.

Lemma closed_test2 : Closed (\x,\y,'y$'x).
Proof.
  prove_closed.
Qed.

Lemma closedSubset {tm : Tm} {c1 : context} :
  Closed' c1 tm ->
  forall c2 : context,
  VarSet.Subset c1 c2 -> Closed' c2 tm.
Proof.
  intro H. induction H.
  + intros. unfold VarSet.Subset in H0.
    eapply C_variable. exact (H0 _ H).
  + intros. eapply C_lambda. apply (IHClosed' (v :: c2)).
    unfold VarSet.Subset in *. 
    intros. inversion H1. subst.
    - simpl. left. trivial.
    - simpl. right. exact (H0 _ H2).
  + intros. eapply C_application.
    - exact (IHClosed'1 _ H1).
    - exact (IHClosed'2 _ H1).    
Qed.

(* -=- Closed Substitute -=- *)

Theorem closedSubstitute' {t t' : Tm} {v : Var} {c : context} :
  (* forall t t' : Tm, forall v : Var, forall c : context, *)
  Closed' c t -> ~ (In v c) -> t[v |-> t'] = t.
Proof.
  intros. induction H.
  + simpl. destruct (Var_dec v v0).
    - subst. unfold "~" in H0. exfalso. exact (H0 H).
    - pose (eq_iso := eqb_neq v v0). inversion eq_iso. rewrite (H2 n). 
      trivial.
  + simpl. destruct (Var_dec v v0).
    - subst. rewrite eqb_refl. trivial.
    - pose (eq_iso := eqb_neq v v0). inversion eq_iso. rewrite (H2 n).
      erewrite IHClosed'.
      * trivial.
      * apply not_in_cons. split. 
        ** exact n.
        ** exact H0.
  + simpl. rewrite (IHClosed'1 H0). rewrite (IHClosed'2 H0). trivial.
Qed.

Theorem closedSubstitute {t t' : Tm} {v : Var} : 
  (* forall t t' : Tm, forall v : Var, *)
  Closed t -> t[v |-> t'] = t.
Proof.
  intros. eapply (closedSubstitute' H).
  - simpl. unfold "~". intros. exact H0.
Qed.


(* -=- One Step Transition Judgement -=- *)

Reserved Notation "t |--> t'" (at level 100).

Inductive OneStepTransitionJudgement : Tm -> Tm -> Prop :=

| OSTJ_beta {x : Var} {t t1 : Tm} :
    Closed t1 ->
    ((\x,t) $ t1) |--> t[x |-> t1]

| OSTJ_lambda {x : Var} {t t' : Tm} :
    (t |--> t') ->
    \x,t |--> \x,t'

| OSTJ_application_left {t1 t1' t2 : Tm} :
    (t1 |--> t1') ->
    t1 $ t2 |--> t1' $ t2

| OSTJ_application_right {t1 t2 t2' : Tm} :
    (t2 |--> t2') ->
    t1 $ t2 |--> t1 $ t2'

where "t |--> t'" := (OneStepTransitionJudgement t t').


(* -=- Any Step Transition Judgement -=- *)

Reserved Notation "t |-->* t'" (at level 100).

Ltac beta_reduce := eapply OSTJ_beta; (prove_closed || assumption).

Inductive AnyStepTransitionJudgement : Tm -> Tm -> Prop :=
| ASTJ_refl {t : Tm} :
    t |-->* t
| ASTJ_trans {t t'' : Tm} (t' : Tm) : 
  (t |--> t') -> (t' |-->* t'') ->
  t |-->* t''
where "t |-->* t'" := (AnyStepTransitionJudgement t t').

Ltac reduce_lambda :=
  cbv delta in *; 
  (* perform only delta reduction *)
  (* https://coq.inria.fr/distrib/current/refman/proof-engine/tactics.html?highlight=cbv#coq:tacn.cbv *)
  repeat (
    apply ASTJ_refl || 
    ( eapply ASTJ_trans
    ; match goal with 
       | [ |- (\_, _) $ _ |--> _ ] => beta_reduce
       | [ |- _ $ _       |--> _ ] => eapply OSTJ_application_left; beta_reduce
       | _ => idtac (* we should "continue" from here *)
      end
    ; simpl
    )
  )
.

Definition inf := (\x , 'x $ 'x).

Lemma infinite : inf $ inf |--> inf $ inf.
Proof.
  unfold inf.
  eapply (@OSTJ_beta x).
  prove_closed.
  (* - eapply C_lambda. *)
  (*   eapply C_application. *)
  (*   + eapply C_variable. *)
  (*     simpl. left. reflexivity. *)
  (*   + eapply C_variable. *)
  (*     simpl. left. reflexivity. *)
Qed.


(* -=- true, false, and, or, not, ifThenElse -=- *)

Definition true := \x,\y,'x.
Definition false := \x,\y,'y.


Definition and := \x,\y,'x$'y$false.

Lemma andTrue (t : Tm) (ct : Closed t) : and $ true $ t |-->* t.
Proof.
  eapply ASTJ_trans. {
    eapply OSTJ_application_left.
    eapply OSTJ_beta; prove_closed.
  } simpl.

  eapply ASTJ_trans. {
    eapply OSTJ_beta; exact ct.
  } simpl.

  eapply ASTJ_trans. {
    eapply OSTJ_application_left.
    eapply OSTJ_beta; exact ct.
  } simpl.

  eapply ASTJ_trans. {
    eapply OSTJ_beta; prove_closed.
  } simpl.

  pose (cs := @closedSubstitute _ false y ct).
  unfold false in cs.
  rewrite cs.
  eapply ASTJ_refl.
Qed.

Lemma and1 : and $ true $ true |-->* true.
Proof.
  reduce_lambda.
Qed.

Lemma and2 : and $ true $ false |-->* false.
Proof.
  reduce_lambda.
Qed.

Lemma andFalse (t : Tm) (ct : Closed t) : and $ false $ t |-->* false.
Proof.
  reduce_lambda.
Qed.

Lemma and3 : and $ false $ true |-->* false.
Proof.
  reduce_lambda.
Qed.

Lemma and4 : and $ false $ false |-->* false.
Proof.
  reduce_lambda.
Qed.


Definition or := \x,\y,'x$true$'y.

Lemma orTrue (t : Tm) (ct : Closed t) : or $ true $ t |-->* true.
Proof.
  reduce_lambda.
Qed.

Lemma or1 : or $ true $ true |-->* true.
Proof.
  reduce_lambda.
Qed.

Lemma or2 : or $ true $ false |-->* true.
Proof.
  reduce_lambda.
Qed.

Lemma orFalse (t : Tm) (ct : Closed t) : or $ false $ t |-->* t.
Proof.
  reduce_lambda.
Qed.

Lemma or3 : or $ false $ true |-->* true.
Proof.
  reduce_lambda.
Qed.

Lemma or4 : or $ false $ false |-->* false.
Proof.
  reduce_lambda.
Qed.


Definition not := \x,'x$false$true.

Lemma not1 : not $ true |-->* false.
Proof.
  reduce_lambda.
Qed.

Lemma not2 : not $ false |-->* true.
Proof.
  reduce_lambda.
Qed.



Definition ifThenElse := \x,'x.

Lemma ifThenElse1 {t1 t2 : Tm} :
  Closed t1 -> Closed t2 ->
  (ifThenElse $ true $ t1 $ t2) |-->* t1.
Proof.
  intros.

  eapply ASTJ_trans. {
    eapply OSTJ_application_left.
    eapply OSTJ_application_left.
    beta_reduce.
  } simpl.

  eapply ASTJ_trans. {
    eapply OSTJ_application_left.
    beta_reduce.
  } simpl.

  eapply ASTJ_trans. {
    beta_reduce.
  } simpl.

  (* change t1[y |-> t2] with t1. *)

  (* pose (csr := @closedSubstitute t1 t2 y H). *)
  (* rewrite csr. *)

  assert (t1[y |-> t2] = t1). {
    eapply closedSubstitute.
    exact H.
  }
  rewrite H1.

  eapply ASTJ_refl.
Qed.

Lemma ifThenElse2 {t1 t2 : Tm} :
  Closed t1 -> Closed t2 ->
  (ifThenElse $ false $ t1 $ t2) |-->* t2.
Proof.
  intros.

  eapply ASTJ_trans. {
    eapply OSTJ_application_left.
    eapply OSTJ_application_left.
    beta_reduce.
  } simpl.

  eapply ASTJ_trans. {
    eapply OSTJ_application_left.
    beta_reduce.
  } simpl.

  eapply ASTJ_trans. {
    beta_reduce.
  } simpl.

  eapply ASTJ_refl.
Qed.

