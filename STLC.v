Set Warnings "-notation-overridden,-parsing".
Require Import String.
Require Import Coq.Init.Nat.
Require Import Coq.Bool.Bool.
Require Import Coq.Sets.Ensembles.

(* The Simply-Typed Lambda Calculus *)

(* STLC types *)
Inductive ltype : Type :=
    | TNat : ltype
    | TBool : ltype
    | TArrow : ltype -> ltype -> ltype.

(* Binary operators *)
Inductive bop : Type :=
    | EAdd 
    | EMul
    | ESub
    | EEq
    | ELe
    | EAnd
    | EOr.

(* STLC expressions *)
Inductive expr : Type :=
    | ENat : nat -> expr
    | EBool : bool -> expr
    | EVar : string -> expr
    | ENot : expr -> expr
    | EBOp : bop -> expr -> expr -> expr
    | ECond : expr -> expr -> expr -> expr
    | ELam : string -> ltype -> expr -> expr
    | EApp : expr -> expr -> expr.

(* Gamma *)
Definition gamma := string -> option ltype.

Definition empty : gamma := fun x => None.

Definition bind (x : string) (t : ltype) (g : gamma) : gamma :=
    fun y => if String.eqb x y then Some t else g y.

(* Static Semantics *)
Inductive checks : gamma -> expr -> ltype -> Prop :=
    | natchecks : forall (g : gamma) (n : nat), checks g (ENat n) TNat
    | boolchecks : forall (g : gamma) (b : bool), checks g (EBool b) TBool
    | varchecks : forall (g : gamma) (x : string) (t : ltype), 
        g x = Some t -> checks g (EVar x) t
    | notchecks : forall (g : gamma) (e : expr), 
        checks g e TBool -> checks g (ENot e) TBool
    | addchecks : forall (g : gamma) (e1 e2 : expr),
        checks g e1 TNat -> checks g e2 TNat -> checks g (EBOp EAdd e1 e2) TNat
    | mulchecks : forall (g : gamma) (e1 e2 : expr),
        checks g e1 TNat -> checks g e2 TNat -> checks g (EBOp EMul e1 e2) TNat
    | subchecks : forall (g : gamma) (e1 e2 : expr),
        checks g e1 TNat -> checks g e2 TNat -> checks g (EBOp ESub e1 e2) TNat
    | eqchecks : forall (g : gamma) (e1 e2 : expr),
        checks g e1 TNat -> checks g e2 TNat -> checks g (EBOp EEq e1 e2) TBool
    | lechecks : forall (g : gamma) (e1 e2 : expr),
        checks g e1 TNat -> checks g e2 TNat -> checks g (EBOp ELe e1 e2) TBool
    | andchecks : forall (g : gamma) (e1 e2 : expr),
        checks g e1 TBool -> checks g e2 TBool -> checks g (EBOp EAnd e1 e2) TBool
    | orchecks : forall (g : gamma) (e1 e2 : expr),
        checks g e1 TBool -> checks g e2 TBool -> checks g (EBOp EOr e1 e2) TBool
    | condchecks : forall (g : gamma) (e1 e2 e3 : expr) (t : ltype),
        checks g e1 TBool -> checks g e2 t -> checks g e3 t ->
        checks g (ECond e1 e2 e3) t
    | lamchecks : forall (g : gamma) (x : string) (t t' : ltype) (e : expr),
        checks (bind x t g) e t' -> checks g (ELam x t e) (TArrow t t')
    | appchecks : forall (g : gamma) (e1 e2 : expr) (t t' : ltype),
        checks g e1 (TArrow t t') -> checks g e2 t -> checks g (EApp e1 e2) t'.

(* Free Variables *)
Fixpoint fv (e : expr) : Ensemble string := 
    match e with
    | ENat _  => Empty_set string
    | EBool _ => Empty_set string
    | EVar x  => Singleton string x
    | ENot e  => fv e
    | EBOp _ e1 e2 => Union string (fv e1) (fv e2)
    | ECond e1 e2 e3 => Union string (Union string (fv e1) (fv e2)) (fv e3)
    | ELam x _ e => Setminus string (fv e) (Singleton string x)
    | EApp e1 e2 => Union string (fv e1) (fv e2)
    end.

(* Dynamic Semantics *)
Inductive step : expr -> expr -> Prop :=
    | addstep : forall (n1 n2 : nat),
        step (EBOp EAdd (ENat n1) (ENat n2)) (ENat (n1 + n2))
    | mulstep : forall (n1 n2 : nat),
        step (EBOp EMul (ENat n1) (ENat n2)) (ENat (n1 * n2))
    | substep : forall (n1 n2 : nat),
        step (EBOp ESub (ENat n1) (ENat n2)) (ENat (n1 - n2))
    | eqstep : forall (n1 n2 : nat),
        step (EBOp EEq (ENat n1) (ENat n2)) (EBool (n1 =? n2))
    | lestep : forall (n1 n2 : nat),
        step (EBOp ELe (ENat n1) (ENat n2)) (EBool (n1 <? n2))
    | andstep : forall (b1 b2 : bool),
        step (EBOp EAnd (EBool b1) (EBool b2)) (EBool (andb b1  b2))
    | orstep : forall (b1 b2 : bool),
        step (EBOp EOr (EBool b1) (EBool b2)) (EBool (orb b1  b2))
    | left_nat_step : forall (op : bop) (n : nat) (e e' : expr),
        step e e' -> step (EBOp op (ENat n) e) (EBOp op (ENat n) e')
    | left_bool_step : forall (op : bop) (b : bool) (e e' : expr),
        step e e' -> step (EBOp op (EBool b) e) (EBOp op (EBool b) e')
    | right_bop_step : forall (op : bop) (e1 e1' e2 : expr),
        step e1 e1' -> step (EBOp op e1 e2) (EBOp op e1' e2)
    | truestep : forall (e2 e3 : expr),
        step (ECond (EBool true) e2 e3) e2
    | falsestep : forall (e2 e3 : expr),
        step (ECond (EBool false) e2 e3) e3
    | condstep : forall (e1 e1' e2 e3 : expr),
        step e1 e1' -> step (ECond e1 e2 e3) (ECond e1' e2 e3)
    | appstep : forall (e1 e1' e2 : expr),
        step e1 e1' -> step (EApp e1 e2) (EApp e1' e2).
    