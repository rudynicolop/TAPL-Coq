Set Warnings "-notation-overridden,-parsing".
Require Import String.

(* The Simply-Typed Lambda Calculus *)

(* STLC types *)
Inductive ltype : Type :=
    | TNat
    | TBool
    | TArrow (arg : ltype) (ret : ltype).

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
    | ENat (n : nat)
    | EBool (b : bool)
    | EVar (x : string)
    | ENot (e : expr)
    | EBOp (op : bop) (e1 : expr) (e2 : expr)
    | ECond (e1 : expr) (e2 : expr) (e3 : expr)
    | ELam (x : string) (t : ltype) (e : expr)
    | EApp (e1 : expr) (e2 : expr).

(* Notations *)

Coercion EVar : string >-> expr.
Coercion ENat : nat >-> expr.
Coercion EBool : bool >-> expr.

Bind Scope stlc_scope with ltype.
Bind Scope stlc_scope with expr.
Delimit Scope stlc_scope with stlc.

Notation "'Nat'" := (TNat) (at level 20, no associativity) : stlc_scope.
Notation "'Bool'" := (TBool) (at level 20, no associativity) : stlc_scope.
Notation "x --> y" := (TArrow x y) (at level 30, right associativity) : stlc_scope.

Notation "x + y" := (EBOp EAdd x y) (at level 50, left associativity) : stlc_scope.
Notation "x - y" := (EBOp ESub x y) (at level 50, left associativity) : stlc_scope.
Notation "x * y" := (EBOp EMul x y) (at level 40, left associativity) : stlc_scope.
Notation "x < y" := (EBOp ELe x y) (at level 70, no associativity) : stlc_scope.
Notation "x = y" := (EBOp EEq x y) (at level 70, no associativity) : stlc_scope.
Notation "x & y" := (EBOp EAnd x y) (at level 74, left associativity) : stlc_scope.
Notation "x | y" := (EBOp EOr x y) (at level 76, left associativity) : stlc_scope.
Notation "!! b" := (EBOp EAdd b) (at level 72, right associativity) : stlc_scope.
Notation "'If' x 'Then' y 'Else' z" := (ECond x y z) (at level 80, no associativity) : stlc_scope.
Notation "'Fun' x :: t =>> e" := (ELam x t e) (at level 90, no associativity) : stlc_scope.
Notation "x $ y" := (EApp x y) (at level 10, left associativity) : stlc_scope.

(* Definition arith_ex : expr := Fun x :: (Nat) =>> 4.

Print arith_ex. *)
