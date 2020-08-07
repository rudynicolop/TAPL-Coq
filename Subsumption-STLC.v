(* An extended STLC with subtyping via the Subsumption Rule *)

Require Import String.
Require Import Coq.Strings.String.
Require Coq.MSets.MSetWeakList.
Module WS := Coq.MSets.MSetWeakList.
Require Coq.MSets.MSetFacts.
Module MSF := Coq.MSets.MSetFacts.
Require Coq.Structures.Equalities.
Module SE := Coq.Structures.Equalities.
Require Import Coq.Logic.FunctionalExtensionality.
    
Definition id := string.

Inductive type : Type :=
    | TTop
    | TFun (t t' : type)
    | TRecord (fields : list (id * type)).

(* Need to define induction principle...yikes... *)