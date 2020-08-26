(* An extended STLC with subtyping via the Subsumption Rule *)

Require Import String.
Require Import Coq.Strings.String.
Local Open Scope string_scope.
Require Import Coq.Lists.List.
Import ListNotations.
Require Coq.MSets.MSetWeakList.
Module WS := Coq.MSets.MSetWeakList.
Require Coq.MSets.MSetFacts.
Module MSF := Coq.MSets.MSetFacts.
Require Coq.Structures.Equalities.
Module SE := Coq.Structures.Equalities.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Lists.SetoidPermutation.
    
Definition id := string.

Definition field (t : Type) : Type := id * t.

Definition fields (t : Type) : Type := list (field t).

Definition predf {U : Type} (P : U -> Prop) : field U -> Prop := fun f => P (snd f).

Definition predfs {U : Type} (P : U -> Prop) (fs : fields U) : Prop := Forall (predf P) fs.

Inductive type : Type :=
    | TTop
    | TUnit
    | TFun (t t' : type)
    | TRec (fs : fields type).

(* automatically generated induction principle is weak *)
Check type_ind.
Compute type_ind.
Compute type_rect.

(* custom induction principle for Type type *)
Section TypeInduction.
    Variable P : type -> Prop.

    Hypothesis HTop : P TTop.

    Hypothesis HUnit : P TUnit.

    Hypothesis HFun : forall (t t' : type),
        P t -> P t' -> P (TFun t t').

    Hypothesis HRec : forall (fs : fields type),
        predfs P fs -> P (TRec fs).

    Fixpoint IHType (t : type) : P t.
    Proof.
        destruct t.
        - assumption.
        - assumption.
        - apply HFun; apply IHType.
        - apply HRec. induction fs; constructor.
            + apply IHType.
            + assumption.
    Qed.
End TypeInduction.

Ltac indtype t := induction t using IHType.

(* The Subtyping Relation *)
Inductive subtype : type -> type -> Prop :=
    | st_refl : forall (t : type), 
        subtype t t
    | st_trans : forall (t u v : type),
        subtype t u -> 
        subtype u v ->
        subtype t v
    | st_top : forall (t : type),
        subtype t TTop
    | st_fun : forall (u u' v v' : type),
        subtype u' u ->
        subtype v v' ->
        subtype (TFun u v) (TFun u' v')
    | st_rec_width : forall (us vs : fields type),
        subtype (TRec (us ++ vs)) (TRec us)
    | st_rec_depth : forall (us vs : fields type),
        Forall2 
            (fun u v => 
                (fst u) = (fst v) /\ 
                subtype (snd u) (snd v)) 
            us vs ->
        subtype (TRec us) (TRec vs)
    | st_rec_perm : forall (us vs : fields type),
        PermutationA (fun u v => u = v) us vs ->
        subtype (TRec us) (TRec vs).

Section Gamma.
    Definition gamma := string -> option type.

    Definition empty : gamma := fun x => None.

    Definition bind (x : string) (t : type) (g : gamma) : gamma :=
        fun y => if String.eqb x y then Some t else g y.

    Lemma bind_correct : 
        forall (x : id) (t : type) (g : gamma),
        bind x t g x = Some t.
    Proof.
        intros. unfold bind. destruct ((x =? x)%string) eqn:eq.
        - reflexivity.
        - apply eqb_neq in eq. contradiction.
    Qed. 

    Lemma bind_complete :
        forall (x x' : id) (t t' : type) (g : gamma),
        x' <> x -> (g x = Some t <-> bind x' t' g x = Some t). 
    Proof.
        intros. unfold bind. apply eqb_neq in H. 
        rewrite H. split; intros; apply H0.
    Qed.

    Lemma rebind_correct : 
        forall (x : id) (t t' : type) (g : gamma),
        bind x t g = bind x t (bind x t' g).
    Proof.
        intros. apply functional_extensionality. intros y.
        unfold bind. destruct ((x =? y)%string); reflexivity.
    Qed.

    Lemma bind_diff_comm : 
        forall (x y : id) (u v : type) (g : gamma),
        x <> y ->
        bind x u (bind y v g) = bind y v (bind x u g).
    Proof.
        intros. apply functional_extensionality. intros z.
        unfold bind. destruct ((x =? z)%string) eqn:eq.
            - apply eqb_eq in eq; subst.
                destruct ((y =? z)%string) eqn:eeq.
                + apply eqb_eq in eeq; subst. contradiction.
                + reflexivity.
            - apply eqb_neq in eq. destruct ((y =? z)%string) eqn:eeq; reflexivity.
    Qed.
End Gamma.

Inductive expr : Type :=
    | EUnit
    | EVar (x : id)
    | EFun (x : id) (t : type) (e : expr)
    | EApp (e1 e2 : expr)
    | ERec (fs : fields expr)
    | EPrj (e : expr) (x : id).

(* custom induction principle for Type expr *)
Section ExprInduction.
    Variable P : expr -> Prop.

    Hypothesis HUnit : P EUnit.

    Hypothesis HVar : forall (x : id), P (EVar x).

    Hypothesis HFun : forall (x : id) (t : type) (e : expr),
        P e -> P (EFun x t e).

    Hypothesis HApp : forall (e1 e2 : expr),
        P e1 -> P e2 -> P (EApp e1 e2).

    Hypothesis HRec : forall (fs : fields expr),
        predfs P fs -> P (ERec fs).

    Hypothesis HPrj : forall (e : expr) (x : id),
        P e -> P (EPrj e x).

    Fixpoint IHExpr (e : expr) : P e.
    Proof.
        destruct e.
        - assumption.
        - apply HVar.
        - apply HFun; apply IHExpr.
        - apply HApp; apply IHExpr.
        - apply HRec. induction fs; constructor.
            + apply IHExpr.
            + assumption.
        - apply HPrj. apply IHExpr.
    Qed.
End ExprInduction.

Ltac indexpr e := induction e using IHExpr.

(* Typechecking with the subsumption rule *)
Inductive check (g : gamma) : expr -> type -> Prop :=
    | check_subsume : forall (e : expr) (u v : type),
        subtype u v ->
        check g e u ->
        check g e v
    | check_unit :
        check g EUnit TUnit
    | check_var : forall (x : id) (t : type),
        g x = Some t ->
        check g (EVar x) t
    | check_fun : forall (x : id) (u v : type) (e : expr),
        check (bind x u g) e v ->
        check g (EFun x u e) (TFun u v)
    | check_app : forall (e1 e2 : expr) (u v : type),
        check g e1 (TFun u v) ->
        check g e2 u ->
        check g (EApp e1 e2) v
    | check_rec : forall (es : fields expr) (ts : fields type),
        Forall2 
            (fun e t => 
                (fst e) = (fst t) /\
                check g (snd e) (snd t))
            es ts ->
        check g (ERec es) (TRec ts)
    | check_prj : forall (e : expr) (x : id) (t : type) (ts : fields type),
        In (x,t) ts ->
        check g e (TRec ts) ->
        check g (EPrj e x) t.

Definition checks : expr -> type -> Prop := check empty.

Example benjy : 
    checks 
        (EApp 
            (EFun "r" (TRec [("x",TUnit)]) 
                (EPrj (EVar "r") "x")) 
            (ERec [("x",EUnit);("y",EUnit)]))
        TUnit.
Proof.
    apply check_app with (u := TRec [("x",TUnit)]).
    - apply check_fun. apply check_prj with 
        (ts := [("x",TUnit)]);
        constructor; reflexivity.
    - apply check_subsume with 
        (u := TRec [("x", TUnit);("y",TUnit)]).
        + apply st_rec_width with
            (us := [("x",TUnit)])
            (vs := [("y",TUnit)]).
        + apply check_rec. constructor.
            { split; try reflexivity. constructor. }
            { constructor.
                - split.
                    + reflexivity.
                    + constructor.
                - constructor. }
Qed. 