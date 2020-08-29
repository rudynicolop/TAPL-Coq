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
Require Import Coq.Logic.Decidable.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Program.Equality.
    
Ltac inv H := inversion H; subst.

Definition id := string.

Definition field (t : Type) : Type := id * t.

Definition fields (t : Type) : Type := list (field t).

Definition predf {U : Type} (P : U -> Prop) (f : field U) : Prop := 
    P (snd f).

Definition predf_prop {U : Type} {V : Prop} (P : U -> V) (f : field U) : V :=
    P (snd f).

Definition predfs {U : Type} (P : U -> Prop) : fields U -> Prop := 
    Forall (predf P).

Definition perm {U : Type} (u1 : fields U) (u2 : fields U) : Prop :=
    Permutation u1 u2.

Definition relf {U V : Type} (R : U -> V -> Prop) (u : field U) (v : field V) : Prop :=
    (fst u) = (fst v) /\ R (snd u) (snd v).

Definition relfs {U V : Type} (R : U -> V -> Prop) : fields U -> fields V -> Prop :=
    Forall2 (relf R).

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
        relfs subtype us vs ->
        subtype (TRec us) (TRec vs)
    | st_rec_perm : forall (us vs : fields type),
        perm us vs ->
        subtype (TRec us) (TRec vs).

Check subtype_ind.

Section SubtypeInduction.
    Variable P : type -> type -> Prop.

    Hypothesis HRefl : forall (t : type), P t t.

    Hypothesis HTrans : forall (t u v : type),
        subtype t u -> P t u ->
        subtype u v -> P u v -> P t v.

    Hypothesis HTop : forall (t : type), P t TTop.

    Hypothesis HFun : forall (u u' v v' : type),
        subtype u' u -> P u' u ->
        subtype v v' -> P v v' ->
        P (TFun u v) (TFun u' v').

    Hypothesis HRecWidth : forall (us vs : fields type),
        P (TRec (us ++ vs)) (TRec us).

    Hypothesis HRecDepth : forall (us vs : fields type),
        relfs subtype us vs -> relfs P us vs ->
        P (TRec us) (TRec vs).

    Hypothesis HRecPerm : forall (us vs : fields type),
        perm us vs -> P (TRec us) (TRec vs).
    
    Fixpoint IHSubtype (t t' : type) {struct t'} : subtype t t' -> P t t'.
    Proof.
        intros HC. destruct HC.
        - apply HRefl.
        - apply HTrans with (u := u); 
            try apply IHSubtype; try assumption.
        - apply HTop.
        - apply HFun; try apply IHSubtype;
            try assumption.
        - apply HRecWidth.
        - apply HRecDepth; try assumption.
            induction H; constructor.
            + destruct H as [HXY ASS]. split.
                * assumption.
                * apply IHSubtype. assumption.
            + assumption.
        - apply HRecPerm. assumption.
    (* No more subgoals. *)
    Admitted.
End SubtypeInduction.


Lemma st_fields_refl :
    forall (fs : fields type), relfs subtype fs fs.
Proof. induction fs; constructor.
    - split; constructor.
    - assumption.
Qed.

Lemma st_fields_rec :
    forall (us vs : fields type),
    relfs subtype us vs -> subtype (TRec us) (TRec vs).
Proof.
    intros us vs HS. constructor. assumption.
Qed.

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

(* Static Semantics with Subsumption *)
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
        relfs (check g) es ts ->
        check g (ERec es) (TRec ts)
    | check_prj : forall (e : expr) (x : id) (t : type) (ts : fields type),
        In (x,t) ts ->
        check g e (TRec ts) ->
        check g (EPrj e x) t.

(* Insufficient for records. *)
Check check_ind.

Section CheckInduction.
    Variable P : gamma -> expr -> type -> Prop.

    Hypothesis HSubsume : 
        forall (g : gamma) (e : expr) (u v : type),
        subtype u v -> check g e u -> P g e u -> P g e v.

    Hypothesis HUnit : 
        forall (g : gamma), P g EUnit TUnit.

    Hypothesis HVar :
        forall (g : gamma) (x : id) (t : type),
        g x = Some t -> 
        P g (EVar x) t.

    Hypothesis HFun :
        forall (g : gamma) (x : id) (u v : type) (e : expr),
        check (bind x u g) e v ->
        P (bind x u g) e v ->
        P g (EFun x u e) (TFun u v).

    Hypothesis HApp :
        forall (g : gamma) (e1 e2 : expr) (u v : type),
        check g e1 (TFun u v) ->
        P g e1 (TFun u v) ->
        check g e2 u ->
        P g e2 u ->
        P g (EApp e1 e2) v.

    Hypothesis HRec :
        forall (g : gamma) (es : fields expr) (ts : fields type),
        relfs (check g) es ts ->
        relfs (P g) es ts ->
        P g (ERec es) (TRec ts).

    Hypothesis HPrj :
        forall (g : gamma) (e : expr) (x : id) (t : type) (ts : fields type),
        In (x,t) ts ->
        check g e (TRec ts) ->
        P g e (TRec ts) ->
        P g (EPrj e x) t.

    Fixpoint IHCheck (g : gamma) (e : expr) (t : type) {struct e} : check g e t -> P g e t.
    Proof.
        intros HC. destruct HC.
        - apply HSubsume with (u := u); auto.
        - apply HUnit.
        - apply HVar. assumption.
        - apply HFun; auto.
        - apply HApp with (u := u); auto.
        - apply HRec; auto. induction H.
            + constructor.
            + constructor; auto. 
                inv H. split; auto.
        - apply HPrj with (ts := ts); auto.
    (* No more subgoals. *)
    Admitted.
    
End CheckInduction.

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

(* Values *)
Inductive value : expr -> Prop :=
    | value_unit : value EUnit
    | value_fun : forall (x : id) (t : type) (e : expr),
        value (EFun x t e)
    | value_rec : forall (vs : fields expr),
        predfs value vs ->
        value (ERec vs).

Section ValueDec.
    Fixpoint value_dec (v : expr) : {value v} + {~ value v}. 
    Proof.
        destruct v.
        - left. constructor.
        - right. intros HF. inv HF.
        - left. constructor.
        - right. intros HF. inv HF.
        - induction fs.
            + left. constructor. constructor.
            + destruct (value_dec (snd a)) as [AV | AV].
                { destruct IHfs as [V | V].
                    - pose proof 
                        (fun x : field expr => value_dec (snd x)) as PFV.
                        pose proof @Forall_dec
                            (field expr) (predf value) 
                            PFV fs as FD.
                        destruct FD as [FV | FV].
                        + left. constructor. 
                            constructor; assumption.
                        + right. intros HF. apply FV.
                            inv HF. inv H0. assumption.
                    - right. intros HF. apply V. 
                        inv HF. inv H0. constructor.
                        assumption. }
                { right. intros HF. apply AV. inv HF.
                    inv H0. assumption. }
        - right. intros HF. inv HF.
    Qed.
End ValueDec.

Module IdDec <: SE.DecidableType.
    Import SE.
    Require Import RelationClasses.
    Definition t := id.
    Definition eq (x1 x2 : t) := x1 = x2.
    Declare Instance eq_equiv : Equivalence eq.
    Theorem eq_dec : forall (x1 x2 : t),
        {x1 = x2} + {x1 <> x2}.
    Proof. intros. apply string_dec. Qed.
    Theorem eq_refl : forall (x : t), x = x.
    Proof. intros. reflexivity. Qed.
    Theorem eq_sym : forall (x y : t), x = y -> y = x.
    Proof. unfold eq. intros; subst; reflexivity. Qed.
    Theorem eq_trans : forall (x y z : t), x = y -> y = z -> x = z.
    Proof. intros; subst. reflexivity. Qed.
End IdDec.

(* variable sets *)
Module IS := WS.Make(IdDec).
Module ISF := MSF.WFactsOn(IdDec)(IS).

(* free variables *)
Fixpoint fv (e : expr) : IS.t :=
    match e with
    | EUnit => IS.empty
    | EVar x => IS.singleton x
    | EFun x _ e => IS.remove x (fv e)
    | EApp e1 e2 => IS.union (fv e1) (fv e2)
    | ERec (es) => 
        fold_right 
            (fun (e : field expr) acc => 
                IS.union acc (fv (snd e)))
            IS.empty es
    | EPrj e _ => fv e
    end.

(* Capture-avoiding Substitution *)
Inductive sub (x : id) (es : expr) : expr -> expr -> Prop :=
    | sub_unit : sub x es EUnit EUnit
    | sub_hit : sub x es (EVar x) es
    | sub_miss : forall (y : id), 
        x <> y -> 
        sub x es (EVar y) (EVar y)
    | sub_fun_bound : forall (t : type) (e : expr),
        sub x es (EFun x t e) (EFun x t e)
    | sub_fun_notfree : forall (y : string) (t : type) (e e' : expr),
        x <> y ->
        ~ IS.In y (fv es) -> 
        sub x es e e' -> 
        sub x es (EFun y t e) (EFun y t e')
    | sub_fun_free : forall (y z : id) (t : type) (e e' e'' : expr),
        x <> y -> 
        x <> z -> 
        y <> z ->
        IS.In y (fv es) -> 
        ~ IS.In z (fv es) ->
        ~ IS.In z (fv e) ->
        sub y (EVar z) e e' -> 
        sub x es e' e'' -> 
        sub x es (EFun y t e) (EFun z t e'')
    | sub_app : forall (e1 e1' e2 e2' : expr),
        sub x es e1 e1' -> 
        sub x es e2 e2' -> 
        sub x es (EApp e1 e2) (EApp e1' e2')
    | sub_rec : forall (fs fs' : fields expr),
        relfs (sub x es) fs fs' ->
        sub x es (ERec fs) (ERec fs')
    | sub_prj : forall (e e' : expr) (y : id),
        sub x es e e' ->
        sub x es (EPrj e y) (EPrj e' y).

Check sub_ind.

Section SubstitutionInduction.
    Variable P : id -> expr -> expr -> expr -> Prop.

    Hypothesis HUnit : 
        forall (x : id) (es : expr), 
        P x es EUnit EUnit.

    Hypothesis HHit : 
        forall (x : id) (es : expr),
        P x es (EVar x) es.

    Hypothesis HMiss : 
        forall (x : id) (es : expr) (y : id),
        x <> y -> P x es (EVar y) (EVar y).

    Hypothesis HFunBound : 
        forall (x : id) (es : expr) (t : type) (e : expr),
        P x es (EFun x t e) (EFun x t e).

    Hypothesis HFunNotFree : 
        forall (x : id) (es : expr) (y : string) (t : type) (e e' : expr),
        x <> y -> ~ IS.In y (fv es) ->
        sub x es e e' -> P x es e e' -> 
        P x es (EFun y t e) (EFun y t e').

    Hypothesis HFunFree :
        forall (x : id) (es : expr) (y z : id)
        (t : type) (e e' e'' : expr),
        x <> y -> x <> z ->
        y <> z -> IS.In y (fv es) ->
        ~ IS.In z (fv es) -> ~ IS.In z (fv e) ->
        sub y (EVar z) e e' -> P y (EVar z) e e' ->
        sub x es e' e'' -> P x es e' e'' -> 
        P x es (EFun y t e) (EFun z t e'').

    Hypothesis HApp :
        forall (x : id) (es e1 e1' e2 e2' : expr),
        sub x es e1 e1' -> P x es e1 e1' ->
        sub x es e2 e2' -> P x es e2 e2' -> 
        P x es (EApp e1 e2) (EApp e1' e2').

    Hypothesis HRec : 
        forall (x : id) (es : expr) (fs fs' : fields expr),
        relfs (sub x es) fs fs' -> 
        relfs (P x es) fs fs' ->
        P x es (ERec fs) (ERec fs').

    Hypothesis HPrj :
        forall (x : id) (es e e' : expr) (y : id),
        sub x es e e' -> P x es e e' -> 
        P x es (EPrj e y) (EPrj e' y).

    Fixpoint IHSubstitute (x : id) (es e e' : expr)
    {struct e} : sub x es e e' -> P x es e e'.
    Proof.
        intros HSub. destruct HSub.
        - apply HUnit.
        - apply HHit.
        - apply HMiss. assumption.
        - apply HFunBound.
        - apply HFunNotFree; auto.
        - apply HFunFree with (e' := e'); auto.
        - apply HApp; auto.
        - apply HRec; auto. 
            induction H; constructor.
            + destruct H as [Hfst Hall]. 
                split; auto.
            + assumption.
        - apply HPrj; auto.
        (* No more subgoals *)
    Admitted.
End SubstitutionInduction.


Axiom sub_exists : forall (x : id) (s e : expr), exists e', sub x s e e'.

(* Dynamic Semantics *)
Inductive step : expr -> expr -> Prop :=
    | step_redux : forall (x : id) (t : type) (e es e' : expr),
        sub x es e e' ->
        step (EApp (EFun x t e) es) e'
    | step_app : forall (e1 e2 e1' : expr),
        step e1 e1' ->
        step (EApp e1 e2) (EApp e1' e2)
    | step_prj_rec : forall (es : fields expr) (x : id) (e : expr),
        In (x,e) es ->
        step (EPrj (ERec es) x) e
    | step_prj : forall (e e' : expr) (x : id),
        step e e' ->
        step (EPrj e x) (EPrj e' x)
    | step_rec : forall (vs es : fields expr) (x : id) (e e' : expr),
        predfs value vs ->
        step e e' ->
        step (ERec (vs ++ (x,e) :: es)) (ERec (vs ++ (x,e') :: es)).

(* Inversion on Subsumption. *)
Section InvSubsumption.
    Lemma inv_top :
        forall (t : type),
        subtype TTop t -> t = TTop.
    Proof.
        intros t HS. dependent induction HS; auto.
    Qed.
            
    Lemma inv_unit :
        forall (t : type),
        subtype t TUnit -> t = TUnit.
    Proof.
        intros t HS. dependent induction HS; auto.
    Qed.

    Lemma inv_fun :
        forall (t a b : type),
        subtype t (TFun a b) ->
        exists (a' b' : type),
        t = TFun a' b' /\ subtype a a' /\ subtype b' b.
    Proof.
        intros t a b HS.
        dependent induction HS.
        - exists a. exists b. split.
            + reflexivity.
            + split; constructor.
        - specialize IHHS2 with 
            (a0 := a) (b0 := b).
            assert (HR : TFun a b = TFun a b);
            try reflexivity.
            apply IHHS2 in HR as [a' [b' [HU [HSA HSB]]]].
            apply IHHS1 in HU as [a'' [b'' [HT [HSA' HSB']]]].
            exists a''. exists b''. split.
            + assumption.
            + split.
                * apply st_trans with
                    (t := a) (u := a') (v := a'');
                    assumption.
                * apply st_trans with
                    (t := b'') (u := b') (v := b);
                assumption.
        - exists u. exists v. split.
            + reflexivity.
            + split; assumption.
    Qed.

    Lemma inv_rec :
        forall (t : type) (ts : fields type),
        subtype t (TRec ts) ->
        exists (us : fields type),
        t = TRec us /\ subtype (TRec us) (TRec ts).
    Proof.
        intros t ts HS. dependent induction HS.
        - exists ts. split; auto.
            apply st_refl.
        - specialize IHHS2 with (ts0 := ts).
            assert (HRts : TRec ts = TRec ts);
            try reflexivity.
            apply IHHS2 in HRts as IH2.
            destruct IH2 as [us [HU HSusts]].
            specialize IHHS1 with (ts := us).
            apply IHHS1 in HU as IH1.
            destruct IH1 as [vs [HT HSvsus]].
            exists vs. split; auto.
            apply st_trans with 
                (t := (TRec vs)) (u := TRec us) (v := TRec ts);
            assumption.
        - exists (ts ++ vs). split; constructor.
        - exists us. split; constructor. assumption.
        - exists us. split; auto.
            apply st_rec_perm. assumption.
    Qed.
End InvSubsumption.

Section CanonicalForms.
    Definition canon_unit (v : expr) : Prop :=
        value v -> checks v TUnit -> v = EUnit.

    Definition canon_fun (v : expr) : Prop :=
        forall (a b : type),
        value v -> checks v (TFun a b) -> 
        exists (x : id) (t : type) (e : expr), 
        subtype a t /\ v = EFun x t e.

    Definition canon_rec (v : expr) := 
        forall (ts : fields type),
        value v -> checks v (TRec ts) ->
        exists (es : fields expr) (us : fields type), 
        v = ERec es /\
        relfs (check empty) es us /\ 
        subtype (TRec us) (TRec ts).

    Lemma canonical_forms_unit : 
        forall (v : expr), canon_unit v.
    Proof.
        unfold canon_unit. intros v HV HChk;
        dependent induction HChk.
        - apply inv_unit in H as HU. auto.
        - reflexivity.
        - inversion HV.
        - inversion HV.
        - inversion HV.
    Qed.

    Lemma canonical_forms_fun :
        forall (v : expr), canon_fun v.
    Proof.
        unfold canon_fun. intros v t t' HV HChk.
        dependent induction HChk.
        - apply inv_fun in H as HU.
            destruct HU as [a' [b' [HF [HSA HSB]]]].
            specialize IHHChk with
                (t := a') (t' := b').
            pose proof (IHHChk HV HF) as IH.
            destruct IH as [x [w [e' [HSW HFW]]]].
            exists x. exists w. exists e'. split.
            + apply st_trans with
                (t := t) (u := a') (v := w);
                assumption.
            + assumption.
        - inversion HV.
        - exists x. exists t. exists e. 
            split; constructor.
        - inversion HV.
        - inversion HV.
    Qed.

    Lemma canonical_forms_rec :
        forall (v : expr), canon_rec v.
    Proof.
        unfold canon_rec. intros v ts HV HChk.
        dependent induction HChk.
        - apply inv_rec in H as [us [HU HSusts]].
            specialize IHHChk with (ts := us).
            apply IHHChk in HV as IH; auto.
            destruct IH as [es [vs [Hrec [HR HSvsus]]]].
            exists es. exists vs. split; auto. split; auto.
            apply st_trans with
                (t := (TRec vs)) (u := (TRec us)) (v := (TRec ts));
            assumption.
        - inv HV.
        - inv HV.
        - exists es. exists ts. 
            split; try reflexivity.
            induction HV; subst; constructor;
            try assumption;
            try apply st_refl.
        - inv HV. 
    Qed.
End CanonicalForms.

Section Progress.
    Lemma st_fields_name :
        forall (us ws : fields type),
        subtype (TRec us) (TRec ws) ->
        forall (x : id) (w : type),
        In (x,w) ws ->
        exists (u : type),
        In (x,u) us /\ subtype u w.
    Proof.
        intros us ws HS.
        dependent induction HS using IHSubtype; intros x w Hinws.
        - subst. exists w. 
            split; auto. constructor.
        - assert (HSusws : subtype (TRec us) (TRec ws)).
            + apply st_trans with (u := u); assumption.
            + pose proof inv_rec u ws HS2 as [vs [Huvs HSvws]]. subst.
                assert (Hduhu : TRec us = TRec us);
                assert (Hduhv : TRec vs = TRec vs);
                assert (Hduhw : TRec ws = TRec ws);
                try reflexivity.
                pose proof IHHS2 vs ws Hduhv Hduhw x w as IH2.
                apply IH2 in Hinws as [w' [Hinvs HSw'w]].
                pose proof IHHS1 us vs Hduhu Hduhv x w' as IH1.
                apply IH1 in Hinvs as [u' [Hinus Hsubu'w']].
                exists u'. split; try assumption.
                apply st_trans with (u := w');
                assumption.
        - exists w. split.
            + apply in_or_app.
                left. auto.
            + constructor.
        - induction H0; inv Hinws.
            + inv H. inv H5. destruct x0 as [x0 u0].
                exists u0. split.
                * constructor. simpl in H2.
                    rewrite <- H2. reflexivity.
                * assumption.
            + inv H. pose proof IHForall2 H8 H2 as HEX.
                destruct HEX as [u [Hinl HSuw]].
                exists u. split; try assumption.
                apply in_cons. assumption.
        - exists w. apply Permutation_sym in H. split.
            + apply Permutation_in with (l := ws);
                assumption.
            + constructor.
    Qed.

    Lemma rec_fields_name :
        forall (es : fields expr) (ts : fields type),
        relfs checks es ts ->
        forall (x : id) (t : type),
        In (x,t) ts ->
        exists (e : expr), In (x,e) es.
    Proof.
        intros es ts HR. induction HR;
        intros z t Hints.
        - inv Hints.
        - destruct x as (x,e). inv Hints.
            + exists e. constructor.
                unfold relf in H.
                destruct H as [HF _].
                simpl in *. subst.
                reflexivity.
            + apply IHHR in H0 as [e' Hinl].
                exists e'. apply in_cons.
                assumption.
    Qed.

    Definition progress_thm (e : expr) (t : type) : Prop :=
        checks e t -> value e \/ exists (e' : expr), step e e'.

    Lemma var_empty_checks :
        forall (x : id) (t : type),
        ~ checks (EVar x) t.
    Proof.
        intros x t H. unfold checks in *.
        remember empty as o in H. 
        remember (EVar x) as z in H.
        dependent induction H; 
        auto; try inv Heqz.
        discriminate.
    Qed.

    Lemma val_rec_exists :
        forall (es : fields expr),
        ~ value (ERec es) <-> Exists (predf (fun e => ~ value e)) es.
    Proof.
        intros es. split; intros H.
        - induction es.
            + exfalso. apply H.
                constructor. constructor.
            + apply Exists_cons. 
                destruct (value_dec (snd a)).
                * right. apply IHes. intros V.
                    inv V. apply H. constructor.
                    constructor; assumption.
                * left. unfold predf. assumption.
        - intros V. apply Exists_Forall_neg in H.
            + apply H. inv V. assumption.
            + pose proof 
                (fun x : field expr => 
                    value_dec (snd x)) as PFV.
                intros e. specialize PFV with e.
                destruct PFV as [VE | VE]; auto.
    Qed.

    Lemma val_rec_prefix :
        forall (es : fields expr),
        ~ value (ERec es) ->
        exists (x : id) (e : expr) 
            (qs rs : fields expr),
        ~ value e /\ 
        predfs value qs /\
        es = qs ++ (x,e) :: rs.
    Proof.
        induction es; intros HV.
        - exfalso. apply HV.
            constructor. constructor.
        - destruct (value_dec (snd a)).
            { assert (HVes : ~ value (ERec es)).
                - intros HR. apply HV. inv HR.
                    constructor.
                    constructor; assumption.
                - pose proof IHes HVes as IH.
                    destruct IH as [x [e [qs [rs [HNV [HPV Hqer]]]]]].
                    exists x. exists e. exists (a :: qs). 
                    exists rs. split; try assumption. split.
                    + constructor; assumption.
                    + rewrite <- app_comm_cons.
                        rewrite Hqer. reflexivity. }
            { exists (fst a). exists (snd a).
                exists []. exists es. split;
                try assumption. split.
                - constructor.
                - rewrite app_nil_l. destruct a as (x,e).
                    reflexivity. }
    Qed.

    Theorem Progress :
        forall (e : expr) (t : type), progress_thm e t.
    Proof.
        unfold progress_thm. intros e t HC.
        unfold checks in *. remember empty as o in HC.
        dependent induction HC using IHCheck; subst;
        assert (HE : empty = empty);
        try reflexivity.
        - destruct IHHC as [V | [e' HS]].
            + reflexivity.
            + left. assumption.
            + right. exists e'. assumption.
        - left. constructor.
        - discriminate.
        - left. constructor.
        - right. pose proof IHHC1 HE as [V | [e1' HS]].
            + pose proof canonical_forms_fun e1 u v V HC1
                as [x [t [e [HS HF]]]].
                pose proof sub_exists x e2 e as [e' HSub].
                exists e'. subst. constructor. assumption.
            + exists (EApp e1' e2). constructor. assumption.
        - induction H0.
            + left. constructor. constructor.
            + inv H. pose proof IHForall2 H7 as IH2.
                destruct H0 as [HFXY YES].
                pose proof YES HE as [HVX | [e' HSX]].
                { destruct (value_dec (ERec l)) as [V | V].
                    - left. constructor. inv V.
                        constructor; auto.
                    - destruct IH2 as [IH2 | IH2]; try contradiction. 
                        pose proof val_rec_prefix l V as HEX.
                        destruct HEX as [z [e [qs [rs [HVE [HPV HL]]]]]].
                        right. subst. destruct IH2 as [e' HS]. inv HS.
                        exists (ERec (x :: vs ++ (x0,e'0) :: es)).
                        rewrite app_comm_cons. rewrite app_comm_cons.
                        constructor; auto.
                        constructor; auto. }
                { right. destruct x as [x e]. simpl in *.
                    exists (ERec ((x, e') :: l)).
                    assert (HPV : predfs value []);
                    try (constructor; constructor).
                    pose proof step_rec [] l x e e' HPV HSX as HR.
                    rewrite app_nil_l in HR. rewrite app_nil_l in HR.
                    assumption. }
        - right. pose proof IHHC HE as [V | [e' HS]].
            + pose proof canonical_forms_rec e ts V HC as HCF.
                destruct HCF as [es [us [HRec [HR Hsub]]]]; subst.
                pose proof st_fields_name us ts Hsub x t H as [u [Hinus HSut]].
                pose proof rec_fields_name es us HR x u Hinus as [e' Hines].
                exists e'. constructor. assumption.
            + exists (EPrj e' x). constructor. assumption.
    Qed.
End Progress.

(* Inversion on the Typing Relation. *)
Section InvCheck.
    Lemma inv_chk_fun :
        forall (g : gamma) (t u v : type) (x : id) (e : expr),
        check g (EFun x t e) (TFun u v) ->
        subtype u t /\ check (bind x t g) e v.
    Proof.
        intros g t u v x e HC. 
        dependent induction HC using IHCheck.
        - pose proof inv_fun u0 u v H as [a [b [Huab [Hua Hbv]]]].
            subst. assert (HEFun : EFun x t e = EFun x t e);
            assert (HTFun : TFun a b = TFun a b); try reflexivity.
            pose proof IHHC t a b x e HEFun HTFun as IH.
            destruct IH as [HS HCB]. split.
            + apply st_trans with (u := a); assumption.
            + apply check_subsume with (u := b); assumption.
        - split; try apply st_refl. assumption.
    Qed.

    Lemma inv_chk_rec :
        forall (g : gamma) (es : fields expr) (ts : fields type),
        check g (ERec es) (TRec ts) ->
        forall (x : id) (t : type),
        In (x,t) ts ->
        exists (e : expr), 
        In (x,e) es /\ check g e t.
    Proof.
        intros g es ts HC x t Hints.
        dependent induction HC using IHCheck.
        - pose proof inv_rec u ts H as HRu.
            destruct HRu as [us [Huus HSus]].
            assert (HERec : ERec es = ERec es);
            try reflexivity.
            pose proof st_fields_name us ts HSus x t Hints as HT.
            destruct HT as [w [Hinus HSut]].
            pose proof IHHC es us HERec Huus x w Hinus as IH.
            destruct IH as [e [Hines HCew]]. exists e. split.
            + assumption.
            + apply check_subsume with (u := w);
                assumption.
        - induction H; inv Hints.
            + destruct x0 as [x0 e0]. exists e0.
                destruct H as [Hfst Hck].
                simpl in *; subst. split.
                * left. reflexivity.
                * assumption.
            + inv H0. destruct IHForall2; try assumption.
                destruct H3 as [Hinl Hchk].
                exists x1. split; try assumption.
                apply in_cons. assumption.
    Qed.
End InvCheck.

Ltac injintrosubst H := injection H; intros; subst.

Section SubstitutionLemma.
    Lemma bind_unfree_var :
        forall (e : expr) (x : id) (u v : type) (g : gamma),
        ~ IS.In x (fv e) ->
        check g e u <-> check (bind x v g) e u.
    Proof.
        intros e x u v g HN. split; intros HC;
        dependent induction HC using IHCheck.
        - pose proof IHHC HN as IH.
            apply check_subsume with (u := u);
            assumption.
        - constructor.
        - constructor. simpl in *.
            assert (Hxx0 : x <> x0).
            + intros Hxx0. apply HN. subst.
                constructor. reflexivity.
            + apply bind_complete; assumption.
        - constructor. destruct (IdDec.eq_dec x x0) as [HX | HX]; subst.
            + rewrite <- rebind_correct. assumption.
            + simpl in *. assert (HNin : ~ IS.In x (fv e)).
                * intros HNin. apply HN.
                    apply not_eq_sym in HX.
                    apply ISF.remove_2; assumption.
                * pose proof bind_diff_comm x x0 v u g HX as BDC.
                    rewrite <- BDC. pose proof IHHC HNin as IH.
                    assumption.
        - simpl in *. apply check_app with (u := u).
            + apply IHHC1. intros H1. apply HN.
                apply ISF.union_2. assumption.
            + apply IHHC2. intros H2. apply HN.
                apply ISF.union_3. assumption.
        - constructor. induction H0;
            constructor; inv H; inv H0.
            + split; try assumption. apply H3.
                intros Hxx0. apply HN. simpl.
                apply ISF.union_3. assumption.
            + assert (Hxl : ~ IS.In x (fv (ERec l))).
                * intros Hxl. apply HN. simpl in *.
                    apply ISF.union_2. assumption.
                * apply (IHForall2 Hxl H7).
        - simpl in *. apply check_prj with (ts := ts);
            try assumption. auto.
        - pose proof IHHC x v g HN as IH.
            apply check_subsume with (u := u); auto.
        - constructor.
        - simpl in *. constructor.
            assert (Hxx0 : x <> x0).
            + intros Hxx0. apply HN. subst.
                constructor. reflexivity.
            + apply bind_complete in H; assumption.
        - constructor. destruct (IdDec.eq_dec x x0) as [HX | HX]; subst.
            + rewrite <- rebind_correct in HC. assumption.
            + simpl in *. assert (HNin : ~ IS.In x (fv e)).
                * intros HNin. apply HN.
                    apply not_eq_sym in HX.
                    apply ISF.remove_2; assumption.
                * pose proof bind_diff_comm x x0 v u g HX as BDC.
                    symmetry in BDC.
                    pose proof IHHC x v (bind x0 u g) HNin BDC as IH.
                    apply IH.
        - simpl in *. apply check_app with (u := u).
            + apply IHHC1 with (x0 := x) (v1 := v); 
                auto. intros H1. apply HN. 
                apply ISF.union_2. assumption.
            + apply IHHC2 with (x0 := x) (v0 := v); 
                auto. intros H2. apply HN. 
                apply ISF.union_3. assumption.
        - constructor. induction H0; 
            constructor; inv H; inv H0.
            + split; try assumption.
                apply H3 with (x1 := x) (v0 := v); auto.
                intros Hxx0. apply HN. simpl.
                apply ISF.union_3. assumption.
            + assert (Hxl : ~ IS.In x (fv (ERec l))).
                * intros Hxl. apply HN. simpl in *.
                    apply ISF.union_2. assumption.
                * apply (IHForall2 H7 Hxl).
        - apply check_prj with (ts := ts); auto.
            simpl in *. assert (HR : bind x v g = bind x v g);
            try reflexivity. pose proof IHHC x v g HN HR as IH.
            assumption.
    Qed.

    Definition substitution_lemma (x : id) (esub e e' : expr) :=
        sub x esub e e' ->
        forall (u v : type) (g : gamma),
        check (bind x u g) e v -> 
        check g esub u -> 
        check g e' v.

    Lemma Substitution_Lemma :
        forall (x : id) (esub e e' : expr),
        substitution_lemma x esub e e'.
    Proof.
        intros x esub e e' HS.
        dependent induction HS using IHSubstitute;
        intros u v g HCB;
        dependent induction HCB using IHCheck;
        intros HC;
        try (apply check_subsume with (u := u0); auto;
            apply IHHCB with (x0 := x) (u1 := u) (g0 := g); 
            try reflexivity; assumption).
        - constructor.
        - rewrite bind_correct in H. injintrosubst H. auto.
        - apply bind_complete in H0 as BC; auto.
            constructor. auto.
        - constructor. clear IHHCB. 
            rewrite <- rebind_correct in HCB.
            assumption.
        - pose proof IHHCB g u e t y 
            H0 x H HS IHHS as IH.
            apply check_subsume with (u := u0); auto.
        - clear IHHCB. constructor.
            rewrite <- (bind_diff_comm x y u t g H) in HCB.
            apply IHHS in HCB as IH; auto.
            apply bind_unfree_var; auto.
        - pose proof IHHCB g u H3 e H4 t y 
            H1 H2 HS1 IHHS1 x H H0 HS2 IHHS2 as IH.
            apply check_subsume with (u := u0); auto.
        - clear IHHCB. constructor.
            apply IHHS2 with (u := u).
            { apply IHHS1 with (u := t).
                - pose proof bind_diff_comm 
                    x z u t g H0 as BDC1.
                    rewrite BDC1.
                    pose proof bind_diff_comm
                        y z t t (bind x u g) H1 as BDC2.
                    rewrite BDC2. apply bind_unfree_var; auto.
                - apply bind_unfree_var.
                    + intros Hin. simpl in *.
                        apply IS.singleton_spec in Hin.
                        contradiction.
                    + constructor. apply bind_correct. }
            { apply bind_unfree_var; auto. }
        - pose proof IHHCB x e1 e2 HS1 HS2
            IHHS1 IHHS2 u g as IH.
            apply check_subsume with (u := u0); auto.
        - clear IHHCB1. clear IHHCB2.
            apply check_app with (u := u0).
            + apply IHHS1 with (u := u); auto.
            + apply IHHS2 with (u := u); auto.
        - pose proof IHHCB x fs H H0 u g as IH.
            apply check_subsume with (u := u0); auto. 
        - constructor. dependent induction H2.
            + admit.
            + inv H0. inv H1.
            assert (Hexpr : expr = expr);
            assert (Htype : type = type);
            try reflexivity.
            pose proof IHForall2 es l'0 l l' 
                H11 Hexpr Htype as IH;
            clear IHForall2.
            constructor.
            {
            destruct y as [y ty];
            destruct x0 as [x0 ex0];
            destruct y0 as [y0 ey0].
            simpl in *. subst.
            inv H6; inv H9; simpl in *;
            subst. split; auto.
            simpl. clear IH. clear H2. clear H.
            inv H3. clear H13.
            inv H7. simpl in *.
            apply H2 with (u := u); auto. }
            { apply IH; auto; clear IH.
                - admit.
                - inv H3. apply H13. }
        - pose proof IHHCB x e y HS  IHHS u g as IH.
            apply check_subsume with (u := u0); auto.
        - clear IHHCB. apply check_prj with (ts := ts); auto.
            apply IHHS in HCB as IH; auto.
    Admitted.
End SubstitutionLemma.