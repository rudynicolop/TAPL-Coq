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
    Lemma top_top :
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
        relfs (fun _ _ => True) es us /\ subtype (TRec us) (TRec ts).

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
            destruct IH as [es [vs [HR HSvsus]]].
            exists es. exists vs. split; auto.
            apply st_trans with
                (t := (TRec vs)) (u := (TRec us)) (v := (TRec ts));
            assumption.
        - inversion HV.
        - inversion HV.
        - exists es. exists ts. split.
            + induction H; subst; constructor.
                * destruct H as [Hid _]. split; auto.
                * apply IHForall2. constructor.
                    inversion HV; subst.
                    inversion H2; subst. assumption.
            + constructor.
        - inversion HV.
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
        (* intros us ws HS x w Hinw.
        remember (TRec us) as ur in HS.
        remember (TRec ws) as wr in HS.
        dependent induction HS; subst.
        - injection Heqwr; intros; 
            subst. exists w. split.
            + assumption.
            + constructor.
        - apply inv_rec in HS2 as [us' [HU' HSU']]; subst. 
            assert (HRus' : TRec us' = TRec us');
            assert (HRws : TRec ws = TRec ws);
            assert (HRus : TRec us = TRec us);
            try reflexivity.
            inv HS1; inv HSU'.
            + exists w. split.
                * assumption.
                * constructor.
            + pose proof IHHS2 HRus'  
                try reflexivity.
                
                try reflexivity.
                pose proof IHHS2 HRus' HRws x w Hinw as IH1.
                destruct IH1 as [u [Hinu HSU]].
        - admit.
        - admit.
        - admit.
        - admit.
        - admit. *)
    Admitted.

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

    Theorem Progress :
        forall (e : expr) (t : type), progress_thm e t.
    Proof.
        unfold progress_thm. intros e t HC.
        dependent induction e.
        - left. constructor.
        - apply var_empty_checks in HC. 
            contradiction.
        - left. constructor.
        - right. inv HC.
            + admit.
            + apply IHe1 in H1 as IH1.
                apply IHe2 in H3 as IH2.
                destruct IH1 as [V1 | [e1' HS1]].
                * pose proof canonical_forms_fun e1 u t V1 H1 
                    as [x [t' [e [HSe HF]]]]; subst.
                    pose proof sub_exists x e2 e as [e' HSub].
                    exists e'. constructor. assumption.
                * exists (EApp e1' e2). constructor. assumption.
        - admit.
        - right. inv HC.
            + admit.
            + apply IHe in H3 as IH. 
                destruct IH as [V | [e' HS]].
                * pose proof canonical_forms_rec e ts V H3
                    as [es [us [HR HS]]].
                    assert (HE : exists (e' : expr), In (x,e') es).
                    admit. admit.
                * exists (EPrj e' x). constructor. assumption.
    Admitted.
End Progress.