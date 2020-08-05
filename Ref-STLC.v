Require Import String.
Require Import Coq.Init.Nat.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.ListSet.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.FunctionalExtensionality.
Require Coq.Structures.Equalities.
Module SE := Coq.Structures.Equalities.
Require Coq.FSets.FMapWeakList.
Module FM := Coq.FSets.FMapWeakList.
Require Coq.FSets.FMapFacts.
Module FF := Coq.FSets.FMapFacts.
Require Import Coq.Arith.PeanoNat.
Require Coq.MSets.MSetWeakList.
Module WS := Coq.MSets.MSetWeakList.
Require Coq.MSets.MSetFacts.
Module MSF := Coq.MSets.MSetFacts.

Inductive type : Type :=
    | TUnit
    | TFun : type -> type -> type
    | TRef : type -> type.

Fixpoint type_eqb (a b : type) : bool :=
    match a, b with
    | TUnit, TUnit => true 
    | TFun a1 a2, TFun b1 b2 => type_eqb a1 b1 && type_eqb a2 b2
    | TRef a, TRef b => type_eqb a b
    | _, _ => false
    end.

Definition id := string.

Definition loc := nat.

Inductive expr : Type :=
    | EVar : id -> expr
    | EFun : id -> type -> expr -> expr
    | EApp : expr -> expr -> expr
    | EUnit
    | ERef : expr -> expr
    | EBang : expr -> expr
    | EAss : expr -> expr -> expr
    | ELoc : loc -> expr.

Inductive value : expr -> Prop :=
    | vfun : forall (x : id) (t : type) (e : expr),
        value (EFun x t e)
    | vunit : value EUnit
    | vloc : forall (l : loc), 
        value (ELoc l).

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

Module IM := FM.Make(IdDec).

Module IFF := FF.WFacts_fun(IdDec)(IM).

(* typing context *)
Definition gamma := IM.t type.

Module LocDec <: SE.DecidableType.
    Import SE.
    Require Import RelationClasses.
    Definition t := loc.
    Definition eq (l1 l2 : t) := l1 = l2.
    Declare Instance eq_equiv : Equivalence eq.
    Theorem eq_dec : forall (l1 l2 : t),
        {l1 = l2} + {l1 <> l2}.
    Proof. intros. apply Nat.eq_dec. Qed.
    Theorem eq_refl : forall (l : t), l = l.
    Proof. intros. reflexivity. Qed.
    Theorem eq_sym : forall (l1 l2 : t), l1 = l2 -> l2 = l1.
    Proof. unfold eq. intros; subst; reflexivity. Qed.
    Theorem eq_trans : forall (l1 l2 l3 : t), l1 = l2 -> l2 = l3 -> l1 = l3.
    Proof. intros; subst. reflexivity. Qed.
End LocDec.

Module LM := FM.Make(LocDec).

Module LF := FF.WFacts_fun(LocDec)(LM).

(* evaluation stores *)
Definition mu : Type := LM.t expr.

(* typing stores *)
Definition sigma : Type := LM.t type.

(* Static Semantics *)
Inductive check (g : gamma) (s : sigma) : expr -> type -> Prop :=
    | check_var : forall (x : id) (t : type), 
        IM.MapsTo x t g ->
        check g s (EVar x) t
    | check_fun : forall (x : id) (t t' : type) (e : expr),
        check (IM.add x t g) s e t' ->
        check g s (EFun x t e) (TFun t t')
    | check_app : forall (e1 e2 : expr) (t t' : type),
        check g s e1 (TFun t t') ->
        check g s e2 t ->
        check g s (EApp e1 e2) t'
    | check_unit : check g s EUnit TUnit
    | check_ref : forall (e : expr) (t : type),
        check g s e t ->
        check g s (ERef e) (TRef t)
    | check_bang : forall (e : expr) (t : type),
        check g s e (TRef t) ->
        check g s (EBang e) t
    | check_ass : forall (e1 e2 : expr) (t : type),
        check g s e1 (TRef t) ->
        check g s e2 t ->
        check g s (EAss e1 e2) TUnit
    | check_loc : forall (l : loc) (t : type),
        LM.MapsTo l t s ->
        check g s (ELoc l) (TRef t).

(* variable sets *)
Module IS := WS.Make(IdDec).

(* free variables of an expression *)
Fixpoint fv (e : expr) : IS.t :=
    match e with
    | EVar x => IS.singleton x
    | EFun x _ e => IS.remove x (fv e)
    | EApp e1 e2 => IS.union (fv e1) (fv e2)
    | EUnit => IS.empty
    | ERef e => fv e
    | EBang e => fv e
    | EAss e1 e2 => IS.union (fv e1) (fv e2)
    | ELoc _ => IS.empty
    end.

(* Capture-avoiding Substitution *)
Inductive sub (x : id) (es : expr) : expr -> expr -> Prop :=
    | sub_hit : sub x es (EVar x) es
    | misssub : forall (y : id), 
        x <> y -> 
        sub x es (EVar y) (EVar y)
    | sub_fun_bound : forall (t : type) (e : expr),
        sub x es (EFun x t e) (EFun x t e)
    | sub_lam_notfree : forall (y : string) (t : type) (e e' : expr),
        x <> y ->
         ~ IS.In y (fv es) -> 
        sub x es e e' -> 
        sub x es (EFun y t e) (EFun y t e')
    | sub_lam_free : forall (y z : id) (t : type) (e e' e'' : expr),
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
    | sub_unit : sub x es EUnit EUnit
    | sub_ref : forall (e e' : expr),
        sub x es e e' ->
        sub x es (ERef e) (ERef e')
    | sub_bang : forall (e e' : expr),
        sub x es e e' ->
        sub x es (EBang e) (EBang e')
    | sub_ass : forall (e1 e1' e2 e2' : expr),
        sub x es e1 e1' ->
        sub x es e2 e2' ->
        sub x es (EAss e1 e2) (EAss e1' e2')
    | sub_loc : forall (l : loc),
        sub x es (ELoc l) (ELoc l).

Axiom sub_exists : forall (x : string) (es e : expr), exists e', sub x es e e'.

(* Dynamic Semantics *)
Inductive step (m : mu) : expr -> expr -> mu -> Prop :=
    | step_redux : forall (x : id) (t : type) (e1 e2 e3 : expr),
        sub x e2 e1 e3 -> 
        step m (EApp (EFun x t e1) e2) e3 m
    | step_app : forall (e1 e1' e2 : expr) (m' : mu),
        step m e1 e1' m' -> 
        step m (EApp e1 e2) (EApp e1' e2) m'
    | step_ref : forall (l : loc) (e : expr),
        ~ LM.In l m ->
        step m (ERef e) (ELoc l) (LM.add l e m)
    | step_loc : forall (l : loc) (e : expr),
        LM.MapsTo l e m ->
        step m (EBang (ELoc l)) e m
    | step_bang : forall (e e' : expr) (m' : mu),
        step m e e' m' ->
        step m (EBang e) (EBang e') m'
    | step_ass1 : forall (l : loc) (e : expr),
        step m (EAss (ELoc l) e) EUnit (LM.add l e m)
    | step_ass2 : forall (e1 e1' e2 : expr) (m' : mu),
        step m e1 e1' m' ->
        step m (EAss e1 e2) (EAss e1' e2) m'.

Definition subset (s s' : sigma) :=
    forall (l : loc) (t : type), LM.MapsTo l t s -> LM.MapsTo l t s'.

Lemma subset_add :
    forall (l : loc) (t : type) (s : sigma),
    ~ LM.In l s ->
    subset s (LM.add l t s).
Proof.
    unfold subset. intros.
    destruct (LocDec.eq_dec l l0); subst.
    - apply LF.not_find_in_iff in H.
        apply LF.find_mapsto_iff in H0.
        rewrite H in H0. discriminate.
    - apply LM.add_2; assumption.
Qed.

Lemma sigma_monotonic :
    forall (g : gamma) (s s' : sigma) (e : expr) (t : type),
    check g s e t -> subset s s' -> check g s' e t.
Proof.
    intros. dependent induction H;
    try constructor; try assumption; auto.
    - eapply check_app; auto.
    - eapply check_ass; auto.
Qed.

Definition dom_eq {A B : Type} (fa : LM.t A) (fb : LM.t B) : Prop :=
    forall (l : loc), LM.In l fa <-> LM.In l fb.

Compute LF.elements_in_iff.

Definition find_default {A : Type} (default : A) (l : loc) (map : LM.t A) : A :=
    match LM.find l map with
    | None => default
    | Some found => found
    end.

Definition fdm : loc -> mu -> expr := find_default EUnit.

Definition fds : loc -> sigma -> type := find_default TUnit.

Definition well_typed_ctxts (m : mu) (s : sigma) (g : gamma) : Prop :=
    dom_eq m s /\ forall (l : loc), check g s (fdm l m) (fds l s).

Definition preservation 
    (e e' : expr) (m m' : mu) : Prop := 
    step m e e' m' ->
    forall (g : gamma) (s : sigma) (t : type),
    well_typed_ctxts m s g ->
    check g s e t ->
    exists (s' : sigma), subset s s' ->
    well_typed_ctxts m' s' g /\ check g s' e' t.

Definition substitution_lemma 
    (x : id) (e1 e1' e2 : expr) : Prop := 
    sub x e2 e1 e1' ->
    forall (g : gamma) (s : sigma) (a b : type),
    check (IM.add x a g) s e1 b -> 
    check g s e2 a ->
    check g s e1' b.

Axiom add_twice : 
    forall {T : Type} (x : id) (a b : T) (map : IM.t T),
    IM.add x a (IM.add x b map) = IM.add x a map.

(* Can probably be replaced with a lemma about type-checking *)
Axiom add_diff_comm :
    forall {T : Type} (x y : id) (a b : T) (map : IM.t T),
    x <> y ->
    IM.add x a (IM.add y b map) = IM.add y b (IM.add x a map). 

Lemma bind_unfree_var :
    forall (e : expr) (x : id) (t' t : type) (g : gamma) (s : sigma),
    ~ IS.In x (fv e) ->
    check g s e t <-> check (IM.add x t' g) s e t.
Proof.
Admitted.

Lemma substitution_lemma_holds : 
    forall (x : id) (e1 e1' e2 : expr),
    substitution_lemma x e1 e1' e2.
Proof.
    unfold substitution_lemma.
    intros x e1 e1' e2 HS.
    induction HS; intros.
    - inversion H; subst.
        apply IFF.add_mapsto_iff in H2 as [[_ AB] | [HMT _]]; 
        subst; auto. contradiction.
    - inversion H0; subst. constructor. eapply IM.add_3 in H.
        + apply H.
        + apply H3.
    - inversion H; subst. constructor. 
        rewrite add_twice in H5. assumption.
    - inversion H1; subst. constructor.
        specialize IHHS with (g := (IM.add y t g)) 
            (s := s) (a := a) (b := t'). apply IHHS.
            + pose proof (add_diff_comm x y a t g H) as ADC.
                rewrite ADC. assumption.
            + apply bind_unfree_var; assumption.
    - inversion H5; subst. constructor.
        specialize IHHS2 with (g := (IM.add z t g)) 
            (s := s) (a := a) (b := t'). apply IHHS2;
            pose proof (add_diff_comm x z a t g H0) as ADC.
                rewrite ADC. specialize IHHS1 with 
                (g := (IM.add z t (IM.add x a g)))
                (s := s) (a := t) (b := t').
                apply IHHS1.
                + pose proof (add_diff_comm y z t t
                    (IM.add x a g) H1) as ACDC.
                    rewrite ACDC. apply bind_unfree_var; 
                    assumption.
                + rewrite <- ADC. apply bind_unfree_var.
                    * intros NIN. inversion NIN; 
                        try contradiction. inversion H8. 
                    * constructor. apply IM.add_1. reflexivity.
                + apply bind_unfree_var; assumption. 
    - inversion H; subst. eapply check_app.
        + eapply IHHS1.
            * apply H3.
            * assumption.
        + eapply IHHS2.
            * apply H5.
            * assumption.
    - inversion H; subst. constructor.
    - inversion H; subst. 
        constructor. eapply IHHS.
        + apply H2.
        + assumption.
    - inversion H; subst.
        constructor. eapply IHHS.
        + apply H2.
        + assumption.
    - inversion H; subst.
        eapply check_ass.
        + eapply IHHS1.
            * apply H3.
            * assumption.
        + eapply IHHS2.
            * apply H5.
            * assumption.
    - inversion H; subst.
        constructor. assumption.
Qed.

Lemma mu_update :
    forall (m : mu) (s : sigma) (g : gamma),
    well_typed_ctxts m s g ->
    forall (e : expr) (l : loc) (t : type),
    check g s e t ->
    LM.MapsTo l t s ->
    well_typed_ctxts (LM.add l e m) s g.
Proof.
    intros. unfold well_typed_ctxts in *.
    destruct H as [DE H]. split.
    - unfold dom_eq in *. split; intros.
        + destruct (LocDec.eq_dec l l0); subst.
            * apply LF.find_mapsto_iff in H1.
                apply LF.in_find_iff.
                intros H'. rewrite H1 in H'.
                discriminate.
            * apply DE. eapply LF.add_neq_in_iff in n.
                apply n. apply H2.
        + apply LF.add_in_iff. right.
            apply DE. assumption.
    - intros. unfold fdm in *.
        unfold fds in *. unfold find_default in *.
        destruct (LocDec.eq_dec l l0); subst.
        + specialize H with (l := l0).
            assert (HF : LM.find l0 (LM.add l0 e m) = Some e).
            * apply LF.add_eq_o. reflexivity.
            * rewrite HF. apply LM.find_1 in H1.
                rewrite H1. assumption.
        + assert (HF : LM.find l0 (LM.add l e m) = LM.find l0 m).
            * apply LF.add_neq_o. assumption.
            * rewrite HF. apply H.
Qed.

Lemma sigma_add :
    forall (m : mu) (s : sigma) (g : gamma),
    well_typed_ctxts m s g ->
    forall (e : expr) (l : loc) (t : type),
    check g s e t ->
    ~ LM.In l m ->
    well_typed_ctxts (LM.add l e m) (LM.add l t s) g.
Proof.
    intros. unfold well_typed_ctxts in *.
    destruct H as [DE H]. split.
    - unfold dom_eq in *. split; intros;
        destruct (LocDec.eq_dec l l0); subst;
        try (apply LF.add_in_iff; left; reflexivity);
        try (eapply LF.add_neq_in_iff in n as NINS; apply NINS;
            eapply LF.add_neq_in_iff in n as NINM;
            apply -> NINM in H2; apply DE; assumption).
    - intros. unfold fdm in *. unfold fds in *. 
        unfold find_default in *.
        destruct (LocDec.eq_dec l l0); subst.
        + specialize H with (l := l0).
            assert (LL: l0 = l0); try reflexivity.
            rewrite (LF.add_eq_o s t LL).
            rewrite (LF.add_eq_o m e LL).
            eapply sigma_monotonic.
            * apply H0.
            * apply subset_add. intros NIn. apply H1.
                eapply DE. assumption.
        + pose proof (LF.add_neq_o s t n) as SANE. rewrite SANE. 
            pose proof (LF.add_neq_o m e n) as MANE.
            rewrite MANE.
            eapply sigma_monotonic.
            * apply H.
            * apply subset_add. intros NIn.
                apply H1. eapply DE. assumption.
Qed.

Theorem preservation_thm :
    forall (e e' : expr) (m m' : mu),
    preservation e e' m m'.
Proof.
    unfold preservation. intros e e' m m' H.
    induction H; intros.
    - exists s. intros; split;
        try assumption.
        inversion H1; subst.
        eapply substitution_lemma_holds.
        + apply H.
        + inversion H5; subst. apply H4.
        + assumption.
    - inversion H1; subst. 
        specialize IHstep with (g := g) (s := s) (t := (TFun t0 t)).
        pose proof (IHstep H0 H4) as [s' IH]. exists s'. intros SS. 
        apply IH in SS as IH'. destruct IH' as [WT CHK]. 
        split; try assumption. eapply check_app.
        + apply CHK.
        + eapply sigma_monotonic.
            * apply H6.
            * assumption.
    - inversion H1; subst. exists (LM.add l t0 s). intros SS; split.
        + apply sigma_add; try assumption.
        + constructor. apply LM.add_1. reflexivity.
    - inversion H1; subst. exists s. intros SS; 
        split; try assumption.
        inversion H3; subst. unfold well_typed_ctxts in H0.
        destruct H0 as [DE CHK]. specialize CHK with l.
        unfold fdm in CHK. unfold fds in CHK.
        unfold find_default in CHK.
        apply LM.find_1 in H5. rewrite H5 in CHK.
        apply LM.find_1 in H. rewrite H in CHK.
        assumption.
    - inversion H1; subst. 
        specialize IHstep with (g := g) (s := s) (t := TRef t).
        pose proof (IHstep H0 H3) as [s' IH].
        exists s'. intros SS. apply IH in SS as IH'.
        destruct IH' as [WTC CHK]. split;
        try assumption. constructor. assumption.
    - inversion H0; subst. exists s. 
        intros SS. split.
        + eapply mu_update; try assumption.
            * apply H5.
            * inversion H3; subst. assumption.
        + constructor.
    - inversion H1; subst.
        specialize IHstep with (g := g) (s := s) (t := TRef t0).
        pose proof (IHstep H0 H4) as [s' IH]. exists s'.
        intros SS. apply IH in SS as IH'. destruct IH' as [WTC CHK].
        split; try assumption. eapply check_ass.
        + apply CHK.
        + eapply sigma_monotonic.
            * apply H6.
            * assumption.
Qed.