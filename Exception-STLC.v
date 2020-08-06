(* STLC with exception handling *)

Require Import String.
Require Import Coq.Strings.String.
Require Coq.MSets.MSetWeakList.
Module WS := Coq.MSets.MSetWeakList.
Require Coq.MSets.MSetFacts.
Module MSF := Coq.MSets.MSetFacts.
Require Coq.Structures.Equalities.
Module SE := Coq.Structures.Equalities.
Require Import Coq.Logic.FunctionalExtensionality.

Definition id : Type := string.

Inductive type : Type :=
    | TUnit
    | TFun : type -> type -> type
    | TExn : type.

Inductive expr : Type :=
    | EUnit
    | EName (x : id)
    | EFun (x : id) (t : type) (e : expr)
    | EApp : expr -> expr -> expr
    | EExn
    | EThrow : expr -> expr
    | ETryWith (e : expr) (catch : expr).

(* Gamma *)
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

Inductive check (g : gamma) : expr -> type -> Prop :=
    | check_unit : check g EUnit TUnit
    | check_name : forall (x : id) (t : type),
        g x = Some t ->
        check g (EName x) t
    | check_fun : forall (x : id) (t t' : type) (e : expr),
        check (bind x t g) e t' ->
        check g (EFun x t e) (TFun t t')
    | check_app : forall (e1 e2 : expr) (t t' :type),
        check g e1 (TFun t t') ->
        check g e2 t ->
        check g (EApp e1 e2) t'
    | check_exn : check g EExn TExn
    | check_throw : forall (e : expr) (t : type),
        check g e TExn ->
        check g (EThrow e) t
    | check_trywith : forall (e catch : expr) (t : type),
        check g e t ->
        check g catch (TFun TExn t) ->
        check g (ETryWith e catch) t.

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
    | EName x => IS.singleton x
    | EFun x t e => IS.remove x (fv e)
    | EApp e1 e2 => IS.union (fv e1) (fv e2)
    | EExn => IS.empty
    | EThrow e => fv e
    | ETryWith e catch => IS.union (fv e) (fv catch)
    end.

(* Capture-avoiding Substitution *)
Inductive sub (x : id) (es : expr) : expr -> expr -> Prop :=
    | sub_unit : sub x es EUnit EUnit
    | sub_hit : sub x es (EName x) es
    | misssub : forall (y : id), 
        x <> y -> 
        sub x es (EName y) (EName y)
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
        sub y (EName z) e e' -> 
        sub x es e' e'' -> 
        sub x es (EFun y t e) (EFun z t e'')
    | sub_app : forall (e1 e1' e2 e2' : expr),
        sub x es e1 e1' -> 
        sub x es e2 e2' -> 
        sub x es (EApp e1 e2) (EApp e1' e2')
    | sub_exn : sub x es EExn EExn
    | sub_throw : forall (e e' : expr),
        sub x es e e' ->
        sub x es (EThrow e) (EThrow e')
    | sub_trywith : forall (e e' catch catch' : expr),
        sub x es e e' ->
        sub x es catch catch' ->
        sub x es (ETryWith e catch) (ETryWith e' catch').

Inductive value : expr -> Prop :=
    | value_unit : value EUnit
    | value_fun : forall (x : id) (t : type) (e : expr),
        value (EFun x t e)
    | value_exn : value EExn.

Inductive step : expr -> expr -> Prop :=
    | throw_left_intros : forall (e1 e2 : expr),
        step (EApp (EThrow e1) e2) (EThrow e1)
    | throw_right_intros : forall (v e : expr),
        value v ->
        step (EApp v (EThrow e)) (EThrow e)
    | step_redux : forall (x : id) (t : type) (e e' v : expr),
        value v ->
        sub x v e e' -> 
        step (EApp (EFun x t e) v) e'
    | step_app_left : forall (e1 e1' e2 : expr),
        step e1 e1' -> 
        step (EApp e1 e2) (EApp e1' e2)
    | step_app_right : forall (v e e' : expr),
        value v ->
        step e e' ->
        step (EApp v e) (EApp v e')
    | step_throw : forall (e e' : expr),
        step e e' ->
        step (EThrow e) (EThrow e')
    | step_throw_throw : forall (v : expr),
        value v ->
        step (EThrow (EThrow v)) (EThrow v)
    | step_try_succ : forall (v catch : expr),
        value v ->
        step (ETryWith v catch) v
    | step_try_catch : forall (v catch : expr),
        value v ->
        step (ETryWith (EThrow v) catch) (EApp catch v).

Lemma bind_unfree_var :
    forall (e : expr) (x : id) (t' t : type) (g : gamma),
    ~ IS.In x (fv e) ->
    check g e t <-> check (bind x t' g) e t.
Proof.
    induction e; split; intros; simpl in H; inversion H0; subst.
    - constructor.
    - constructor. 
    - apply check_name.
        apply bind_complete.
        + unfold not in *; intros; subst.
            apply H. left. reflexivity.
        + apply H2.
    - apply check_name. destruct (IdDec.eq_dec x x0); subst.
        + simpl in H. exfalso. apply H. left. reflexivity.
        + eapply bind_complete.
            * intros HE. apply n.
                symmetry. apply HE.
            * apply H2.
    - apply check_fun. destruct (IdDec.eq_dec x x0); subst.
        + rewrite <- rebind_correct. apply H5.
        + pose proof bind_diff_comm.
            eapply H1 in n as nxs.
            rewrite nxs. apply IHe.
            * unfold not in *. intros.
                apply H. apply ISF.remove_2; assumption.
            * apply H5.
    - apply check_fun. destruct (IdDec.eq_dec x x0); subst.
        + erewrite rebind_correct. apply H5.
        + eapply IHe.
            * unfold not in *. intros.
                apply H. apply ISF.remove_2; 
                try assumption. apply H1.
            * rewrite bind_diff_comm.
                apply H5. apply not_eq_sym. assumption.
    - eapply check_app.
        + apply IHe1.
            * unfold not in *; intros. apply H.
                apply ISF.union_2. assumption.
            * apply H3.
        + apply IHe2.
            * unfold not in *; intros. apply H.
                apply ISF.union_3. assumption.
            * apply H5.
    - eapply check_app.
        + eapply IHe1.
            * unfold not in *; intros. apply H.
                apply ISF.union_2. apply H1.
            * apply H3.
        + eapply IHe2.
            * unfold not in *; intros. apply H.
                apply ISF.union_3. apply H1.
            * apply H5.
    - constructor.
    - constructor.
    - constructor. apply IHe; assumption.
    - constructor. eapply IHe.
        + apply H.
        + apply H2.
    - constructor.
        + apply IHe1.
            * unfold not in *; intros. apply H.
                apply ISF.union_2. assumption.
            * apply H3.
        + apply IHe2.
            * unfold not in *; intros. apply H.
                apply ISF.union_3. assumption.
            * apply H5.
    - constructor.
        + eapply IHe1.
            * unfold not in *; intros. apply H.
                apply ISF.union_2. apply H1.
            * apply H3.
        + eapply IHe2.
            * unfold not in *; intros. apply H.
                apply ISF.union_3. apply H1.
            * apply H5.
Qed.