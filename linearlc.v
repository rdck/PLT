(* A formalization of a simply typed linear lambda calculus, and some basic properties. *)

Require Coq.Lists.List.
Local Open Scope list_scope.

(* bind for option monad *)
Definition bind {A} (x : option A) (f : A -> option A) :=
  match x with
  | None => None
  | Some y => f y
  end
.

(* do notation for option monad *)
Notation "pat <- e ;; f" := (bind e (fun pat => f))
  (at level 60, right associativity).
Notation "' pat <- e ;; f" := (bind e (fun x => match x with pat => f end))
  (at level 60, pat pattern, right associativity).

(* we use De Bruijn indices *)
Definition idx := nat.

Inductive type : Set :=
| ty_unit : type
| ty_arrow : type -> type -> type
.

Scheme Equality for type.

Inductive term : Set :=
| star : term
| var : idx -> term
| abs : type -> term -> term
| app : term -> term -> term
.

Scheme Equality for term.

Definition ltype : Set := nat * type.

Notation ctx := (list ltype).

Reserved Notation "Γ '⊢' e '∈' t '⊣' out" (at level 90).
Inductive has_type : ctx -> term -> type -> ctx -> Prop :=

(* variables use up types in the context *)
| linear_reflexivity : forall Γ1 Γ2 ix t n,
    length Γ1 = ix ->
    Γ1 ++ (S n, t)::Γ2 ⊢ var ix ∈ t ⊣ Γ1 ++ (n, t)::Γ2

(* star freely has type unit *)
| unit_introduction : forall Γ,
    Γ ⊢ star ∈ ty_unit ⊣ Γ

(* function abstraction *)
| arrow_introduction : forall (Γ1 Γ2 : ctx) (domain codomain : type) (e : term) (blank : ltype),
    (1, domain) :: Γ1 ⊢ e ∈ codomain ⊣ blank :: Γ2 ->
    Γ1 ⊢ abs domain e ∈ ty_arrow domain codomain ⊣ Γ2

(* function application *)
| arrow_elimination : forall (Γ1 Γ2 Δ : ctx) (e1 e2 : term) (domain codomain : type),
    Γ1 ⊢ e1 ∈ ty_arrow domain codomain ⊣ Δ ->
    Δ ⊢ e2 ∈ domain ⊣ Γ2 ->
    Γ1 ⊢ app e1 e2 ∈ codomain ⊣ Γ2

where "Γ '⊢' e '∈' t '⊣' out" := (has_type Γ e t out).

(* Output contexts are the same size as input contexts. *)
Theorem context_size_invariant :
  forall (Γ1 Γ2 : ctx) (e : term) (t : type),
  Γ1 ⊢ e ∈ t ⊣ Γ2 -> length Γ1 = length Γ2.
Proof.
  intros.
  induction H as [ | | Γ1 Γ2 dom cod e blank H IH | Γ1 Γ2 Δ e1 e2 dom cod H_arrow IH_arrow H_arg IH_arg ] .
  + rewrite -> List.app_length.
    rewrite -> List.app_length.
    reflexivity.
  + reflexivity.
  + simpl in IH.
    injection IH.
    intros equality.
    assumption.
  + rewrite IH_arrow.
    rewrite IH_arg.
    reflexivity.
Qed.

(* derived boolean equality preserves propositional equality *)
Lemma type_beq_faithful : forall t1 t2, type_beq t1 t2 = true <-> t1 = t2.
Proof.
  intros t1 t2.
  split.
  {
    revert t2.
    induction t1 as [ | dom IH_dom cod IH_cod ].
    + intros t2 H.
      destruct t2 as [ | dom cod ].
      - reflexivity.
      - discriminate H.
    + intros t2 H.
      destruct t2 as [ | dom' cod' ].
      - discriminate H.
      - simpl in H.
        rewrite Bool.andb_true_iff in H.
        destruct H as [Hdom Hcod].
        apply IH_dom in Hdom.
        apply IH_cod in Hcod.
        subst.
        reflexivity.
  } {
    intros.
    rewrite <- H.
    clear H t2.
    induction t1 as [ | dom IH_dom cod IH_cod ].
    + reflexivity.
    + simpl.
      rewrite IH_dom.
      rewrite IH_cod.
      reflexivity.
  }
Qed.

(* simple example *)
Goal nil ⊢ app (abs ty_unit (var 0)) star ∈ ty_unit ⊣ nil.
Proof.
  eapply arrow_elimination.
  + eapply arrow_introduction.
    apply (linear_reflexivity nil).
    reflexivity.
  + apply unit_introduction.
Qed.

(* bisect a context *)
Fixpoint split {A : Type} (Γ : list A) (n : nat) :=
  match (n, Γ) with
  | (O, _)          => (nil, Γ)
  | (S m, nil)      => (nil, nil)
  | (S m, x :: xs)  =>
      let (lft, rgt) := split xs m in
      (x :: lft, rgt)
  end
.

Lemma split_faithful {A : Type} : forall (Γ : list A) n,
  fst (split Γ n) ++ snd (split Γ n) = Γ
.
Proof.
  intros Γ.
  induction Γ.
  + intros n.
    destruct n.
    - reflexivity.
    - reflexivity.
  + intros n.
    destruct n.
    - reflexivity.
    - simpl.
      destruct (split Γ n) as [lft rgt] eqn:EQ.
      set (IH := (IHΓ n)).
      rewrite EQ in IH.
      simpl in IH.
      simpl.
      rewrite IH.
      reflexivity.
Qed.

Lemma split_left_length {A : Type} : forall (Γ : list A) n lft rgt x,
  split Γ n = (lft, x :: rgt) -> length lft = n
.
Proof.
  intros Γ.
  induction Γ.
  + intros n.
    destruct n.
    - intros.
      simpl in H.
      discriminate H.
    - intros.
      simpl in H.
      discriminate H.
  + intros n.
    destruct n.
    - intros.
      simpl in H.
      injection H.
      intros _ _ EQ.
      rewrite <- EQ.
      reflexivity.
    - specialize (IHΓ n).
      simpl.
      destruct (split Γ n) as [l r] eqn:EQ.
      intros LFT RGT x H.
      injection H.
      intros HRIGHT HLEFT.
      rewrite <- HLEFT.
      simpl.
      apply eq_S.
      specialize (IHΓ l RGT x).
      apply IHΓ.
      rewrite <- HRIGHT.
      reflexivity.
Qed.

(* type inference algorithm *)
Fixpoint synth (Γ : ctx) (e : term) :=
  match e with
  | star => Some (ty_unit, Γ)
  | var ix =>
      match split Γ ix with
      | (Γ1, (S n, t) :: Γ2) => Some (t, Γ1 ++ (n, t) :: Γ2)
      | _ => None
      end
  | abs domain e =>
      ' (codomain, Γ2) <- synth ((1, domain) :: Γ) e ;;
      match Γ2 with
      | _ :: Γ2' => Some (ty_arrow domain codomain, Γ2')
      | _ => None
      end
  | app e1 e2 =>
      ' (ft, Δ) <- synth Γ e1 ;;
      ' (t1', Γ2) <- synth Δ e2 ;;
      match ft with
      | ty_arrow t1 t2 => if type_beq t1 t1' then Some (t2, Γ2) else None
      | _ => None
      end
  end
.

(* simple example *)
Definition Γ00 := (3, ty_unit) :: (4, ty_unit) :: nil.
Compute synth Γ00 (var 1).

(* soundness of type inference *)
Theorem synth_sound : forall e Γ1 Γ2 t, synth Γ1 e = Some (t, Γ2) -> Γ1 ⊢ e ∈ t ⊣ Γ2.
Proof.
  intros e.
  induction e as [ | | | ].
  + intros Γ1 Γ2 t H.
    simpl in H.
    injection H. intros EQ_Γ EQ_t.
    subst.
    apply unit_introduction.
  + intros Γ1 Γ2 t H.
    simpl in H.
    destruct (split Γ1 i) as [l r] eqn:EQ.
    destruct r as [ | (count, t') r ].
    - discriminate H.
    - destruct count.
      * discriminate H.
      * rewrite <- (split_faithful Γ1 i).
        injection H.
        intros EQ_RIGHT EQ_T.
        rewrite <- EQ_RIGHT.
        rewrite EQ.
        simpl.
        rewrite EQ_T.
        apply linear_reflexivity.
        apply split_left_length in EQ.
        assumption.
  + intros Γ1 Γ2 arrow H.
    simpl in H.
    destruct (synth ((1, t) :: Γ1) e) as [ (cod, Δ) | ] eqn:EQ .
    - simpl in H.
      destruct Δ.
      * discriminate H.
      * injection H.
        intros EQ_Δ EQ_arrow.
        rewrite <- EQ_arrow.
        eapply arrow_introduction.
        specialize (IHe ((1, t) :: Γ1) (l :: Δ) cod).
        rewrite EQ_Δ in IHe.
        rewrite EQ_Δ in EQ.
        apply IHe.
        rewrite EQ.
        reflexivity.
    - simpl in H. discriminate H.
  + intros Γ1 Γ2 t H.
    simpl in H.
    destruct (synth Γ1 e1) as [ (arrow, Δ) | ] eqn:EQ1.
    - simpl in H.
      destruct (synth Δ e2) as [ (dom, Γ2') | ] eqn:EQ2.
      * simpl in H.
        destruct arrow as [ | DOM COD ].
        discriminate H.
        destruct (type_beq DOM dom) eqn:EQDOM.
        injection H.
        intros EQΓ EQT.
        eapply arrow_elimination.
        apply IHe1.
        rewrite EQT in EQ1.
        rewrite EQ1.
        reflexivity.
        apply IHe2.
        apply type_beq_faithful in EQDOM.
        rewrite EQDOM.
        rewrite EQ2.
        rewrite EQΓ.
        reflexivity.
        discriminate H.
      * simpl in H.
        discriminate H.
    - simpl in H.
      discriminate H.
Qed.

Lemma split_lemma : forall (Γ1 Γ2 : ctx) n x,
  length Γ1 = n ->
  split (Γ1 ++ x :: Γ2) n = (Γ1, x :: Γ2)
.
Proof.
  intros Γ1.
  induction Γ1.
  {
    intros.
    simpl in H.
    rewrite <- H.
    reflexivity.
  } {
    intros.
    simpl in H.
    simpl.
    destruct n.
    + discriminate H.
    + injection H.
      intros LENGTH.
      specialize (IHΓ1 Γ2 n x).
      apply IHΓ1 in LENGTH.
      rewrite LENGTH.
      reflexivity.
  }
Qed.

Corollary synth_var_length : forall (Γ1 Γ2 : ctx) ix count t,
  length Γ1 = ix ->
  synth (Γ1 ++ (S count, t) :: Γ2) (var ix) = Some (t, Γ1 ++ (count, t) :: Γ2)
.
Proof.
  intros.
  simpl.
  apply (split_lemma Γ1 Γ2 ix (S count, t)) in H.
  fold ltype in *.
  rewrite H.
  reflexivity.
Qed.

(* completeness of type inference *)
Theorem synth_complete :
  forall e Γ1 Γ2 t,
  Γ1 ⊢ e ∈ t ⊣ Γ2 ->
  synth Γ1 e = Some (t, Γ2)
.
Proof.
  intros e Γ1 Γ2 t H.
  induction H as [ | | Γ1 Γ2 dom cod e blank H IH | Γ1 Γ2 Δ e1 e2 dom cod H1 IH1 H2 IH2 ].
  + apply synth_var_length.
    assumption.
  + reflexivity.
  + simpl.
    rewrite IH.
    reflexivity.
  + simpl.
    rewrite IH1.
    simpl.
    rewrite IH2.
    simpl.
    rewrite ((proj2 (type_beq_faithful dom dom)) eq_refl).
    reflexivity.
Qed.

Fixpoint substitute (v : term) (ix : idx) (e : term) :=
  match e with
  | var ix'   => if Nat.eqb ix ix' then v else var ix'
  | star      => star
  | abs t e'  => abs t (substitute v (S ix) e')
  | app e1 e2 => app (substitute v ix e1) (substitute v ix e2)
  end
.

Fixpoint eval (e : term) :=
  match e with
  | app (abs _ e') x  => substitute (eval x) 0 (eval e')
  | _                 => e
  end
.

Compute eval (app (abs ty_unit (var 0)) star).
Compute eval (app (abs ty_unit (abs ty_unit (var 1))) star).
