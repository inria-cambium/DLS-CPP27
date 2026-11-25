Require Import FOL.DLS.Retracts.
From Stdlib Require Import List Fin PeanoNat Classes.Morphisms Lia.

Definition injective {X Y} (f: X -> Y) := forall x x', f x = f x' -> x = x'.
Class ii A B := ii_constr:> exists i: A -> B, injective i.
Notation "A ≤i B" := (ii A B) (at level 80).
Class eqi A B := { eqi_l: A ≤i B ; eqi_r: B ≤i A }.
Open Scope type_scope.

Section OrderInstances.

#[global] Instance ii_of_eqi_l {A B} {h: eqi A B}: A ≤i B.
Proof.
  now destruct h as [? _].
Qed.

#[global] Instance ii_of_eqi_r {A B} {h: eqi A B}: B ≤i A.
Proof.
  now destruct h as [_ ?].
Qed.

#[global] Instance ii_refl: Reflexive ii.
Proof.
  intros A. exists id. intros x x'. exact id.
Qed.

#[global] Instance ii_trans: Transitive ii.
Proof.
  intros A B C [iAB hAB] [iBC hBC]. exists (fun a => iBC (iAB a)). intros c c' e.
  apply hBC, hAB in e. assumption.
Qed.

#[global] Instance ii_refl' {A}: A ≤i A.
Proof. 
  reflexivity.
Qed.

#[global] Instance eqi_refl: Reflexive eqi.
Proof.
  intros A. split. all: exact _.
Qed.

#[global] Instance eqi_sym: Symmetric eqi.
Proof.
  intros A B [h1 h2]. split. all: exact _.
Qed.

#[global] Instance eqi_trans: Transitive eqi.
Proof.
  intros A B C [h11 h12] [h21 h22]. split. all: transitivity B; exact _.
Qed.

#[global] Instance eqi_compat_ii {A A' B B'}: eqi A B -> eqi A' B' -> A ≤i A' -> B ≤i B'.
Proof.
  intros [_ h] [h' _] H.
  transitivity A; [ | transitivity A']; exact _.
Qed.

#[global] Instance add_comm_ii {A B}: (A + B) ≤i (B + A).
Proof.
  exists (fun s => match s with | inl a => inr a | inr b => inl b end).
  intros [a|b] [a'|b'] e.
  all: try discriminate e; f_equal; injection e as e'; assumption.
Qed.

#[global] Instance add_comm_eqi {A B}: eqi (A + B) (B + A).
Proof.
  split. all: exact _.
Qed.

#[global] Instance add_assoc_ii {A B C}: (A + B + C) ≤i (A + (B + C)).
Proof.
  exists (fun s => match s with | inl (inl a) => inl a | inl (inr b) => inr (inl b) | inr c => inr (inr c) end).
  intros [[a|b]|c] [[a'|b']|c'] e.
  all: try discriminate e; repeat f_equal; injection e as e'; assumption.
Qed.

Lemma add_assoc_eqi {A B C}: eqi (A + B + C) (A + (B + C)).
Proof.
  split.
  - exact _.
  - transitivity ((B + C) + A). exact _.
    transitivity (B + (C + A)). exact _.
    transitivity ((C + A) + B). exact _.
    transitivity (C + (A + B)). exact _.
    exact _.
Qed.

#[global] Instance ii_False {A}: False + A ≤i A.
Proof.
  exists (fun s => match s with | inl devil => match devil: False with end | inr a => a end).
  intros [[]|a] [[]|a'] e. f_equal. assumption.
Qed.

#[global] Instance option_mono_ii {A B}: A ≤i B -> option A ≤i option B .
Proof.
  intros [i hi]. exists (fun s => match s with | Some a => Some (i a) | None => None end).
  intros [a1|] [a2|] e.
  2,3: discriminate e.
  all: f_equal.
  injection e as e'.
  apply (hi _ _ e').
Qed.

#[global] Instance ii_sum {A B A' B'} {h: A ≤i B} {h': A' ≤i B'}: A + A' ≤i B + B'.
Proof.
  destruct h as [i hi].
  destruct h' as [i' hi'].
  exists (fun s => match s with | inl a => inl (i a) | inr a' => inr (i' a') end).
  intros [a1|a1'] [a2|a2'] e.
  all: try discriminate e.
  all: f_equal.
  all: injection e as e'.
  - apply (hi _ _ e').
  - apply (hi' _ _ e').
Qed.

#[global] Instance ii_left {A B} : A ≤i A + B.
Proof.
  exists (inl).
  intros a a' e. injection e as e'. assumption.
Qed.

#[global] Instance ii_right {A B} : A ≤i B + A.
Proof.
  exists (inr).
  intros a a' e. injection e as e'. assumption.
Qed.

#[global] Instance option_add_eqi_add_option {A B}: eqi (option (A + B)) (option A + B).
Proof.
  split.
  - exists (fun s => match s with | Some (inl a) => inl (Some a) | Some (inr b) => inr b | None => inl None end).
    intros [[a1|b1]|] [[a2|b2]|] e.
    all: try discriminate e.
    all: repeat f_equal.
    all: injection e.
    all: exact id.
  - exists (fun s => match s with inl (Some a) => Some (inl a) | inr b => Some (inr b) | inl None => None end).
    intros [[a|]|b] [[a'|]|b'] e.
    all: try discriminate e.
    all: repeat f_equal.
    all: injection e.
    all: exact id.
Qed.

#[global] Instance onat_ii_nat: option nat ≤i nat.
Proof.
  exists (fun o => match o with | Some n => S n | None => 0 end).
  intros [n|] [n'|] e.
  2,3: discriminate e.
  - injection e as e'. f_equal. assumption.
  - reflexivity.
Qed.

#[global] Instance nat_add_nat_ii_nat: nat + nat ≤i nat.
Proof.
  exists (fun s => match s with inl n => 2 * n | inr n => 2 * n + 1 end)%nat.
  intros [n|n] [n'|n'] e.
  1,4: f_equal; lia. all: exfalso; lia.
Qed.

End OrderInstances.
Section FIN.

  Fixpoint FIN n: Type := match n with | O => False | S n' => option (FIN n') end.

  #[global] Instance FIN_succ: forall n, FIN n ≤i FIN (S n).
  Proof.
    intros n. induction n as [|n' [i hi]].
    - transitivity (False + FIN 1); exact _.
    - exists (fun s => match s with Some m => Some (i m) | None => None end).
      intros [m|] [m'|] H.
      all: try discriminate H.
      all: f_equal.
      injection H as H'. apply (hi _ _ H').
  Qed.

  #[global] Instance FIN_ii_nat: forall n, FIN n ≤i nat.
  Proof.
    intros n. induction n as [|n' [i hi]].
    + transitivity (False + nat); exact _.
    + exists (fun s => match s with | None => 0 | Some x => S (i x) end).
      intros [x|] [x'|] e.
      all: try discriminate e.
      all: f_equal. injection e as e'. apply (hi _ _ e').
  Qed.

  #[global] Instance FIN_succ': forall A n2, option A ≤i FIN (S n2) -> A ≤i FIN n2.
  Proof.
    intros A n2.
    destruct n2 as [|n2].
    + intros [i hi]. simpl in *.
      assert (f: A -> False).
      intros x. destruct (i (Some x)) as [[]|] eqn: ex. destruct (i None) as [[]|] eqn: en.
      rewrite <-ex in en. apply hi in en. discriminate en.
      exists f. intros x. destruct (f x).
    + intros [i hi]. simpl in *.
      exists (fun x => match i (Some x) with
        | Some y => y
        | None =>
          match i None with
          | Some y => y
          | None => None
          end
        end).
      intros x x' e0.
      destruct (i None) as [on|] eqn: en.
      all: destruct (i (Some x')) as [o'|] eqn: e'.
      all: destruct (i (Some x)) as [o|] eqn: e.
      all: try subst o'; try subst on.
      all: try rewrite <-e' in e; try apply hi in e; try injection e; try exact id.
      all: try rewrite <-e' in en; try rewrite <-e in en; try apply hi in en; try discriminate en.
  Qed.

  #[global] Instance add_FIN_eqi {n1 n2: nat}: eqi (FIN n1 + FIN n2) (FIN (n1 + n2)).
  Proof.
    split.
    all: induction n1.
    all: simpl.
    all: try exact _.
    all: transitivity (option (FIN n1 + FIN n2)); exact _.
  Qed.

End FIN.

Section Amorphous.

  Axiom pi: forall P: Prop, forall (p p': P), p = p'.
  Axiom cc: forall r: nat -> nat -> Prop, totalR r -> exists f: nat -> nat, forall n, r n (f n).

  Definition fin X := exists n, X ≤i FIN n.
  Definition subsingleton X := forall x x': X, x = x'.
  (* Definition inf X := nat ≤i X. *)
  Definition oinf X := option X ≤i X.
  Definition sinf X := X + X ≤i X.
  Definition amorphous X := ~ fin X /\ forall Y Z, Y + Z ≤i X -> ~ fin Y -> ~ ~ fin Z.

  (* Fixpoint into_k k x: FIN (S k) :=
  match k, x with
  | O, _ => None
  | S k', O => None
  | S k', S x' => Some (into_k k' x')
  end.

  Lemma into_k_inj {k}: forall x x', x < k -> x' < k -> into_k k x = into_k k x' -> x = x'.
  Proof.
    induction k.
    - intros. lia.
    - intros [|x] [|x'] hx hx' e.
      all: simpl in e; try discriminate e.
      + lia.
      + injection e as e'. f_equal.
        assert (h': x' < k). lia.
        assert (h: x < k). lia.
        apply (IHk _ _ h h' e').
  Qed. 

  Lemma no_bound_on_not_fin:
  forall P: nat -> Type, (forall n, P n ≤i FIN 1) -> ~ fin (sigT P) ->
  forall k, ~ fin ({s: sigT P | k <= let (n, _) := s in n }).
  Proof.
    intros P hP hnfP k.
    simpl. intros [s [is his]].
    apply hnfP. exists (S k + s)%nat.
    transitivity (FIN (S k) + FIN s).
    - exists (fun s: sigT P => let (x, p) := s in
        match Compare_dec.le_lt_dec k x with
        | left e => inr (is (exist _ (existT _ x p) e))
        | right _ => inl (into_k k x)
        end).
      intros [x p] [x' p'] e0.
      destruct (Compare_dec.le_lt_dec k x) as [e|e];
      destruct (Compare_dec.le_lt_dec k x') as [e'|e'].
      all: try discriminate e0.
      all: injection e0 as e0'.
      + apply his in e0'. injection e0' as ex ee. assumption.
      + pose proof (H := into_k_inj x x' e e' e0'). subst x'. f_equal.
        destruct (hP x) as [i1 hi1].
        apply hi1. destruct (i1 p) as [[]|]; destruct (i1 p') as [[]|]. auto.
    - refine ii_of_eqi_l.
  Qed. *)

  Lemma not_fin_nat: ~ fin nat.
  Proof.
    intros [n hn]. induction n.
    - destruct hn as [i _]. apply (i 0).
    - apply IHn. apply FIN_succ'. transitivity nat; exact _.
  Qed.

  (* Lemma not_fin_of_inf: forall X, inf X -> ~ fin X.
  Proof.
    intros X hiX [n hnX]; unfold inf in hiX.
    apply not_fin_nat. exists n. transitivity X; exact _.
  Qed. *)


  Lemma amorphous_sub:
  forall A, amorphous A ->
  forall B, ~ fin B -> B ≤i A -> amorphous B.
  Proof.
    intros A [hiA haA] B hiB hBA. split.
    - exact hiB.
    - intros Y Z hYZ hiY.
      refine (haA Y Z _ hiY).
      transitivity B; exact _.
  Qed.

  Lemma no_inf_sub_amorphous:
  forall A, amorphous A ->
  forall B, B ≤i A -> ~ (nat ≤i B).
  Proof.
    intros A [hiA haA] B hBA hiB.
    apply (fun s: ~ ~ fin nat => s not_fin_nat).
    refine (haA nat nat _ not_fin_nat).
    transitivity nat. exact _. transitivity B; exact _.
  Qed.


  Definition inspect {A : Type} (x: A) : { y : A | x=y } := exist _ x eq_refl.

  Inductive s1 (P: nat -> Type): nat -> Type := 
  | base1: s1 P 0
  | immo1 n': (s1 P n') -> (forall m,
    ({s: sigT P | (let (x, _) := s in x) < n' } ≤i FIN m) ->
    ({s: sigT P | (let (x, _) := s in x) < S n' } ≤i FIN m)) -> s1 P (S n')
  | chng1 n' m:
    s2 P n' ->
    ({s: sigT P | (let (x, _) := s in x) < n' } ≤i FIN m) ->
    ~ ({s: sigT P | (let (x, _) := s in x) < S n' } ≤i FIN m) ->
    s1 P (S n')
  with s2 (P: nat -> Type): nat -> Type := 
  | immo2 n': (s2 P n') -> (forall m,
    ({s: sigT P | (let (x, _) := s in x) < n' } ≤i FIN m) ->
    ({s: sigT P | (let (x, _) := s in x) < S n' } ≤i FIN m)) -> s2 P (S n')
  | chng2 n' m:
    s1 P n' ->
    ({s: sigT P | (let (x, _) := s in x) < n' } ≤i FIN m) ->
    ~ ({s: sigT P | (let (x, _) := s in x) < S n' } ≤i FIN m) ->
    s2 P (S n').

  Lemma s_prop (P: nat -> Type): forall n, (s1 P n * s2 P n) -> False.
  Proof.
    intros n. induction n.
    - firstorder. inversion b.
    - simpl. intros [H1 H2]. inversion H1; inversion H2.
      + auto.
      + subst n' n'0. apply H7, H3, H6.
      + subst n' n'0. apply H4, H7, H3.
      + auto.
  Qed.


  
  
   Axiom inf_of_not_fin: forall P: nat -> Type, (forall n, subsingleton (P n)) -> ~ fin (sigT P) -> nat ≤i (sigT P).

  Lemma core_lemma:
  forall A, amorphous A ->
  forall P: nat -> Type, (forall n, subsingleton (P n)) ->
  ~ fin (sigT P) -> ~ (sigT P ≤i A).
  Proof.
    intros A haA P hsP hnfP hPA.
    apply (inf_of_not_fin _ hsP) in hnfP.
    apply (no_inf_sub_amorphous _ haA _ hPA hnfP).
  Qed.

  Lemma oinf_impl_sinf_prop: (forall X, oinf X -> sinf X) -> forall X, nat + X + X ≤i nat + X.
  Proof.
    intros H X.
    assert (h : oinf (nat + X)). 
    { unfold oinf. transitivity (option nat + X). all: exact _. }
    specialize (H _ h). unfold sinf in H.
    transitivity (nat + X + (nat + X)); exact _.
  Qed.

  Definition B11 {A} (j: nat + A + A -> nat + A) :=
  { x: A & { y: A | j (inl (inr x)) = inr y }}.

  Definition B12 {A} (j: nat + A + A -> nat + A) :=
  { x: A & { y: nat | j (inl (inr x)) = inl y }}.

  Definition jB12 {A} (j: nat + A + A -> nat + A) :=
  { y: nat & { x: A | j (inl (inr x)) = inl y }}.

  Definition jB12' {A} (j: nat + A + A -> nat + A) :=
  { y: nat | exists x: A, j (inl (inr x)) = inl y }.

  Definition B21 {A} (j: nat + A + A -> nat + A) :=
  { x: A & { y: A | j (inr x) = inr y }}.

  Definition B22 {A} (j: nat + A + A -> nat + A) :=
  { x: A & { y: nat | j (inr x) = inl y }}.

  Definition jB22 {A} (j: nat + A + A -> nat + A) :=
  { y: nat & { x: A | j (inr x) = inl y }}.


  Definition A_to_B11_add_jB12 {A} (j: nat + A + A -> nat + A):
  A -> B11 j + jB12 j. 
  Proof.
    intros a.
    destruct (inspect (j (inl (inr a)))) as [[y|y] e].
    - right. exists y. exists a. exact e. 
    - left. exists a. exists y. exact e.
  Defined.

  Instance A_ii_B11_add_jB12 {A} (j: nat + A + A -> nat + A):
  A ≤i B11 j + jB12 j.
  Proof.
    exists (A_to_B11_add_jB12 j).
    intros a1 a2 e. 
    unfold A_to_B11_add_jB12 in e.
    destruct (inspect (j (inl (inr a1)))) as [[a1'|a1'] e1];
    destruct (inspect (j (inl (inr a2)))) as [[a2'|a2'] e2].
    all: try discriminate e.
    all: injection e; auto.
  Qed.

  Instance B12_eqi_jB12 {A} (j: nat + A + A -> nat + A):
  eqi (B12 j) (jB12 j).
  Proof.
    split.
    - exists (fun s: B12 j => match s with | existT _ x (exist _ y e) => existT _ y (exist _ x e) end).
      intros [x [y e]] [x' [y' e']] e0.
      inversion e0. subst x' y'. repeat f_equal. apply pi.
    - exists (fun s: jB12 j => match s with | existT _ y (exist _ x e) => existT _ x (exist _ y e) end).
      intros [y [x e]] [x' [y' e']] e0.
      inversion e0. subst x' y'. repeat f_equal. apply pi.
  Qed.

  Definition A_to_B21_add_jB22 {A} (j: nat + A + A -> nat + A):
  A -> B21 j + jB22 j. 
  Proof.
    intros a.
    destruct (inspect (j (inr a))) as [[y|y] e].
    - right. exists y. exists a. exact e. 
    - left. exists a. exists y. exact e.
  Defined.

  Instance A_ii_B21_add_jB22 {A} (j: nat + A + A -> nat + A):
  A ≤i B21 j + jB22 j.
  Proof.
    exists (A_to_B21_add_jB22 j).
    intros a1 a2 e. 
    unfold A_to_B21_add_jB22 in e.
    destruct (inspect (j (inr a1))) as [[a1'|a1'] e1];
    destruct (inspect (j (inr a2))) as [[a2'|a2'] e2].
    all: try discriminate e.
    all: injection e; auto.
  Qed.

  Instance B22_eqi_jB22 {A} (j: nat + A + A -> nat + A):
  eqi (B22 j) (jB22 j).
  Proof.
    split.
    - exists (fun s: B22 j => match s with | existT _ x (exist _ y e) => existT _ y (exist _ x e) end).
      intros [x [y e]] [x' [y' e']] e0.
      inversion e0. subst x' y'. repeat f_equal. apply pi.
    - exists (fun s: jB22 j => match s with | existT _ y (exist _ x e) => existT _ x (exist _ y e) end).
      intros [y [x e]] [x' [y' e']] e0.
      inversion e0. subst x' y'. repeat f_equal. apply pi.
  Qed.

  Lemma amorphous_prop: forall A, amorphous A -> ~ (nat + A + A ≤i nat + A).
  Proof.
    intros A hA [j hj].

    assert (H_1 : B11 j + B21 j ≤i A).
    {
      exists (fun s => 
        match s with
        | inl (existT _ x (exist _ y _)) => y
        | inr (existT _ x (exist _ y _)) => y
        end).
      intros [[x [y h]]|[x [y h]]] [[x' [y' h']]|[x' [y' h']]] e.
      all: subst y'.
      all: assert (e := h).
      all: rewrite <-h' in e.
      all: apply hj in e.
      all: try discriminate e.
      all: injection e as e'.
      all: subst x'.
      all: repeat f_equal.
      all: apply pi.
    }

    assert (H11: ~ fin (B11 j)).
    {
      intros H11'.
      assert (H12: ~ fin (jB12 j)).
      {
        destruct hA as [hiA _].
        destruct H11' as [n11 hn11].
        intros [n12 hn12].
        apply hiA.
        exists (n11 + n12)%nat.
        transitivity (FIN n11 + FIN n12); [ transitivity (B11 j + jB12 j); exact _ | ].
        refine (ii_of_eqi_l).
      }
      assert (jB12 j ≤i A).
      {
        exists (fun s => match s with | existT _ _ (exist _ x _) => x end).
        intros [x [y e]] [x' [y' e']] e0.
        subst y'.
        pose proof (h := e); rewrite e' in h. injection h as ex. subst x'.
        repeat f_equal. apply pi.
      }
      assert (forall n, subsingleton {x: A | j (inl (inr x)) = inl n}).
      {
        intros n [x e] [x' e'].
        pose proof (h := e). rewrite <-e' in h. apply hj in h. injection h as ex. subst x'.
        f_equal. apply pi.
      }
      refine (core_lemma A hA (fun n => {x: A | j (inl (inr x)) = inl n}) H0 H12 H).
    }

    assert (H21: ~ fin (B21 j)).
    {
      intros H21'.
      assert (H22: ~ fin (jB22 j)).
      {
        destruct hA as [hiA _].
        destruct H21' as [n21 hn21].
        intros [n22 hn22].
        apply hiA.
        exists (n21 + n22)%nat.
        transitivity (FIN n21 + FIN n22); [ transitivity (B21 j + jB22 j); exact _ | ].
        refine (ii_of_eqi_l).
      }
      assert (jB22 j ≤i A).
      {
        exists (fun s => match s with | existT _ _ (exist _ x _) => x end).
        intros [x [y e]] [x' [y' e']] e0.
        subst y'.
        pose proof (h := e); rewrite e' in h. injection h as ex. subst x'.
        repeat f_equal. apply pi.
      }
      assert (forall n, subsingleton {x: A | j (inr x) = inl n}).
      {
        intros n [x e] [x' e'].
        pose proof (h := e). rewrite <-e' in h. apply hj in h. injection h as ex. subst x'.
        f_equal. apply pi.
      }
      refine (core_lemma A hA (fun n => {x: A | j (inr x) = inl n}) H0 H22 H).
    }

    apply (fun s: ~ ~ fin (B21 j) => s H21). destruct hA as [_ haA]. apply (haA (B11 j) (B21 j) _ H11).
  Qed.

  Corollary sinf_is_not_oinf_of_amorphous:
  (exists A, amorphous A) -> ~ (forall X, oinf X -> sinf X).
  Proof.
    intros [A hA] H.
    apply amorphous_prop in hA.
    apply hA.
    apply oinf_impl_sinf_prop.
    apply H.
  Qed.

  Print Assumptions sinf_is_not_oinf_of_amorphous.

End Amorphous.
