(*
Trying to find counterexamples to implications between different kinds of infinity
The thing is, there are 2 relations on types:
- through retracts
- through injections;
and there are 3 kinds of infinity:
- (oinf) X + 1 ≤ X
- (sinf) X + X ≤ X ∧ 1 ≤ X
- (pinf) X * X ≤ X ∧ 2 ≤ X.
 *)

Require Import FOL.DLS.Retracts.
From Stdlib Require Import List Fin PeanoNat Classes.Morphisms Lia.

Section Preamble.

Definition injective {A B} (f: A -> B) := forall a1 a2, f a1 = f a2 -> a1 = a2.

Definition le_r A B := inhabited ((A ≤R B)).

Definition le_i A B := exists i: A -> B, injective i.

End Preamble.
Notation "A ≤r B" := (le_r A B) (at level 90).
Notation "A ≤i B" := (le_i A B) (at level 90).
Section Utils.

#[global] Instance ler_refl: Reflexive le_r.
Proof.
  intros X. apply inhabits. exact _.
Qed.
#[global] Instance ler_trans: Transitive le_r.
Proof.
  intros X Y Z [h1] [h2].
  apply inhabits. compose_retracts (List.cons Y List.nil).
Qed.

#[global] Instance lei_refl: Reflexive le_i.
Proof.
  intros X. exists id. intros x x'. auto.
Qed.
#[global] Instance lei_trans: Transitive le_i.
Proof.
  intros X Y Z [i hi] [i' hi'].
  exists (fun x => i' (i x)).
  intros x x'. auto.
Qed.

Lemma lei_of_ler {A B}: A ≤r B -> A ≤i B.
Proof.
  intros [[i s o]]. exists i. intros a a' e.
  apply (f_equal s) in e. repeat rewrite o in e.
  assumption.
Qed.

Lemma nler_of_nlei {A B}: ~ (A ≤i B) -> ~ (A ≤r B).
Proof.
  intros H h. apply H, lei_of_ler, h.
Qed.

Definition oinf_r X := option X ≤r X.
Definition oinf_i X := option X ≤i X.
Definition sinf_r X := (X + X ≤r X) /\ (unit ≤r X).
Definition sinf_i X := (X + X ≤i X) /\ (unit ≤i X).
Definition pinf_r X := (X * X ≤r X) /\ (bool ≤r X).
Definition pinf_i X := (X * X ≤i X) /\ (bool ≤i X).

Lemma oinf_i_of_r {X}: oinf_r X -> oinf_i X.
Proof.
  apply lei_of_ler.
Qed.

Lemma sinf_i_of_r {X}: sinf_r X -> sinf_i X.
Proof.
  intros [? ?]; split.
  all: apply lei_of_ler; assumption.
Qed.

Lemma pinf_i_of_r {X}: pinf_r X -> pinf_i X.
Proof.
  intros [? ?]; split.
  all: apply lei_of_ler; assumption.
Qed.

End Utils.

Lemma add_nat_oinf: forall A, oinf_r (A + nat).
Proof.
  intros A. apply inhabits.
  refine (Build_retract
   (fun o => match o with | Some (inl a) => inl a | Some (inr n) => inr (S n) | None => inr 0 end)
   (fun s => match s with | inl a => Some (inl a) | inr 0 => None | inr (S n) => Some (inr n) end)
   (fun o => match o with | None => eq_refl | Some (inl a) => eq_refl | Some (inr n) => eq_refl end)
   ).
Qed.

Lemma mul_nat_sinf: forall A, inhabited A -> sinf_r (A * nat).
Proof.
  intros A [a]. split.
  - transitivity (A * (nat + nat))%type.
    all: apply inhabits.
    + refine (Build_retract
        (fun s => match s with | inl (a, n) => (a, inl n) | inr (a, n) => (a, inr n) end)
        (fun p => match p with | (a, inl n) => inl (a, n) | (a, inr n) => inr (a, n) end)
        (fun s => match s with | inl (a, n) => eq_refl | inr (a, n) => eq_refl end)
        ).
    + exact _.
  - apply inhabits.
    pose proof ((a, 0) : inhab (A * nat)).
    exact _.
Qed.

Goal forall A, ~ (A + A + nat ≤i A + nat) -> oinf_r (A + nat) /\ ~ sinf_i (A + nat).
Proof.
  intros A H. split.
  - apply add_nat_oinf.
  - intros [h _]. apply H.
    transitivity (A + nat + (A + nat))%type.
    + exists (fun s => match s with | inl (inl a) => inl (inl a) | inl (inr a) => inr (inl a) | inr n => inr (inr n) end).
      intros [[|]|] [[|]|] e.
      all: try discriminate e.
      all: repeat f_equal; injection e as e'; assumption.
    + assumption.
Qed.

Goal forall A, inhabited A -> ~ (A * A * nat ≤i A * nat) -> sinf_r (A * nat) /\ ~ pinf_i (A * nat).
Proof.
  intros A [a] H. split.
  - apply mul_nat_sinf, inhabits, a.
  - intros [h _]. apply H.
    transitivity (A * nat * (A * nat))%type.
    + exists (fun p => match p with | ((a, a'), n) => ((a, 0), (a', n)) end).
      intros [[]] [[]] e.
      repeat f_equal; injection e as e'; assumption.
    + assumption.
Qed.