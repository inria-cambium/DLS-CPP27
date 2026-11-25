Require Import FOL.DLS.Defs FOL.DLS.Utils FOL.DLS.Retracts FOL.DLS.Signatures.

Section Fix_s_f.

  Import VectorNotations.

  Context {s_f: funcs_signature}.

  Fixpoint seq n: vec nat n :=
  match n with
  | O => []
  | S n' => 0 :: map S (seq n')
  end.

  Lemma seq_prop {X n}:
  forall x0 (xv: vec X n),
  map (vec2env xv x0) (seq n) = xv.
  Proof.
    intros x xv. induction xv as [|xh n' xt ih].
    - reflexivity.
    - simpl. rewrite map_map. unfold ".:". f_equal. apply ih.
  Qed.

End Fix_s_f.

Section Plus.
  Import VectorNotations.

  Context (K: Type).
  Context (k0: inhab K).
  Context (X: Type).

  Existing Instance s_0f.
  Instance s_P: preds_signature := Build_preds_signature (fun px: X + unit => match px with | inl _ => 1 | inr tt => 2 end).

  Definition I_plus: interp (X + unit + unit).
  Proof.
    refine (B_I _ _).
    + intros [].
    + intros [px|[]] v.
      - exact (match hd v with | inl (inl vx) => vx = px | inl (inr tt) => True | inr tt => False end).
      - exact (match hd v with | inl (inr tt) | inr tt => True | _ => False end /\ match hd (tl v) with | inr tt => True | _ => False end).
  Defined.

  Definition M_plus := Build_model I_plus.

  Instance sig_plus_retr_K {R: X + unit ≤R K}:
  s_0f + s_P ≤R K.
  Proof.
    exact _.
  Qed.

  Theorem plus_of_DLS_and_oX:
  inhabited (X + unit ≤R K) -> AC X ->
  (DLS_full' K) -> inhabited (X + unit + unit ≤R K).
  Proof.
    intros [R] ac dls.
    destruct (dls _ _ _ M_plus (inr tt)) as [IK [h Hh]]. simpl in *.
    pose (phix := fun x => ∃ (atom (inl x) [$0] ∧ (∀ ¬ (atom (inr tt) [$1; $0])))).
    pose (phil := ∃ ((∃ (atom (inr tt) [$1; $0])) ∧ (¬ (atom (inr tt) [$0; $0])))).
    pose (phir := ∃ ((∃ (atom (inr tt) [$1; $0])) ∧ (atom (inr tt) [$0; $0]))).
    assert (M_phil : M_plus ⊨[(fun _ => k0) >> h] phil).
    { exists (inl (inr tt)). simpl. split. exists (inr tt). auto. intros [_ []]. }
    assert (M_phir : M_plus ⊨[(fun _ => k0) >> h] phir).
    { exists (inr tt). simpl. split. exists (inr tt). auto. auto. }
    assert (K_phix: forall x, Build_model IK ⊨[(fun _ => k0)] phix x).
    {
      intros x. rewrite (Hh _ _). simpl. exists (inl (inl x)). split.
      auto. intros [[x'|[]]|[]]. all: intros [[] _].
    }
    rewrite <-(Hh _ _) in M_phil.
    rewrite <-(Hh _ _) in M_phir.
    destruct M_phil as [kl hkl].
    destruct M_phir as [kr hkr].
    destruct (ac  _ _ (fun (x: X) (k: K) => Build_model IK ⊨[k .: (fun _ => k0)] (atom (inl x: s_P) [$0] ∧ (∀ ¬ (atom (inr tt: s_P) [$1; $0])))) K_phix) as [kx hkx].
    pose (i := fun f: X + unit + unit => 
      match f with
      | inl (inl x) => kx x
      | inl (inr tt) => kl
      | inr tt => kr
      end).
    refine (inhabits (Build_retract i h _)).
    intros f.
    unfold i.
    destruct f as [[x|[]]|[]].
    + specialize (hkx x).
      rewrite (Hh _ _) in hkx.
      simpl in hkx. unfold ">>", ".:" in hkx.
      destruct (h (kx x)) as [[x'|[]]|[]].
      * destruct hkx as [e _]. f_equal; f_equal. assumption.
      * destruct hkx as [_ e]. destruct (e (inr tt)). auto.
      * destruct hkx as [[] _]. 
    + rewrite (Hh _ _) in hkl; unfold ">>", ".:" in hkl; simpl in hkl.
      destruct (h kl) as [[x'|[]]|[]]. all: simpl in *.
      * destruct (hkl) as [[d [[]]] _].
      * auto.
      * destruct hkl as [_ []]. auto.
    + rewrite (Hh _ _) in hkr; unfold ">>", ".:" in hkr; simpl in hkr.
      destruct (h kr) as [[x'|[]]|[]]. all: simpl in *.
      * destruct hkr as [[d [[]]] _].
      * destruct hkr as [_ [_ []]].
      * auto.
  Qed.

  Lemma ac_plus: AC X -> AC (X + unit).
  Proof.
    intros ac Y y0 R htR.
    destruct (htR (inr tt)) as [yt hyt].
    pose (R' := fun x y => R (inl x) y).
    assert (htR': totalR R').
    {
      intros x. destruct (htR (inl x)) as [y hy]. exists y. exact hy.
    }
    destruct (ac Y y0 R' htR') as [f' hf'].
    exists (fun ox => match ox with | inl x => f' x | inr tt => yt end).
    intros [x|[]]; [ apply hf' | apply hyt ].
  Qed.

End Plus.

Section Psim.
  Import VectorNotations.

  Variant sim_P := sim.

  #[global] Instance s_P_sim: preds_signature := Build_preds_signature (fun p: sim_P => 2).
  Definition IP_sim {M}: forall p: s_P_sim, vec M (ar_preds p) -> Prop.
  Proof.
    intros p v. exact ((hd v = (hd (tl v)))).
  Defined.

  Lemma IP_sim_prop {s_f: funcs_signature}
  {L} {l0: L}
  {K: model} {k0: K}
  {IfL: forall f: s_f, vec L (ar_syms f) -> L}
  {h: K -> L}
  {HKL: K ⪳[h] Build_model (B_I IfL IP_sim)}:
  forall (f: s_f) (kv: vec K (ar_syms f)),
  h (i_func _ (interp' K) f kv) = i_func _ (B_I IfL IP_sim) f (map h kv).
  Proof.
    intros f kv.
    assert (H0: sat (interp' K) (fun _ => i_func _ (interp' K) f kv) (atom sim [$0; $0])).
    { rewrite (HKL _ _). unfold IP_sim. reflexivity. }
    simpl in H0.
    assert (H1: sat
      (interp' K)
      (i_func _ (interp' K) f kv .: vec2env kv k0)
      (atom sim [$0; func f (map var (map S (seq (ar_syms f))))])).
    {
      simpl.
      rewrite map_map, map_map.
      unfold eval. unfold ".:".
      rewrite seq_prop.
      exact H0.
    }
    rewrite (HKL _ _) in H1.
    unfold IP_sim in H1. simpl in *.
    unfold ".:" at 1 in H1.
    unfold ">>" in H1.
    rewrite H1. f_equal.
    unfold eval, ".:".
    simpl.
    rewrite map_map, map_map.
    rewrite <-(map_map nat K L (vec2env kv k0) h).
    rewrite seq_prop.
    reflexivity.
  Qed.

End Psim.

From Stdlib Require Import List.
Import ListNotations.

Section Nat.
  Section ThreeNat.

  Variant nat_f := fO | fS.
  Instance s_f_nat: funcs_signature := Build_funcs_signature
  (fun f =>
    match f with
    | fO => 0
    | fS => 1
    end).

  Definition I_nat: interp nat.
  Proof.
    refine (B_I _ (IP_sim)).
    intros [|] v.
    + exact 0.
    + exact (S (Vector.hd v)).
  Defined.

  Definition M_nat := Build_model I_nat.

  Instance sig_nat_retr_K {K} {sK: unit + unit + unit ≤R K}:
  s_f_nat + s_P_sim ≤R K.
  Proof.
    assert (R:=Build_retract
      (fun s =>
        match s with
        | inl fO => inr tt
        | inl fS => inl (inr tt)
        | inr sim => (inl (inl tt))
        end)
      (fun s =>
        match s with
        | inr tt => inl fO
        | inl (inr tt) => inl fS
        | inl (inl tt) =>inr sim
        end)
      (fun s => match s with | inl fO | inl fS | inr sim => eq_refl end)
      ).
    compose_retracts [ unit + unit + unit ]%type.
  Qed.

  Theorem nat_of_DLS_and_three
  {K} {k0: inhab K}:
  (inhabited (unit + unit + unit ≤R K)) ->
  (DLS_full' K) -> inhabited (nat ≤R K).
  Proof.
    intros [sK] dls.
    unfold DLS_full' in dls.
    destruct (dls s_f_nat _ _ M_nat 0) as [IK [h Hh]]. simpl in *.
    pose (i := fix i n :=
      match n with
      | 0 => i_func _ IK fO (Vector.map i (Vector.nil _))
      | S n' => i_func _ IK fS (Vector.map i (Vector.cons _ n' _ (Vector.nil _)))
      end).
    refine (inhabits (Build_retract i h _)).
    intros n. induction n as [|n' ih].
    all: simpl.
    - pose proof (HO := IP_sim_prop
        (l0:=0)
        (k0:=_: inhab (domain (Build_model IK)))
        (HKL:=Hh)
        (fO: s_f_nat)).
      simpl in HO. rewrite HO. reflexivity.
    - pose proof (HS := IP_sim_prop
        (l0:=0)
        (k0:=_: inhab (domain (Build_model IK)))
        (HKL:=Hh)
        (fS: s_f_nat)).
      simpl in HS. rewrite HS. f_equal. simpl. exact ih.
  Qed.

  End ThreeNat.

  Theorem nat_of_DLS_and_one
  {K} {sK: inhab K}:
  (DLS_full' K) -> inhabited (nat ≤R K).
  Proof.
    intros dls.
    refine (nat_of_DLS_and_three _ dls).
    enough (H: inhabited (False + unit + unit + unit ≤R K)).
    destruct H; apply inhabits. compose_retracts [False + unit + unit + unit]%type.
    refine (plus_of_DLS_and_oX _ _ _ _ (ac_plus _ _) dls).
    refine (plus_of_DLS_and_oX _ _ _ _ _ dls).
    exact (inhabits _).
    all: intros Y y0 R htR; exists (fun devil: False => match devil with end); intros [].
  Qed.

End Nat.

Section List.

  Context (K: Type).
  Context (oK: K + unit ≤R K).

  Inductive list_f := fnil | fcons (k: K).

  Instance s_f_list : funcs_signature := Build_funcs_signature
  (fun f =>
    match f with
    | fnil => 0
    | fcons k => 1
    end).

  Definition I_list: interp (list K).
  Proof.
    refine (B_I _ (IP_sim)).
    intros [|k] v.
    + exact (nil).
    + exact (k :: Vector.hd v).
  Defined.

  Definition M_list := Build_model I_list.

  Instance K_add_two_retr_K:
  K + unit + unit ≤R K.
  Proof.
    compose_retracts [ K + unit ]%type.
  Qed.

  Instance sig_list_retr_K:
  s_f_list + s_P_sim ≤R K.
  Proof.
    assert (R:=Build_retract
      (fun s =>
        match s with
        | inl fnil => inl (inr tt)
        | inl (fcons k) => inl (inl k)
        | inr sim => (inr tt)
        end)
      (fun s =>
        match s with
        | inr tt => inr sim
        | inl (inr tt) => inl fnil
        | inl (inl k) => inl (fcons k)
        end)
      (fun s => match s with | inl fnil | inr sim => eq_refl | inl (fcons k) => eq_refl end)
      ).
    compose_retracts [ K + unit + unit ]%type.
  Qed.

  Instance inhab_of_oinf:
  inhab K.
  Proof.
    pose proof (_: unit ≤R K).
    pose proof (_: inhab unit).
    exact (inhab_retr (X:=unit)).
  Qed.

  Theorem pinf_of_DLS_and_oinf:
  (DLS_full' K) -> inhabited (list K ≤R K).
  Proof.
    intros dls.
    unfold DLS_full' in dls.
    destruct (dls s_f_list _ _ M_list []) as [IK [h Hh]]. simpl in *.
    pose (i := fix i n :=
      match n with
      | nil => i_func _ IK fnil (Vector.map i (Vector.nil _))
      | cons k lk => i_func _ IK (fcons k) (Vector.map i (Vector.cons _ lk _ (Vector.nil _)))
      end).
    refine (inhabits (Build_retract i h _)).
    intros l. induction l as [|k lk ih].
    all: simpl.
    - pose proof (HO := IP_sim_prop
        (l0:=[])
        (k0:=_: inhab (domain (Build_model IK)))
        (HKL:=Hh)
        (fnil: s_f_list)).
      simpl in HO. rewrite HO. reflexivity.
    - pose proof
        (HS := IP_sim_prop (l0:=[])
        (k0:=_: inhab (domain (Build_model IK)))
        (HKL:=Hh)
        (fcons k: s_f_list)).
      simpl in HS. rewrite HS. f_equal. simpl. exact ih.
  Qed.

End List.

Section ListListList.

Instance nat_retr_list2 K: nat ≤R list (list K).
Proof. refine (Build_retract
  (fix i n := match n with | 0 => [] | S n' => [] :: i n' end)
  (fix s l := match l with | [] => 0 | _ :: l' => S (s l') end)
  _).
  induction x as [|n' ih]. all: auto.
Qed.

Instance list3_nat_retr_list3 K: list (list (list K)) * nat ≤R list (list (list K)).
Proof.
  pose proof (R := _ : nat ≤R list (list K)).
  refine (Build_retract 
    (fun p: _ * nat => let (l, n) := p in retr_i R n :: l)
    (fun l => match l with | [] => ([], 0) | h :: t => (t, retr_s R h) end)
    _).
  intros [l n]. rewrite retr_o. reflexivity.
Qed.

Fact firstn_app_self {K} (l: list K): forall l', firstn (length l) (l ++ l') = l.
Proof.
  induction l.
  - auto.
  - simpl. intros. f_equal. apply IHl.
Qed.

Fact skipn_app_self {K} (l: list K): forall l', skipn (length l) (l ++ l') = l'.
Proof.
  induction l.
  - auto.
  - simpl. intros. apply IHl.
Qed.

Instance list2_retr_list1_nat K: list (list K) ≤R list K * list nat.
Proof.
  pose (s := fix s (r: list K) ln :=
    match ln with
    | [] => []
    | hn :: tn => firstn hn r :: (s (skipn hn r) tn)
    end).
  pose (i := fix i (L: list (list K)) :=
    match L with
    | [] => ([], [])
    | h :: t =>(h ++ let (r, ln) := i t in r, length h :: let (r, ln) := i t in ln)
    end).
  refine (Build_retract
    i
    (fun p => match p with | pair l ln => s l ln end)
    _).
  intros L. induction L as [|H T ih].
  - auto.
  - destruct (i (H :: T)) as [r ln] eqn: eL. simpl in eL. injection eL as e elength.
    subst r ln. simpl. rewrite firstn_app_self, skipn_app_self.
    destruct (i T) eqn: eT.
    auto using f_equal.
Qed.

Instance list4_retr_list3 K: strongInf (list (list (list K))).
Proof.
  compose_retracts [
    list (list (list K)) * list nat;
    list (list (list K)) * nat
  ]%type.
Qed.

Instance list2_retr_list_o {K}: list (list K) ≤R list (option K).
Proof.
  pose (before := fix before (l: list (option K)) :=
    match l with
    | [] => []
    | None :: l' => []
    | Some k :: l' => k :: before l'
    end).
  pose (after := fix after (l: list (option K)) :=
    match l with
    | Some _ :: l' => after l'
    | _ => l
    end).
  refine (Build_retract
    (fix i L := match L with | [] => [] | l :: L' => None :: (map Some l) ++ i L' end)
    (fix s inp :=
    match inp with
    | [] => []
    | None :: l' => before l' :: s (after l')
    | Some k :: l' => []
    end)
    _).
  intros L. induction L as [|H T ih].
  - auto.
  - induction H as [|k H' ih'].
    + simpl. f_equal.
      * destruct T. all: auto.
      * destruct T. all: auto.
    + simpl. injection ih' as eH eT. f_equal.
      * f_equal. assumption.
      * assumption.
Qed.


Instance list_mono_sum_retr A B: list A + list B ≤R option (list (A + B)).
Proof.
  pose (sl := fix sl (l: list (A + B)) := match l with | [] => [] | (inl a) :: l' => a :: sl l' | (inr _) :: l' => sl l' end).
  pose (sr := fix sr (l: list (A + B)) := match l with | [] => [] | (inl _) :: l' => sr l' | (inr b) :: l' => b :: sr l' end).
  refine (Build_retract
    (fun s => match s with | inl la => Some (map inl la) | inr [] => None | inr lb => Some (map inr lb) end)
    (fun ol => match ol with
      | None => inr []
      | Some [] => inl []
      | Some (inl a :: l') => inl (a :: sl l')
      | Some (inr b :: l') => inr (b :: sr l')
    end)
    _).
  intros [la|lb].
  - destruct la.
    + reflexivity.
    + simpl. repeat f_equal. induction la. auto. simpl. auto using f_equal.
  - destruct lb.
    + reflexivity.
    + simpl. repeat f_equal. induction lb. auto. simpl. auto using f_equal.
Qed.

End ListListList.