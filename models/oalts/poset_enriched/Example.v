Require Import Coq.Init.Nat.
Require Import Coq.Arith.PeanoNat.
Require Import coqrel.LogicalRelations.
Require Import models.DCPO.
Require Import models.oalts.DownsetMonad.
Require Import models.oalts.poset_enriched.PosetBicartesian.
Require Import models.oalts.poset_enriched.PosetAsyncEvents.
Require Import models.oalts.poset_enriched.PosetDownsetKleisli.
Require Import models.oalts.poset_enriched.TimeDownset.
Require Import models.oalts.poset_enriched.PosetAlts.

(** * Example: A Simple Counter Transition System

    States: natural numbers
    Events:
      - inc: increment the counter
      - get(n): observe the current value n
      - tau (implicit): silent transition, stays in same state
*)

(** ** Event Type *)

Inductive event : Type :=
  | inc : event
  | get : nat -> event.

(** Events with discrete partial order (only reflexive) *)
Definition event_le (e1 e2 : event) : Prop := e1 = e2.

Lemma event_le_preo : PreOrder event_le.
Proof.
  constructor.
  - intros x. reflexivity.
  - intros x y z Hxy Hyz. unfold event_le in *. congruence.
Qed.

Lemma event_le_po : Antisymmetric event eq event_le.
Proof.
  intros x y Hxy Hyx. exact Hxy.
Qed.

Definition EventPO : DCPO.PartialOrder event :=
  {| le := event_le;
     le_preo := event_le_preo;
     le_po := event_le_po |}.

Definition EventPoset : Poset.t := @Poset.mkt event EventPO.

(** ** State Type *)

(** States are natural numbers with discrete order *)
Definition state_le (n m : nat) : Prop := n = m.

Lemma state_le_preo : PreOrder state_le.
Proof.
  constructor.
  - intros x. reflexivity.
  - intros x y z Hxy Hyz. unfold state_le in *. congruence.
Qed.

Lemma state_le_po : Antisymmetric nat eq state_le.
Proof.
  intros x y Hxy Hyx. exact Hxy.
Qed.

Definition StatePO : DCPO.PartialOrder nat :=
  {| le := state_le;
     le_preo := state_le_preo;
     le_po := state_le_po |}.

Definition StatePoset : Poset.t := @Poset.mkt nat StatePO.

(** ** The Step Function *)

(** The lifted event type: L(E) = 1 + E *)
Definition LEvent := PosetAsyncEvents.L.omap EventPoset.

(** The target type: L(E) × S *)
Definition StepTarget := PosetTimeFunctor.omap EventPoset StatePoset.

(** Partial order on the target *)
Definition StepTargetPO := Poset.structure StepTarget.

(** Build the step function.
    For state n, the possible transitions are:
    - (inl tt, n) : tau, stay in state n
    - (inr inc, S n) : increment to n+1
    - (inr (get n), n) : get the current value
*)

Definition step_pred (n : nat) : (unit + event) * nat -> Prop :=
  fun p =>
    match p with
    | (inl tt, m) => m = n                  (* tau: stay in n *)
    | (inr inc, m) => m = S n               (* inc: go to n+1 *)
    | (inr (get k), m) => k = n /\ m = n    (* get(n): stay in n *)
    end.

(** Prove downward closure *)
Lemma step_pred_closed (n : nat) :
  forall p1 p2, @le _ StepTargetPO p1 p2 -> step_pred n p2 -> step_pred n p1.
Proof.
  intros [[a1 | e1] m1] [[a2 | e2] m2] [He Hm] H2;
    simpl in *; try contradiction.
  - (* tau case: a1 : unit, a2 : unit *)
    destruct a1, a2. unfold state_le in Hm. rewrite Hm. exact H2.
  - (* event case: e1, e2 : event *)
    unfold event_le in He. unfold state_le in Hm. subst.
    exact H2.
Qed.

Definition step_dset (n : nat) : @DownsetMonadDef.dset _ StepTargetPO :=
  @DownsetMonadDef.mk_dset _ StepTargetPO (step_pred n) (step_pred_closed n).

(** The step function as a morphism in Kleisli(Downset) *)
Definition step_fun (n : nat) : @DownsetMonadDef.dset _ StepTargetPO := step_dset n.

Lemma step_mor : @Poset.Morphism _ _ StatePO (Poset.structure (DownsetMonadDef.omap StepTarget)) step_fun.
Proof.
  intros n1 n2 Hle. destruct Hle. reflexivity.
Qed.

Definition step : Poset.m StatePoset (DownsetMonadDef.omap StepTarget) :=
  @Poset.mkm StatePoset (DownsetMonadDef.omap StepTarget) step_fun step_mor.

(** ** The Counter ALTS *)

Definition Counter : PosetAlts.t :=
  PosetAltsInternal.mk_coalg EventPoset StatePoset step.
