Require Import interfaces.Category.
Require Import oalts.AsyncEvents.
Require Import oalts.Sig.
Require Import oalts.Tree.

From Paco Require Import paco.

Module Strat. (* <: Category *)
  Import AsyncEvents.
  Import Sig.
  Import Tree.

  Local Open Scope event_obj_scope.

  (** Strategies from A to B are trees of [A -o B] events *)
  Definition strat (A B : sig) : Type := tree ([A -o B]).

  (** ** Identity Strategy *)

  (** Step function for identity: maps [A] events to [A -o A] events
      An input am : A^- becomes neg ⟨am | am⟩
      An output ap : A^+ becomes pos ⟨ap | ap⟩ *)
  Definition id_step {A : sig} (ev : [A]) : [A -o A] :=
    match ev with
    | neg am => neg ⟨am | am⟩
    | pos ap => pos ⟨ap | ap⟩
    end.

  CoFixpoint id (A : sig) : strat A A :=
    go (StepF [A] id_step (fun _ => id A)).

  (** ** StateLess Strategies *)

  Module StateLess.

    (** Step function for stateless strategy:
        Maps [A] events to [A -o B] events based on generator *)
    Definition stless_step {A B : sig} (gen : Sig.m A B) (ev : [A]) : [A -o B] :=
      match ev with
      | neg am =>  (* A^- input *)
        match gen^- am with
        | 'bm => neg ⟨am | bm⟩
        | ɛ => neg ⟨am |⟩
        end
      | pos ap =>  (* A^+ output *)
        match gen^+ ap with
        | 'bp => pos ⟨ap | bp⟩
        | ɛ => pos ⟨ap |⟩
        end
      end.

    CoFixpoint StLess {A B : sig} (gen : Sig.m A B) : strat A B :=
      go (StepF [A] (stless_step gen) (fun _ => StLess gen)).

    (** Identity strategy equals StLess of identity generator *)
    Proposition id_stless_id {A : sig} :
      sbisim (id A) (StLess (Sig.id A)).
    Proof.
      pcofix IH. pfold. unfold sbisimF. simpl.
      split; intros ev; exists ev;
      destruct ev as [am | ap]; simpl;
      unfold stless_step; simpl;
      split; try reflexivity; right; exact IH.
    Qed.

  End StateLess.

  (** ** Strategy Composition *)

  Section Compose.
    Context {A B C : sig}.

    (** Index type for visible composed events:
        - Left-only: σ has A-only event (projR = ɛ)
        - Right-only: τ has C-only event (projL = ɛ)
        - Sync: matching B events with visible A or C component *)
    Inductive compose_vis_idx
      (Xσ Xτ : Type) (stepσ : Xσ -> [A -o B]) (stepτ : Xτ -> [B -o C]) : Type :=
    | cv_left (x : Xσ) : projR (stepσ x) = ɛ -> compose_vis_idx Xσ Xτ stepσ stepτ
    | cv_right (y : Xτ) : projL (stepτ y) = ɛ -> compose_vis_idx Xσ Xτ stepσ stepτ
    | cv_sync (x : Xσ) (y : Xτ) :
        projR (stepσ x) = projL (stepτ y) ->
        (projL (stepσ x) <> ɛ \/ projR (stepτ y) <> ɛ) ->
        compose_vis_idx Xσ Xτ stepσ stepτ.

    Arguments cv_left {Xσ Xτ stepσ stepτ}.
    Arguments cv_right {Xσ Xτ stepσ stepτ}.
    Arguments cv_sync {Xσ Xτ stepσ stepτ}.

    (** Combine events from σ and τ into an A-o-C event *)
    Definition compose_event {Xσ Xτ : Type}
      (stepσ : Xσ -> [A -o B]) (stepτ : Xτ -> [B -o C])
      (idx : compose_vis_idx Xσ Xτ stepσ stepτ) : [A -o C].
    Proof.
      destruct idx as [x Heps | y Heps | x y Hmatch Hvis].
      - (* Left-only: extract A component from σ *)
        destruct (stepσ x) as [[am_bm | am | bm] | [ap_bp | ap | bp]];
        simpl in Heps; try discriminate.
        + exact (neg ⟨am |⟩).
        + exact (pos ⟨ap |⟩).
      - (* Right-only: extract C component from τ *)
        destruct (stepτ y) as [[bm_cm | bm | cm] | [bp_cp | bp | cp]];
        simpl in Heps; try discriminate.
        + exact (neg ⟨| cm⟩).
        + exact (pos ⟨| cp⟩).
      - (* Sync: combine A from σ with C from τ *)
        destruct (projL (stepσ x)) as [a |] eqn:Ha;
        destruct (projR (stepτ y)) as [c |] eqn:Hc.
        + (* Both visible *)
          destruct a as [am | ap]; destruct c as [cm | cp].
          * exact (neg ⟨am | cm⟩).
          * (* neg/pos mismatch - provide dummy, unreachable by typing *)
            exact (neg ⟨am |⟩).
          * (* pos/neg mismatch - provide dummy, unreachable by typing *)
            exact (pos ⟨ap |⟩).
          * exact (pos ⟨ap | cp⟩).
        + (* A visible, C epsilon *)
          destruct a as [am | ap].
          * exact (neg ⟨am |⟩).
          * exact (pos ⟨ap |⟩).
        + (* A epsilon, C visible *)
          destruct c as [cm | cp].
          * exact (neg ⟨| cm⟩).
          * exact (pos ⟨| cp⟩).
        + (* Both epsilon - contradicts Hvis *)
          exfalso. destruct Hvis as [H | H]; congruence.
    Defined.

    (** Index for pure sync (silent transitions):
        Both sides have B-only events with matching B components *)
    Definition pure_sync_idx
      (Xσ Xτ : Type) (stepσ : Xσ -> [A -o B]) (stepτ : Xτ -> [B -o C]) : Type :=
      { xy : Xσ * Xτ |
        projR (stepσ (fst xy)) = projL (stepτ (snd xy)) /\
        projR (stepσ (fst xy)) <> ɛ /\
        projL (stepσ (fst xy)) = ɛ /\
        projR (stepτ (snd xy)) = ɛ }.

  End Compose.

  (** Compose two strategies *)
  CoFixpoint compose {A B C : sig} (σ : strat A B) (τ : strat B C) : strat A C :=
    match observe σ, observe τ with
    | EpsF Xσ kσ, _ =>
        go (EpsF Xσ (fun x => compose (kσ x) τ))
    | StepF _ _ _, EpsF Xτ kτ =>
        go (EpsF Xτ (fun y => compose σ (kτ y)))
    | StepF Xσ stepσ kσ, StepF Xτ stepτ kτ =>
        let visible_tree :=
          go (StepF
            (compose_vis_idx Xσ Xτ stepσ stepτ)
            (compose_event stepσ stepτ)
            (fun idx =>
              match idx return strat A C with
              | cv_left _ _ _ _ x _ => compose (kσ x) τ
              | cv_right _ _ _ _ y _ => compose σ (kτ y)
              | cv_sync _ _ _ _ x y _ _ => compose (kσ x) (kτ y)
              end)) in
        go (EpsF
          (pure_sync_idx Xσ Xτ stepσ stepτ + unit)
          (fun choice =>
            match choice with
            | inl (exist _ (x, y) _) => compose (kσ x) (kτ y)
            | inr tt => visible_tree
            end))
    end.

  Notation "σ ;; τ" := (compose σ τ) (at level 40, left associativity).

End Strat.
