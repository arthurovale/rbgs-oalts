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
  Definition strat (A B : sig) : Type := tree «A -o B».

  Definition id_gen {A : sig} (ev : [A]) : «A -o A» :=
    match ev with
    | inl a => ⟨tgt a | src a⟩
    | inr a => ⟨src a | tgt a⟩
    end.

  CoFixpoint id (A : sig) : strat A A :=
    go (StepF [A] id_gen (fun _ => id A)).

  Module StLess.
    Import Sets.

    CoFixpoint StLess {A B : sig} (gen : Sig.m A B) : strat A B :=
      go (StepF [A]
        (fun ev =>
          match ev with
          | inl a =>
            match gen^- a with
            | 'b => ⟨tgt b | src a⟩
            | ɛ => ⟨ | src a⟩
            end
          | inr a =>
            match gen^+ a with
            | 'b => ⟨src a | tgt b⟩
            | ɛ => ⟨src a | ⟩
            end
          end)
        (fun _ => StLess gen)).

    Proposition id_stless_id {A : sig} :
      sbisim (id A) (StLess (Sig.id A)).
    Proof.
      pcofix IH. pfold. unfold sbisimF. simpl.
      split; intros ev; exists ev;
      destruct ev as [a | a]; split;
      try reflexivity; right; exact IH.
    Qed.
  End StLess.

  (** ** Strategy Composition *)

  Section Compose.
    Context {A B C : sig}.

    (** Index type for composed visible events:
        - Asynchronous A event
        - Asynchronous C event
        - Visible syncs (A and C components with matching B, excluding pure syncs) *)
    Definition compose_visible_idx
      (Xσ Xτ : Type) (stepσ : Xσ -> «A -o B») (stepτ : Xτ -> «B -o C») : Type :=
      { x : Xσ | projR (stepσ x) = ɛ } +
      { y : Xτ | projL (stepτ y) = ɛ } +
      { xy : Xσ * Xτ |
          projR (stepσ (fst xy)) = projL (stepτ (snd xy)) /\
          projR (stepσ (fst xy)) <> ɛ /\
          has_visible_AC (stepσ (fst xy)) (stepτ (snd xy)) = true }.

    (** Combine two events with matching B components into an A -o C event.
        evσ contributes the A component, evτ contributes the C component.
        Requires proof that at least one of A or C component is visible. *)
    Definition combine_sync (evσ : «A -o B») (evτ : «B -o C»)
      (Hvis : has_visible_AC evσ evτ = true) : «A -o C».
    Proof.
      unfold has_visible_AC in Hvis.
      (* Extract A component from evσ (env = A^+ or sys = A^-) *)
      destruct evσ as [[ap | bm] [am | bp] | [ap | bm] | [am | bp]];
      (* Extract C component from evτ (env = C^- or sys = C^+) *)
      destruct evτ as [[bp' | cm] [bm' | cp] | [bp' | cm] | [bm' | cp]];
      simpl in Hvis.
      (* All 64 cases - extract A from σ, C from τ *)
      (* σ = ⟨src ap | src am⟩ (A sync) cases - all have A component *)
      - exact ⟨src ap | src am⟩.  (* τ = ⟨src bp' | src bm'⟩ *)
      - exact ⟨src ap | src am⟩.  (* τ = ⟨src bp' | tgt cp⟩ *)
      - exact ⟨src ap | src am⟩.  (* τ = ⟨tgt cm | src bm'⟩ *)
      - exact ⟨src ap | src am⟩.  (* τ = ⟨tgt cm | tgt cp⟩ *)
      - exact ⟨src ap | src am⟩.  (* τ = ⟨src bp' |⟩ *)
      - exact ⟨src ap | src am⟩.  (* τ = ⟨tgt cm |⟩ *)
      - exact ⟨src ap | src am⟩.  (* τ = ⟨| src bm'⟩ *)
      - exact ⟨src ap | src am⟩.  (* τ = ⟨| tgt cp⟩ *)
      (* σ = ⟨src ap | tgt bp⟩ cases - all have A component *)
      - exact ⟨src ap |⟩.         (* τ = ⟨src bp' | src bm'⟩ *)
      - exact ⟨src ap | tgt cp⟩.  (* τ = ⟨src bp' | tgt cp⟩ *)
      - exact ⟨src ap |⟩.         (* τ = ⟨tgt cm | src bm'⟩ *)
      - exact ⟨src ap | tgt cp⟩.  (* τ = ⟨tgt cm | tgt cp⟩ *)
      - exact ⟨src ap |⟩.         (* τ = ⟨src bp' |⟩ *)
      - exact ⟨src ap |⟩.         (* τ = ⟨tgt cm |⟩ *)
      - exact ⟨src ap |⟩.         (* τ = ⟨| src bm'⟩ *)
      - exact ⟨src ap | tgt cp⟩.  (* τ = ⟨| tgt cp⟩ *)
      (* σ = ⟨tgt bm | src am⟩ cases - all have A component *)
      - exact ⟨| src am⟩.         (* τ = ⟨src bp' | src bm'⟩ *)
      - exact ⟨| src am⟩.         (* τ = ⟨src bp' | tgt cp⟩ *)
      - exact ⟨tgt cm | src am⟩.  (* τ = ⟨tgt cm | src bm'⟩ *)
      - exact ⟨tgt cm | src am⟩.  (* τ = ⟨tgt cm | tgt cp⟩ *)
      - exact ⟨| src am⟩.         (* τ = ⟨src bp' |⟩ *)
      - exact ⟨tgt cm | src am⟩.  (* τ = ⟨tgt cm |⟩ *)
      - exact ⟨| src am⟩.         (* τ = ⟨| src bm'⟩ *)
      - exact ⟨| src am⟩.         (* τ = ⟨| tgt cp⟩ *)
      (* σ = ⟨tgt bm | tgt bp⟩ (B sync) cases - no A component, need C component *)
      - discriminate Hvis.        (* τ = ⟨src bp' | src bm'⟩ - pure sync, unreachable *)
      - exact ⟨| tgt cp⟩.         (* τ = ⟨src bp' | tgt cp⟩ *)
      - exact ⟨tgt cm |⟩.         (* τ = ⟨tgt cm | src bm'⟩ *)
      - exact ⟨tgt cm | tgt cp⟩.  (* τ = ⟨tgt cm | tgt cp⟩ *)
      - discriminate Hvis.        (* τ = ⟨src bp' |⟩ - pure sync, unreachable *)
      - exact ⟨tgt cm |⟩.         (* τ = ⟨tgt cm |⟩ *)
      - discriminate Hvis.        (* τ = ⟨| src bm'⟩ - pure sync, unreachable *)
      - exact ⟨| tgt cp⟩.         (* τ = ⟨| tgt cp⟩ *)
      (* σ = ⟨src ap |⟩ cases - all have A component *)
      - exact ⟨src ap |⟩.         (* τ = ⟨src bp' | src bm'⟩ *)
      - exact ⟨src ap | tgt cp⟩.  (* τ = ⟨src bp' | tgt cp⟩ *)
      - exact ⟨src ap |⟩.         (* τ = ⟨tgt cm | src bm'⟩ *)
      - exact ⟨src ap | tgt cp⟩.  (* τ = ⟨tgt cm | tgt cp⟩ *)
      - exact ⟨src ap |⟩.         (* τ = ⟨src bp' |⟩ *)
      - exact ⟨src ap |⟩.         (* τ = ⟨tgt cm |⟩ *)
      - exact ⟨src ap |⟩.         (* τ = ⟨| src bm'⟩ *)
      - exact ⟨src ap | tgt cp⟩.  (* τ = ⟨| tgt cp⟩ *)
      (* σ = ⟨tgt bm |⟩ cases - no A component, need C component *)
      - discriminate Hvis.        (* τ = ⟨src bp' | src bm'⟩ - pure sync, unreachable *)
      - exact ⟨| tgt cp⟩.         (* τ = ⟨src bp' | tgt cp⟩ *)
      - exact ⟨tgt cm |⟩.         (* τ = ⟨tgt cm | src bm'⟩ *)
      - exact ⟨tgt cm | tgt cp⟩.  (* τ = ⟨tgt cm | tgt cp⟩ *)
      - discriminate Hvis.        (* τ = ⟨src bp' |⟩ - pure sync, unreachable *)
      - exact ⟨tgt cm |⟩.         (* τ = ⟨tgt cm |⟩ *)
      - discriminate Hvis.        (* τ = ⟨| src bm'⟩ - pure sync, unreachable *)
      - exact ⟨| tgt cp⟩.         (* τ = ⟨| tgt cp⟩ *)
      (* σ = ⟨| src am⟩ cases - all have A component *)
      - exact ⟨| src am⟩.         (* τ = ⟨src bp' | src bm'⟩ *)
      - exact ⟨| src am⟩.         (* τ = ⟨src bp' | tgt cp⟩ *)
      - exact ⟨tgt cm | src am⟩.  (* τ = ⟨tgt cm | src bm'⟩ *)
      - exact ⟨tgt cm | src am⟩.  (* τ = ⟨tgt cm | tgt cp⟩ *)
      - exact ⟨| src am⟩.         (* τ = ⟨src bp' |⟩ *)
      - exact ⟨tgt cm | src am⟩.  (* τ = ⟨tgt cm |⟩ *)
      - exact ⟨| src am⟩.         (* τ = ⟨| src bm'⟩ *)
      - exact ⟨| src am⟩.         (* τ = ⟨| tgt cp⟩ *)
      (* σ = ⟨| tgt bp⟩ cases - no A component, need C component *)
      - discriminate Hvis.        (* τ = ⟨src bp' | src bm'⟩ - pure sync, unreachable *)
      - exact ⟨| tgt cp⟩.         (* τ = ⟨src bp' | tgt cp⟩ *)
      - exact ⟨tgt cm |⟩.         (* τ = ⟨tgt cm | src bm'⟩ *)
      - exact ⟨tgt cm | tgt cp⟩.  (* τ = ⟨tgt cm | tgt cp⟩ *)
      - discriminate Hvis.        (* τ = ⟨src bp' |⟩ - pure sync, unreachable *)
      - exact ⟨tgt cm |⟩.         (* τ = ⟨tgt cm |⟩ *)
      - discriminate Hvis.        (* τ = ⟨| src bm'⟩ - pure sync, unreachable *)
      - exact ⟨| tgt cp⟩.         (* τ = ⟨| tgt cp⟩ *)
    Defined.

    (** Step function for composed visible events *)
    Definition compose_visible_step
      (Xσ Xτ : Type) (stepσ : Xσ -> «A -o B») (stepτ : Xτ -> «B -o C»)
      : compose_visible_idx Xσ Xτ stepσ stepτ -> «A -o C» :=
      fun idx =>
        match idx with
        | inl (inl (exist _ x Hx)) => embed_L (stepσ x) Hx
        | inl (inr (exist _ y Hy)) => embed_R (stepτ y) Hy
        | inr (exist _ (x, y) (conj _ (conj _ Hvis))) =>
            combine_sync (stepσ x) (stepτ y) Hvis
        end.

  End Compose.

  (** Compose two strategies *)
  CoFixpoint compose {A B C : sig} (σ : strat A B) (τ : strat B C) : strat A C :=
    match observe σ, observe τ with
    | EpsF Xσ kσ, _ =>
        go (EpsF Xσ (fun x => compose (kσ x) τ))
    | StepF _ _ _, EpsF Xτ kτ =>
        go (EpsF Xτ (fun y => compose σ (kτ y)))
    | StepF Xσ stepσ kσ, StepF Xτ stepτ kτ =>
        (* Pure syncs: B-only on both sides with matching B *)
        let pure_sync_idx := { xy : Xσ * Xτ |
            projR (stepσ (fst xy)) = projL (stepτ (snd xy)) /\
            projR (stepσ (fst xy)) <> ɛ /\
            projL (stepσ (fst xy)) = ɛ /\
            projR (stepτ (snd xy)) = ɛ } in
        let visible_tree :=
            go (StepF
              (compose_visible_idx Xσ Xτ stepσ stepτ)
              (compose_visible_step Xσ Xτ stepσ stepτ)
              (fun idx =>
                match idx with
                | inl (inl (exist _ x _)) => compose (kσ x) τ
                | inl (inr (exist _ y _)) => compose σ (kτ y)
                | inr (exist _ (x, y) _) => compose (kσ x) (kτ y)
                end)) in
        go (EpsF
          (pure_sync_idx + unit)
          (fun choice =>
            match choice with
            | inl (exist _ (x, y) _) => compose (kσ x) (kτ y)
            | inr tt => visible_tree
            end))
    end.

  Notation "σ ;; τ" := (compose σ τ) (at level 40, left associativity).

End Strat.
