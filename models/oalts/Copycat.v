Require Import Oalts.
Require Import Karoubi.

Import OALTS.
Import Karoubi.

Require Import List.
Import ListNotations.
Open Scope event_obj_scope.

Definition cc_state {A : sig} : Type := list [A].

Definition cc_start {A : sig} (s : @cc_state A) : Prop := s = [].


Definition cc_trans {A : sig} 
  (s : @cc_state A) (ev : Async [A -o A]%event_obj) (s' : @cc_state A) : Prop :=
  match ev with
  | 'neg ⟨ | an ⟩ => s' = (neg an)::s 
  | 'neg ⟨ an | ⟩ => exists s1 s2, s = s1 ++ [neg an] ++ s2 /\ s' = s1 ++ s2
  | 'pos ⟨ ap | ⟩ => s' = (pos ap)::s
  | 'pos ⟨ | ap ⟩ => exists s1 s2, s = s1 ++ [pos ap] ++ s2 /\ s' = s1 ++ s2
  | _ => False
  end.

Definition cc (A : sig) : oalts A A :=
    {|
      states := @cc_state A;
      start := cc_start;
      trans := cc_trans;
    |}.
