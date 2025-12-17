Require Import interfaces.Category.
Require Import interfaces.Functor.
Require Import interfaces.DoubleCat.

Module Idempotents (V : CategoryDefinition) (D : DoubleCategory V) <: Category.
  Import D.
  Import Siso.

  Record idem (a : V.t) :=
    {
      carrier :> hcell a a;
      idempotency : sisocell (carrier ⨀ carrier) carrier;
      idem_coh : (idempotency ⊙ vid carrier) ;; idempotency =
        assoc carrier carrier carrier ;; (vid carrier ⊙ idempotency) ;; idempotency;
    }.
  Arguments carrier {_}.
  Arguments idempotency {_}.
  Arguments idem_coh {_}.    

  Record idem_obj := 
    mk_idem_obj {
      idem_type : V.t;
      idem_carrier :> idem idem_type
    }.

  Program Definition id_idem (a : V.t) :=
    {|
      carrier := hid a;
      idempotency := runit (hid a);
    |}.
  Next Obligation.
    rewrite <- lunit_hid_runit_hid. rewrite <- unit_coh.
    rewrite lunit_hid_runit_hid. reflexivity.
  Defined.

  Definition idem_to_obj {a : V.t} : idem a -> idem_obj 
    := fun e => mk_idem_obj a e.
  Coercion idem_to_obj : idem >-> idem_obj.
  
  Definition t : Type := idem_obj.

  Record idem_vmor {a : V.t} (e : idem a) {b : V.t} (e' : idem b) :=
    {
      idem_vmor_carrier :> V.m a b;
      idem_vmor_sq : e =[idem_vmor_carrier, idem_vmor_carrier]=> e';
      idem_vmor_coh : idempotency e ;; idem_vmor_sq = 
        idem_vmor_sq ⊙ idem_vmor_sq ;; idempotency e';
    }.

  Definition m : t -> t -> Type := fun e => fun e' => idem_vmor e e'.

  Program Definition idem_id_vmor {a : V.t} (e : idem a) : idem_vmor e e :=
    {|
      idem_vmor_carrier := V.id a;
      idem_vmor_sq := vid e;
    |}.
  Next Obligation.
    rewrite hcomp_fmap_id. rewrite vid_is_Vert_id.
    rewrite Vert.compose_id_left. rewrite vid_is_Vert_id. 
    rewrite Vert.compose_id_right. reflexivity.
  Defined.

  Definition id (e : t) : m e e := idem_id_vmor e.

End Idempotents.