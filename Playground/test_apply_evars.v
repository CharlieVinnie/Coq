Inductive sth (x y z:nat) := | qwq.

Goal forall (A B:Type) (P: A->B->Prop) (x:A) (y:B), False.
Proof.
  intros.
  repeat match goal with
  | [ P:forall (_:?x), _ |- _ ] => let t:=fresh "t" in
      evar (t:x);specialize (P t)
  end.
  (* is_evar t. *)

Goal forall (P: nat->nat->nat->Prop), False.
Proof.
  intros.
  evar (x: _).
  evar (y: nat).
  specialize (qwq x y x).
  let u := eval compute in x in is_evar u.
  