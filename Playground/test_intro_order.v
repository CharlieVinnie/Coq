From TLC Require Import LibTactics.

Ltac nats n tac :=
  match n with
  | O => idtac
  | S ?n' => tac n;nats n' tac
  end.

Inductive obj (n:nat) :=
  | qwq.

Goal forall (P:nat -> Prop), True.
Proof.
  intros.
  nats 10 ltac:(fun n=>let Q:=fresh "Q" in specialize (qwq n) as Q).
  repeat match goal with
  | [ H : _ |- _ ] => generalize H;clear H
  end.
  intros.