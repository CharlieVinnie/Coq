From TLC Require Import LibTactics.

Ltac nats n tac :=
  match n with
  | O => idtac
  | S ?n' => tac n;nats n' tac
  end.

Inductive obj (n:nat) :=
  | qwq.

Goal forall (P:nat -> Prop) (a b c d :nat), True.
Proof.
  intros.
  nats 10 ltac:(fun n=>let Q:=fresh "Q" in specialize (qwq n) as Q).
  specialize (qwq a) as A.
  generalize Q. clear Q. intro Q.
  generalize Q. clear Q. intro Q.
  generalize Q. clear Q. intro Q.
  generalize Q. clear Q. intro Q.
  generalize Q. clear Q. intro Q.
  generalize Q. clear Q. intro Q.
  generalize Q. clear Q. intro Q.
  generalize Q. clear Q. intro Q.
  (* let t := Q in generalize Q; clear Q; specialize t. *)
  generalize A. clear A. intro A.

  repeat match goal with
  | [ H : _ |- _ ] => generalize H;clear H
  end.
  intros.
Abort.