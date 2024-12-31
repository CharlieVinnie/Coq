From CRUSH Require Import Crush.
Require Import Arith Lia.

Goal forall (P Q: nat -> Prop) m, (P m <-> Q m) -> Q m.
Proof.
  Crush.
Abort.

Ltac test:=
  repeat (match goal with
            | [ H : ?P |- _ ] =>
              match P with
                | ?x = ?y => rewrite P
                | forall t1, ?x = ?y => rewrite P
              end
          end).

Ltac test0:= timeout 2 test.


Goal forall n m, ( (n <=? m) = false <-> n <= m ) -> n <= m.
Proof.
  Print Rewrite HintDb core.
  intros. destruct H as [H1 H2].
  test0.
Abort.

Ltac f n :=
  match n with
  | O => idtac
  | S ?n' =>
    try (match goal with
      | [ H : ?P |- _ ] =>
        match P with
          | _ => (rewrite H;trivial)
        end
    end; f n')
  end.

Goal forall n m, ( (n <=? m) = false <-> n <= m ) -> n <= m.
Proof.
  intros. destruct H as [H1 H2].
  rewrite H1.
  f 101.
Abort.