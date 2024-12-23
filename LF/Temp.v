
Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export Logic.


Fixpoint div2 (n : nat) :=
  match n with
    0 => 0
  | 1 => 0
  | S (S n) => S (div2 n)
  end.

Definition f (n : nat) :=
  if even n then div2 n
  else (3 * n) + 1.


Inductive Collatz_holds_for : nat -> Prop :=
  | Chf_done : Collatz_holds_for 1
  | Chf_more (n : nat) : Collatz_holds_for (f n) -> Collatz_holds_for n.
