From CRUSH Require Import Crush.
Require Import Arith.

Goal forall n, (n<=0 <-> n<=1) -> S n <= 2.
  Crush.
Abort.

Goal forall n m, ( (n <=? m) = false <-> n <= m ) -> n <= m.
Proof.
  intros. destruct H as [H1 H2]. 
  crush.