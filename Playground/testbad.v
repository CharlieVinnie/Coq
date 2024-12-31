From CRUSH Require Import Crush.
Require Import Arith.

Goal forall (P Q: nat -> Prop) m, (P m <-> Q m) -> Q m.
Proof.
  Crush.
Abort.

Goal forall n m, ( (n <=? m) = false <-> n <= m ) -> n <= m.
Proof.
  intros. destruct H as [H1 H2]. 
  Crush.