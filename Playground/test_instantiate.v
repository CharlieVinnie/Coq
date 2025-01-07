From CRUSH Require Import Crush.
From TLC Require Import LibTactics.

Goal forall (A B:Prop), (A->B) -> A -> B.
Proof. crush.