Require Import TLC.LibTactics.

Lemma qwq : forall A B C D, A /\ B /\ C /\ D -> C /\ A /\ D /\ B.
Proof.
    introv H. destructs H. splits; assumption.
Qed.

Lemma qwq2 : forall A B C D, A \/ B \/ C \/ D -> C \/ A \/ D \/ B.
Proof.
    introv H. branches H;
    try (branch 1;assumption);
    try (branch 2;assumption);
    try (branch 3;assumption);
    try (branch 4;assumption).
Qed.