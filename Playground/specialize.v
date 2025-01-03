Goal forall (x:nat) P, P x -> False.
Proof.
    intros. specialize (P 1) as P0.