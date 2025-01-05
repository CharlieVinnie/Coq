Ltac bad := bad.

Goal True.
Proof.
  (try constructor); match goal with | _ => idtac end; bad.
  (* first [(match goal with | _ => bad end)|idtac]. *)
Qed.
