From CRUSH Require Import Crush.

(* Set Implicit Arguments. *)

Inductive lis (n: nat) :=
| Nil : lis n
| Cons m : m<=n -> lis n -> lis n.

(* Definition a : lis 4.
  refine (Cons _ (Cons _(Cons _(Nil _))) );crush.
Qed. *)

Fixpoint add_1 (n: nat) (l: lis n) : lis (S n).
  refine (
    match l in (lis _) return lis (S n) with
    | Nil _ => Nil (S n)
    | Cons _ x H l' => Cons (S n) x _ (add_1 _ l')
    end
  );crush.
Defined.

Print add_1.