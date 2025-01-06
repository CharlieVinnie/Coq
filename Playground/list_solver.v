From CRUSH Require Import Crush.
From TLC Require Import LibTactics.

From Coq Require Import List.

Inductive F {T:Type}: list T -> Prop :=
  | Cons a b : F a -> F b -> F (a++b).

Hint Constructors F : core.

Ltac get_sub_helper l cont :=
  match l with
  | ?a ++ ?b =>
    match goal with
    | [ |- context [a] ] =>
      get_sub_helper b ltac:(
        match goal with
        | [ |- context [ a ++ b ++ ?c ] ] => rewrite (@app_assoc _ a b c)
        end;cont
      )
    end
  | _ =>
    match goal with
    | [ |- context [l] ] => cont
    end
  end.

Ltac get_sub l := get_sub_helper l idtac.

Ltac subst_sub l :=
  let l' := fresh "l" in
  let H := fresh "Heq_l" in
  sets_eq l' H: l; clear H.

Ltac generalize_sub l := get_sub l; subst_sub l.

Ltac try_generalize_sublists solver :=
  match goal with
  | [ H: context [ ?a ++ ?b ] |- _ ] =>
    generalize_sub (a++b); try solve[solver]; try_generalize_sublists solver
  end.

Ltac list_solver solver :=
  simpl; repeat rewrite <- app_assoc in *; try_generalize_sublists solver.

Goal forall T (x1 x2 x3 x4 x5 x6 x7 x8 l1 l2 l3 l4 l5: list T),
  l1 = x1 ++ x2 ->
  l2 = x3 ++ x4 ->
  l3 = x6 ++ x7 ->
  l4 = x1 ++ x2 ++ x3 ->
  l5 = x5 ++ x6 ++ x7 ->
  (* F l1 -> F l2 -> F x5 -> F l3 -> *)
  F l4 -> F x4 -> F l5 -> F x8 ->
  F (x1++x2++x3++x4++x5++x6++x7++x8).
Proof.
  crush; list_solver crush.
Qed.

Goal forall T (x1 x2 x3 x4: list T),
  F (x1++x2) ->
  F (x1++x3++x4) ->
  F (x4++x2) ->
  F (x2++x1) ->
  F (x1++x3++x4++x2++x1).
Proof.
  crush; list_solver crush.
Qed.
