From CRUSH Require Import Crush.
From TLC Require Import LibTactics.

From Coq Require Import List.

Inductive F {T:Type}: list T -> Prop :=
  | Cons a b : F a -> F b -> F (a++b).

Hint Constructors F : core.

Local Lemma list_app_1 : forall (T:Type) (a b c d:list T),
  a++b++c++d = a++(b++c)++d.
Proof. intros;repeat rewrite app_assoc;reflexivity. Qed.

Local Lemma list_app_2 : forall (T:Type) (a b c d e:list T),
  a++(b++c)++d++e = a++(b++c++d)++e.
Proof. intros;repeat rewrite app_assoc;reflexivity. Qed.

Ltac list_splitter' tac :=
  match goal with
      | [ |- context[ ?o ++ ?a ++ ?b ++ ?c ] ] => rewrite list_app_1
      | [ |- context[ ?o ++ (?a ++ ?b) ++ ?c ++ ?d ] ] => rewrite list_app_2
      | [ |- context[ ?o ++ ?a ++ ?b ] ] =>
        let a' := fresh "a" in
          remember a as a'; rewrite app_assoc
  end;try tac;list_splitter' tac.

Ltac list_splitter tac :=
  match goal with
      (* | [ |- context[ ?o ++ ?a ++ ?b ++ ?c ] ] => rewrite list_app_1
      | [ |- context[ ?o ++ (?a ++ ?b) ++ ?c ++ ?d ] ] => rewrite list_app_2 *)
      | [ |- context[ ?o ++ ?a ++ ?b ] ] =>
        let a' := fresh "a" in
          remember a as a'; rewrite app_assoc
  end;try tac.

Goal forall T (x1 x2 x3: list T),
  F x1 -> F (x2++x3) -> F (x1++x2++x3).
Proof.
  intros. rewrite <- app_nil_l.
  (* match goal with
      (* | [ |- context[ ?o ++ ?a ++ ?b ++ ?c ] ] => rewrite list_app_1 *)
      (* | [ |- context[ ?o ++ (?a ++ ?b) ++ ?c ++ ?d ] ] => rewrite list_app_2 *)
      | [ |- context[ ?o ++ ?a ++ ?b ] ] =>
        let a' := fresh "a" in
          remember a as a'; rewrite app_assoc
  end.
  solve[crush]. *)
  list_splitter ltac:(solve[crush]).

Goal forall T (x1 x2 x3 x4 x5 x6 x7 l1 l2 l3 l4 l5: list T),
  l1 = x1 ++ x2 ->
  l2 = x3 ++ x4 ->
  l3 = x6 ++ x7 ->
  l4 = x1 ++ x2 ++ x3 ->
  l5 = x4 ++ x5 ++ x6 ->
  F l1 -> F l2 -> F x5 -> F l3 ->
  F (x1++x2++x3++x4++x5++x6++x7).
Proof.
  intros.
  (* cuts_rewrite <- ( (x1++x2)++(x3++x4)++x5++(x6++x7) = x1++x2++x3++x4++x5++x6++x7 ).
  remember (x1++x2) as a.
  remember (x3++x4) as b.
  remember (x5) as c.
  remember (x6++x7) as d.
  try subst. crush. *)
  repeat rewrite <- app_assoc in *. simpl in *.
  rewrite <- app_nil_l.
  list_splitter (idtac "hey").
  repeat (
    match goal with
      | [ |- context[ ?o ++ ?a ++ ?b ++ ?c ] ] => rewrite list_app_1
      | [ |- context[ ?o ++ (?a ++ ?b) ++ ?c ++ ?d ] ] => rewrite list_app_2
      | [ |- context[ ?o ++ ?a ++ ?b ] ] =>
        let a' := fresh "a" in
          remember a as a'; rewrite app_assoc
      (* | [ H : ?a =~ _ |- context [?a ++ _] ] =>
        let a' := fresh "a" in
          sets_eq a': a
      | [ |- context [?ab ++ ?cd] ] =>
        match ab with
        | ?a ++ ?b =>
          match cd with
          | ?c ++ ?d => rewrite list_app_progress
          | _ => fail 3
          end
        | _ => first [ rewrite app_assoc | fail 2 ]
        end *)
    end;try solve[crush]
  ).