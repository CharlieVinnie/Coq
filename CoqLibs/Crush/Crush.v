(* Copyright (c) 2008-2012, Adam Chlipala
 * 
 * This work is licensed under a
 * Creative Commons Attribution-Noncommercial-No Derivative Works 3.0
 * Unported License.
 * The license text is available at:
 *   http://creativecommons.org/licenses/by-nc-nd/3.0/
 *)

Require Import Eqdep List Lia.

Set Implicit Arguments.


(** A version of [injection] that does some standard simplifications afterward: clear the hypothesis in question, bring the new facts above the double line, and attempt substitution for known variables. *)
Ltac inject H := injection H; clear H; intros; try subst.

(** Try calling tactic function [f] on all hypotheses, keeping the first application that doesn't fail. *)
Ltac appHyps f :=
  match goal with
    | [ H : _ |- _ ] => f H
  end.

(** Succeed iff [x] is in the list [ls], represented with left-associated nested tuples. *)
Ltac inList x ls :=
  match ls with
    | x => idtac
    | (_, x) => idtac
    | (?LS, _) => inList x LS
  end.

(** Try calling tactic function [f] on every element of tupled list [ls], keeping the first call not to fail. *)
Ltac app f ls :=
  match ls with
    | (?LS, ?X) => f X || app f LS || fail 1
    | _ => f ls
  end.

(** Run [f] on every element of [ls], not just the first that doesn't fail. *)
Ltac all f ls :=
  match ls with
    | (?LS, ?X) => f X; all f LS
    | (_, _) => fail 1
    | _ => f ls
  end.

(** Succeed iff a >= b *)
Ltac geq_tac a b :=
  match b with
  | O => idtac
  | S ?b' => match a with | S ?a' => geq_tac a' b' end
  end.

(** Workhorse tactic to simplify hypotheses for a variety of proofs.
   * Argument [invOne] is a tuple-list of predicates for which we always do inversion automatically. *)
Ltac simplHyp' invOne branches :=
  (** Helper function to do inversion on certain hypotheses, where [H] is the hypothesis and [F] its head symbol *)
  let invert H F :=
    (** We only proceed for those predicates in [invOne]. *)
    inList F invOne;
    (** This case covers an inversion that succeeds immediately, meaning no constructors of [F] applied. *)
      (inversion H; fail)
    (** Otherwise, we only proceed if inversion eliminates all but one constructor case. *)
      || (inversion H; [idtac]; clear H; try subst)
      || (geq_tac branches 2; inversion H; [idtac|idtac]; clear H; try subst)
      || (geq_tac branches 3; inversion H; [idtac|idtac|idtac]; clear H; try subst)
      || (geq_tac branches 4; inversion H; [idtac|idtac|idtac|idtac]; clear H; try subst)
      || (geq_tac branches 5; inversion H; [idtac|idtac|idtac|idtac|idtac]; clear H; try subst)
      in

  match goal with
    (** Eliminate all existential hypotheses. *)
    | [ H : ex _ |- _ ] => destruct H

    (** Find opportunities to take advantage of injectivity of data constructors, for several different arities. *)
    | [ H : ?F ?X = ?F ?Y |- ?G ] =>
      (** This first branch of the [||] fails the whole attempt iff the arguments of the constructor applications are already easy to prove equal. *)
      (assert (X = Y); [ assumption | fail 1 ])
      (** If we pass that filter, then we use injection on [H] and do some simplification as in [inject].
         * The odd-looking check of the goal form is to avoid cases where [injection] gives a more complex result because of dependent typing, which we aren't equipped to handle here. *)
      || (injection H;
        match goal with
          | [ |- X = Y -> G ] =>
            try clear H; intros; try subst
        end)
    | [ H : ?F ?X ?U = ?F ?Y ?V |- ?G ] =>
      (assert (X = Y); [ assumption
        | assert (U = V); [ assumption | fail 1 ] ])
      || (injection H;
        match goal with
          | [ |- U = V -> X = Y -> G ] =>
            try clear H; intros; try subst
        end)

    (** Consider some different arities of a predicate [F] in a hypothesis that we might want to invert. *)
    | [ H : ?F _ |- _ ] => invert H F
    | [ H : ?F _ _ |- _ ] => invert H F
    | [ H : ?F _ _ _ |- _ ] => invert H F
    | [ H : ?F _ _ _ _ |- _ ] => invert H F
    | [ H : ?F _ _ _ _ _ |- _ ] => invert H F

    (** Use an (axiom-dependent!) inversion principle for dependent pairs, from the standard library. *)
    | [ H : existT _ ?T _ = existT _ ?T _ |- _ ] => generalize (inj_pair2 _ _ _ _ _ H); clear H

    (** If we're not ready to use that principle yet, try the standard inversion, which often enables the previous rule. *)
    | [ H : existT _ _ _ = existT _ _ _ |- _ ] => inversion H; clear H

    (** Similar logic to the cases for constructor injectivity above, but specialized to [Some], since the above cases won't deal with polymorphic constructors. *)
    | [ H : Some _ = Some _ |- _ ] => injection H; clear H
  end.

Tactic Notation "simplHyp" constr(invOne) := simplHyp' invOne 1.

Tactic Notation "simplHyp" constr(invOne) integer(n) := simplHyp' invOne n.

(** Find some hypothesis to rewrite with, ensuring that [auto] proves all of the extra subgoals added by [rewrite]. *)
Ltac rewriteHyp :=
  match goal with
    | [ H : _ |- _ ] => rewrite H by solve [ auto ]
  end.

(** Combine [autorewrite] with automatic hypothesis rewrites. *)
Ltac rewriterP := repeat (rewriteHyp; autorewrite with core in *).
Ltac rewriter := autorewrite with core in *; rewriterP.

(** This one is just so darned useful, let's add it as a hint here. *)
(* Hint Rewrite app_assoc. *)
Hint Rewrite <- app_assoc.

(** Devious marker predicate to use for encoding state within proof goals *)
Definition done (T : Type) (x : T) := True.

(** Try a new instantiation of a universally quantified fact, proved by [e].
   * [trace] is an accumulator recording which instantiations we choose. *)
Ltac inster e trace :=
  (** Does [e] have any quantifiers left? *)
  match type of e with
    | forall x : _, _ =>
      (** Yes, so let's pick the first context variable of the right type. *)
      match goal with
        | [ H : _ |- _ ] =>
          inster (e H) (trace, H)
        | _ => fail 2
      end
    | _ =>
      (** No more quantifiers, so now we check if the trace we computed was already used. *)
      match trace with
        | (_, _) =>
          (** We only reach this case if the trace is nonempty, ensuring that [inster] fails if no progress can be made. *)
          match goal with
            | [ H : done (trace, _) |- _ ] =>
              (** Uh oh, found a record of this trace in the context!  Abort to backtrack to try another trace. *)
              fail 1
            | _ =>
              (** What is the type of the proof [e] now? *)
              let T := type of e in
                match type of T with
                  | Prop =>

                    (** Charlie: A small modification to eliminate duplicate proofs *)
                    match goal with
                    | [ H: e |- _ ] => fail 2
                    end;

                    (** [e] should be thought of as a proof, so let's add it to the context, and also add a new marker hypothesis recording our choice of trace. *)
                    generalize e; intro;
                      assert (done (trace, tt)) by constructor
                  | _ =>
                    (** [e] is something beside a proof.  Better make sure no element of our current trace was generated by a previous call to [inster], or we might get stuck in an infinite loop!  (We store previous [inster] terms in second positions of tuples used as arguments to [done] in hypotheses.  Proofs instantiated by [inster] merely use [tt] in such positions.) *)
                    all ltac:(fun X =>
                      match goal with
                        | [ H : done (_, X) |- _ ] => fail 1
                        | _ => idtac
                      end) trace;
                    (** Pick a new name for our new instantiation. *)
                    let i := fresh "i" in (pose (i := e);
                      assert (done (trace, i)) by constructor)
                end
          end
      end
  end.

(** After a round of application with the above, we will have a lot of junk [done] markers to clean up; hence this tactic. *)
Ltac un_done :=
  repeat match goal with
           | [ H : done _ |- _ ] => clear H
         end.

Require Import JMeq.

(** A more parameterized version of the famous [crush].  Extra arguments are:
   * - A tuple-list of lemmas we try [inster]-ing 
   * - A tuple-list of predicates we try inversion for *)
Ltac crush' lemmas invOne branches :=
  (** A useful combination of standard automation *)
  let sintuition := simpl in *; intuition; try subst;
    repeat (simplHyp' invOne branches; intuition; try subst); try congruence in

  (** A fancier version of [rewriter] from above, which uses [crush'] to discharge side conditions *)
  let rewriter := autorewrite with core in *;
    repeat (match goal with
              | [ H : ?P |- _ ] =>
              let rewrite_H := rewrite H by crush' lemmas invOne branches in
                match P with
                  | context[JMeq] => fail 1 (** JMeq is too fancy to deal with here. *)
                  (* | _ => rewrite H by crush' lemmas invOne *)
                  | _ = _ => rewrite_H
                  | forall t1, _ = _ => rewrite_H
                  | forall t1 t2, _ = _ => rewrite_H
                  | forall t1 t2 t3, _ = _ => rewrite_H
                  | forall t1 t2 t3 t4, _ = _ => rewrite_H
                  (* This part is refactored, due to rewrite sometimes acts like apply :( *)
                end
            end; autorewrite with core in *) in

  (** Now the main sequence of heuristics: *)
    (sintuition; rewriter;
      match lemmas with
        | false => idtac (** No lemmas?  Nothing to do here *)
        | _ =>
          (** Try a loop of instantiating lemmas... *)
          repeat ((app ltac:(fun L => inster L L) lemmas
          (** ...or instantiating hypotheses... *)
            || appHyps ltac:(fun L => inster L L));
          (** ...and then simplifying hypotheses. *)
          repeat (simplHyp' invOne branches; intuition)); un_done
      end;
      sintuition; rewriter; sintuition;
      (** End with a last attempt to prove an arithmetic fact with [lia], or prove any sort of fact in a context that is contradictory by reasoning that [lia] can do. *)
      try lia; try (exfalso; lia)).

Ltac crush_with_aux cru tac :=
  solve [tac;cru].
  (* app ltac:(fun x => x;cru;crush_with_aux cru tac) tac. *)

Ltac crush_with lemmas invOne branches tac :=
  let cru := crush' lemmas invOne branches in
    cru; crush_with_aux cru tac.

Tactic Notation "crush" := crush' false false 1.

Tactic Notation "crush" "lemma:" constr(a) := crush' a false 1.

Tactic Notation "crush" "inv:" constr(b) := crush' false b 1.

Tactic Notation "crush" "lemma:" constr(a) "inv:" constr(b) := crush' a b 1.

Tactic Notation "crush" "width:" constr(n) :=
  let n' := eval compute in n in crush' false false n'.

Tactic Notation "crush" "lemma:" constr(a) "width:" constr(n) :=
  let n' := eval compute in n in crush' a false n'.

Tactic Notation "crush" "inv:" constr(b) "width:" constr(n) :=
  let n' := eval compute in n in crush' false b n'.

Tactic Notation "crush" "lemma:" constr(a) "inv:" constr(b) "width:" constr(n) :=
  let n' := eval compute in n in crush' a b n'.


Tactic Notation "crush" "with" ltac(t) := crush_with false false 1 t.

Tactic Notation "crush" "lemma:" constr(a) "with" ltac(t) := crush_with a false 1 t.

Tactic Notation "crush" "inv:" constr(b) "with" ltac(t) := crush_with false b 1 t.

Tactic Notation "crush" "lemma:" constr(a) "inv:" constr(b) "with" ltac(t) := crush_with a b 1 t.

Tactic Notation "crush" "width:" constr(n) "with" ltac(t) :=
  let n' := eval compute in n in crush_with false false n' t.

Tactic Notation "crush" "lemma:" constr(a) "width:" constr(n) "with" ltac(t) :=
  let n' := eval compute in n in crush_with a false n' t.

Tactic Notation "crush" "inv:" constr(b) "width:" constr(n) "with" ltac(t) :=
  let n' := eval compute in n in crush_with false b n' t.

Tactic Notation "crush" "lemma:" constr(a) "inv:" constr(b) "width:" constr(n) "with" ltac(t) :=
  let n' := eval compute in n in crush_with a b n' t.


From TLC Require Import LibTactics.

Ltac unfolder ls := all ltac:(fun x => try unfolds x) ls.

Ltac applyer ls := all ltac:(fun x => try apply x) ls.

(** [crush] instantiates [crush'] with the simplest possible parameters. *)
(* Ltac crush := crush' false false. *)

(** * Wrap Program's [dependent destruction] in a slightly more pleasant form *)

Require Import Program.Equality.

(** Run [dependent destruction] on [E] and look for opportunities to simplify the result.
   The weird introduction of [x] helps get around limitations of [dependent destruction], in terms of which sorts of arguments it will accept (e.g., variables bound to hypotheses within Ltac [match]es). *)
Ltac dep_destruct E :=
  let x := fresh "x" in
    remember E as x; simpl in x; dependent destruction x;
      try match goal with
            | [ H : _ = E |- _ ] => try rewrite <- H in *; clear H
          end.

(** Nuke all hypotheses that we can get away with, without invalidating the goal statement. *)
Ltac clear_all :=
  repeat match goal with
           | [ H : _ |- _ ] => clear H
         end.

(** Instantiate a quantifier in a hypothesis [H] with value [v], or, if [v] doesn't have the right type, with a new unification variable.
   * Also prove the lefthand sides of any implications that this exposes, simplifying [H] to leave out those implications. *)
Ltac guess v H :=
  repeat match type of H with
           | forall x : ?T, _ =>
             match type of T with
               | Prop =>
                 (let H' := fresh "H'" in
                   assert (H' : T); [
                     solve [ eauto 6 ]
                     | specialize (H H'); clear H' ])
                 || fail 1
               | _ =>
                 specialize (H v)
                 || let x := fresh "x" in
                   evar (x : T);
                   let x' := eval unfold x in x in
                     clear x; specialize (H x')
             end
         end.

(** Version of [guess] that leaves the original [H] intact *)
Ltac guessKeep v H :=
  let H' := fresh "H'" in
    generalize H; intro H'; guess v H'.


(** My Tactics & Hints *)

Ltac Crush := timeout 5 crush.

Ltac Induct n :=
  match n with
  | 1 => match goal with | [ |- forall x, _ ] => induction x end
  | S ?n' => match goal with | [ |- forall x, _ ] => intros x;Induct n' end
  end.

From Coq Require Import Arith.Arith.
Require Export Coq.Strings.String.

Hint Extern 1 =>
  match goal with
  | [ |- context[Nat.eqb ?x ?x] ] => rewrite Nat.eqb_refl
  end : core.

Hint Extern 1 =>
  match goal with
  | [ |- context[String.eqb ?x ?x] ] => rewrite String.eqb_refl
  end : core.

(** Modified to consider objects given in obj *)
(** Try a new instantiation of a universally quantified fact, proved by [e].
   * [trace] is an accumulator recording which instantiations we choose. *)
Ltac inster' e trace obj :=
  (** Does [e] have any quantifiers left? *)
  match type of e with
    | forall x : _, _ =>
      (** Yes, so let's pick the first context variable of the right type. *)
      match goal with
        | [ H : _ |- _ ] =>
          inster' (e H) (trace, H) obj
        | _ => app ltac:(fun x => inster' (e x) (trace,x) obj) obj
        (* | _ => idtac "oh" *)
        | _ => fail 2
      end
    | _ =>
      (** No more quantifiers, so now we check if the trace we computed was already used. *)
      match trace with
        | (_, _) =>
          (** We only reach this case if the trace is nonempty, ensuring that [inster] fails if no progress can be made. *)
          match goal with
            | [ H : done (trace, _) |- _ ] =>
              (** Uh oh, found a record of this trace in the context!  Abort to backtrack to try another trace. *)
              fail 1
            | _ =>
              (** What is the type of the proof [e] now? *)
              let T := type of e in
                match type of T with
                  | Prop =>

                    (** Charlie: A small modification to eliminate duplicate proofs *)
                    match goal with
                    | [ H: e |- _ ] => fail 2
                    end;

                    (** [e] should be thought of as a proof, so let's add it to the context, and also add a new marker hypothesis recording our choice of trace. *)
                    generalize e; intro;
                      assert (done (trace, tt)) by constructor
                  | _ =>
                    (** [e] is something beside a proof.  Better make sure no element of our current trace was generated by a previous call to [inster], or we might get stuck in an infinite loop!  (We store previous [inster] terms in second positions of tuples used as arguments to [done] in hypotheses.  Proofs instantiated by [inster] merely use [tt] in such positions.) *)
                    all ltac:(fun X =>
                      match goal with
                        | [ H : done (_, X) |- _ ] => fail 1
                        | _ => idtac
                      end) trace;
                    (** Pick a new name for our new instantiation. *)
                    let i := fresh "i" in (pose (i := e);
                      assert (done (trace, i)) by constructor)
                end
          end
      end
  end.