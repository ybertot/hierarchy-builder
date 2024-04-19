From HB Require Import structures.
From Coq Require Import ssreflect ssrbool ssrfun Lia.
Require Import sets.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Declare Scope set_scope.
Delimit Scope set_scope with set.
Local Open Scope set_scope.

(******************************)
(* The real demo begins here. *)
(******************************)

(* State-of-the-art approach to subsets, before using our extension of HB.   *)
Class td_even :=
  Mkev {ev_val : nat; ev_val_subproof : exists n, ev_val = 2 * n}.

Coercion ev_val : td_even >-> nat.

Check fun n : td_even => n * 3.

(* By rather using the generic subset constructor [set .. | ..] defined in   *)
(* The companion file sets.v, we obtained that the projection out of the     *)
(* set, whose name we don't need to know, is also deciared as a coercion.    *)
Definition even : set nat := [set n | exists m, n = 2 * m].

(* The notion of set also comes with a notion of membership.                 *)
(* n \in even is how we write that n is even, using standard set theory      *)
(*  notation.                                                                *)
Check fun n : nat => n \in even.

(* However, even, can also be used as a type, thanks to a coercion.          *)
(* And thanks to a second coercion, any even number can be used where        *)
(* a member of the supertype (here nat) is expected.                         *)
Check fun n : even => n * 3.

(* When n is natural number, the formula saying that if x is even, its       *)
(* triple also is, this formula is well-formed.                              *)
Check fun x => x \in even -> x * 3 \in even.

(* However, with the current stored knowledge, there is no way for the       *)
(* system to guess that, if n is even, its triple also is.                   *)
Fail Check fun n : even => (n * 3 : even).

(* Still, we can prove that the triple of an even number is even.            *)
Lemma times_3_even (n : even) : n * 3 \in even.
Proof.
move: (memP n).
rewrite !setE.
move=> -[m ->].
exists (m * 3).
lia.
Qed.

(*#[global]
Hint Resolve times_3_even : typeclass_instances.
*)

Lemma times_5_even (n : even) : n * 5 \in even.
Proof.
move: (memP n).
rewrite !setE.
move=> -[m ->].
exists (m * 5).
lia.
Qed.

#[global]
Hint Resolve times_3_even : typeclass_instances.

Definition times_3_td (n : td_even) : td_even.
exists (n * 3).
move: (@ev_val_subproof n)=> [m ->].
exists (m * 3).
lia.
Defined.
Check times_3_td.

Definition td2_proof : exists n, 2 = 2 * n.
Proof. exists 1; lia. Qed.

Compute @ev_val (times_3_td (Mkev td2_proof)).

(*HB.instance Definition _ (x : even) := times_3_even x.
HB.instance Definition _ (x : even) := times_5_even x. *)

(* HB_unnamed_factory_10, sets_MemType__to__sets_mem, HB_unnamed_mixin_12, 
   Nat_mul__canonicall_sets_MemType. *)

(* We shall use the function half as a way to detect when a value can
  be cast as an even number. *)
Definition half (n : even) : nat := Nat.div2 n.

(* Here something clever happens.  half expects an even argument.
  (n * 3) is by default a value of type nat, as a result of the multiplication
  function.
  But multiplication expects a natural argument, while n is an even number.
  So to satisfy the requirements of multiplication the evenness of n is
  temporarily "forgotten" while constructing the multiplication.

  Now, n * 3 is a natural number but an even number is expected.  What happens
  here is there is a coercion from nat to even, which relies on the constructor
  of an element of the subset (it is call MemType.Pack), but for this coercion
  to be inserted an extra proo of the element being satisfying the membership
  property has to be produced, and type-class resolution does it using the
  hint we provided, times_3_even. 
*)

Check fun n : even => half (n * 3).

Fail Check fun n : even => half ((((n * 3) * 3) * 3) * 3).

Fail Check fun n : even => half ((((n * 3) * 3) * 5) * 3).

Fail Check fun n : even => half (n * (3 * 3)).

(* A few oddities: if a named argument is provided stating that the property *)
(* of membership is satisfied, the type can be used.                         *)
Check fun (x : nat) (h : x \in even) => (x : even).
Check fun (x : nat) (_ : x \in even) => (x : even).

(* When used in a logical expression, it feels odd that the hypothesis needs *)
(* to be named for the reconstruction to the subset type to succeed.         *)
Fail Check forall (P : even -> Prop) (x : nat), x \in even -> P x.
Fail Check forall (P : even -> Prop) (x : nat) (_ : x \in even), P x.
Check forall (* (P : even -> Prop) *) (x : nat) (h : x \in even), x = x :> even.
