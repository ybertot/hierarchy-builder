From Coq Require Import ssreflect ssrbool ssrfun.
From elpi.apps Require Import coercion cs.
From HB Require Import structures.

Elpi Command foo.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Declare Scope set_scope.
Delimit Scope set_scope with set.
Local Open Scope set_scope.

Axiom propext : forall (P Q : Prop), (P <-> Q) -> P = Q.
Axiom PI : forall (P : Prop) (p q : P), q = p.
Axiom dfunext : forall A (B : A -> Type) 
  (f g : forall x, B x), (forall x, f x = g x) -> f = g.
Axiom CEM : forall (P : Prop), {P} + {~ P}.
Axiom CID : forall (T : Type) (P : T -> Prop), (exists x, P x) -> {x | P x}.

Ltac done :=
  trivial; hnf; intros; solve
   [ do ![solve [trivial | apply: sym_equal; trivial]
         | discriminate | contradiction | split]
   | case not_locked_false_eq_true; assumption
   | match goal with H : ~ _ |- _ => solve [case H; trivial] end 
   | apply _ ].

Reserved Notation "[ 'set' x : T | P ]"
  (at level 0, x at level 99, only parsing).
Reserved Notation "[ 'set' x | P ]"
  (at level 0, x, P at level 99, format "[ 'set'  x  |  P ]").
Reserved Notation "[ 'set' E | x 'in' A ]" (at level 0, E, x at level 99,
  format "[ '[hv' 'set'  E '/ '  |  x  'in'  A ] ']'").
Reserved Notation "[ 'set' E | x 'in' A & y 'in' B ]"
  (at level 0, E, x at level 99,
  format "[ '[hv' 'set'  E '/ '  |  x  'in'  A  &  y  'in'  B ] ']'").
Reserved Notation "[ 'set' a ]"
  (at level 0, a at level 99, format "[ 'set'  a ]").
Reserved Notation "[ 'set' : T ]" (at level 0, format "[ 'set' :  T ]").
Reserved Notation "[ 'set' a : T ]"
  (at level 0, a at level 99, format "[ 'set'  a   :  T ]").
Reserved Notation "A `|` B" (at level 52, left associativity).
Reserved Notation "a |` A" (at level 52, left associativity).
Reserved Notation "\bigcap_ ( i 'in' P ) F"
  (at level 41, F at level 41, i, P at level 50,
           format "'[' \bigcap_ ( i  'in'  P ) '/  '  F ']'").
Reserved Notation "\bigcap_ ( i : T ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \bigcap_ ( i  :  T ) '/  '  F ']'").
Reserved Notation "\bigcap_ i F"
  (at level 41, F at level 41, i at level 0,
           format "'[' \bigcap_ i '/  '  F ']'").
Reserved Notation "A `<=` B" (at level 70, no associativity).
Reserved Notation "f @^-1` A" (at level 24).
Reserved Notation "f @` A" (at level 24).



(*********************************** Sets ************************************)

Structure set (T : Type) := MkSet {
  set_to_pred : T -> Prop
}.
Notation "[ 'set' x : T | P ]" := (@MkSet _ (fun x : T => P)) : set_scope.
Notation "[ 'set' x | P ]" := (@MkSet _ (fun x => P)) : set_scope.
Notation "[ 'set!' P ]" := (@MkSet _ P)
  (P at level 200, format "[ 'set!'  P ]") : set_scope.

HB.mixin Record mem T (X : set T) (x : T) : Prop :=
  Mem { IsMem : set_to_pred X x }.

#[short(type="memType")]
HB.structure Definition MemType T (X : set T) := {x of mem T X x}.

Notation "x \in X" := (@MemType _ X x).

Notation memP := MemType.class.

Coercion memType : set >-> Sortclass.

Check fun (T : Type) (X : set T) (x : X) => x : T.
Check fun (T : Type) (X : set T) (x : T) (xX : x \in X) => x : X.
Check fun (T : Type) (X : set T) (x : X) => (_ : x \in X).

Lemma setE T (P : T -> Prop) x : x \in [set! P] = P x.
Proof. by apply/propext; split=> // -[[]]. Qed.

(* Extentionality of sets. *)
Lemma eq_set T (X Y : set T) : X = Y <-> (forall x, (x \in X) = (x \in Y)).
Proof.
split=> [->//|]; case: X Y => [P] [Q] /= eqXY.
by congr MkSet; apply/dfunext => x; have := eqXY x; rewrite !setE.
Qed.

(* TOTHINK : there was a `rewrite eq\_set` here, which does not work anymore
  for some reason. *)
Lemma eq_setP T (X Y : set T) : X = Y <-> (forall x, (x \in X) <-> (x \in Y)).
Proof.
by apply: (iff_trans (eq_set X Y)); split=> XY x;
  [rewrite XY//|apply/propext].
Qed.
(*
Section basic_definitions.
Context {T U rT : Type}.
Implicit Types (T : Type) (A B : set T) (f : T -> rT) (g : T -> U -> rT)
  (Y : set rT).

Definition range f :=
  [set y | exists x, f x = y].
Definition range2 g :=
  [set z | exists (x : T) (y : U), g x y = z].
Definition preimage f Y : set T := [set t | f t \in Y].

Definition setT := [set _ : T | True].
Definition set0 := [set _ : T | False].
Definition set1 (t : T) := [set x : T | x = t].
Definition setU A B := [set x | x \in A \/ x \in B].

Definition bigcap T I (F : I -> set T) :=
  [set a | forall i, a \in F i].

Definition subset A B := forall (t : A), t \in B.

End basic_definitions.

Notation "[ 'set' E | x 'in' A ]" :=
  (@range A _ (fun x => E)) : set_scope.
Notation "[ 'set' E | x 'in' A & y 'in' B ]" :=
  (@range2 A B _ (fun x y => E)) : set_scope.
Notation "[ 'set' a ]" := (set1 a) : set_scope.
Notation "[ 'set' a : T ]" := [set (a : T)] : set_scope.
Notation "[ 'set' : T ]" := (@setT T) : set_scope.
Notation "A `|` B" := (setU A B) : set_scope.
Notation "a |` A" := ([set a] `|` A) : set_scope.

Notation "\bigcap_ ( i 'in' P ) F" :=
  (bigcap (fun (i : P) => F)) : set_scope.
Notation "\bigcap_ ( i : T ) F" :=
  (bigcap (fun (i : T) => F)) : set_scope.
Notation "\bigcap_ i F" := (\bigcap_(i : _) F) : set_scope.

Notation "A `<=` B" := (subset A B) : set_scope.

Notation "f @^-1` A" := (preimage f A) : set_scope.
Notation "f @` A" := (@range A _ f) (only parsing) : set_scope.

Lemma set0fun {P T : Type} : @set0 T -> P.
Proof. by case=> x; rewrite setE. Qed.

Section basic_membership.

Lemma mem_range {T rT} (f : T -> rT) (x : T) : f x \in [set f x | x in T].
Proof. by rewrite setE; exists x. Qed.

HB.instance Definition _ {T rT} (f : T -> rT) (x : T) := @mem_range T rT f x.


Timeout 1 Check fun (x : nat) => S x : [set S x | x in nat].

Lemma mem_range2 {T U rT} (f : T -> U -> rT) (x : T) (y : U) :
  f x y \in [set f x y | x in T & y in U].
Proof. by rewrite setE; exists x, y. Qed.

HB.instance Definition _ {T U rT} (f : T -> U -> rT) (x : T) (y : U) :=
  @mem_range2 T U rT f x y.

Check fun (x : nat) => x + x : [set x + y | x in nat & y in nat].

Lemma mem_setUl {T} (A B : set T) (x : A) : x \in A `|` B.
Proof. by rewrite setE; left. Qed.

#[non_forgetful_inheritance]
HB.instance Definition _ {T} (A B : set T) (x : A) := @mem_setUl T A B x.

Check fun (A : set nat) (x : A) => x : (A `|` (@set0 nat)).

Lemma mem_setUr {T} (A B : set T) (x : B) : x \in A `|` B.
Proof. by rewrite setE; right. Qed.

#[non_forgetful_inheritance]
HB.instance Definition _ {T} (A B : set T) (x : B) := @mem_setUr T A B x.

Check fun (A : set nat) (x : A) => x : ((@set0 nat) `|` A).
Check fun (A : set nat) (x : A) => x : (A `|` (@set0 nat)).

Lemma mem_bigcap {T I} (F : I -> set T) (x : T) :
  (forall i, x \in F i) -> x \in \bigcap_i F i.
Proof. by rewrite setE. Qed.

HB.instance Definition _ {T I} F x H := @mem_bigcap T I F x H.

Check fun T I (F : I -> set T) (x : T) (H : forall i, x \in F i) =>
  x : \bigcap_i F i.

Lemma mem_set1 {T} (x : T) : x \in [set x].
Proof. by exists. Qed.

HB.instance Definition _ {T} (x : T) := @mem_set1 T x.

Check fun (x : nat) => x : [set x].

End basic_membership.
 *)


(*************************** Function restriction ****************************)

Check fun (A : Type) (B : Type) (S : set A) (S' : set B) (f : A -> B)
  (h : forall (x : S), f x \in S') => (f : S -> S').
Check fun (A : Type) (B : Type) (S : set A) (S' : set B) (f : A -> B)
  (h : forall (x : S), f x \in S') (x : S) => f x : S'.



(**************************00ffc05***** Pointed Types *******************************)

HB.mixin Record isPointed (T : Type) := {
  pt : T
}.

#[short(type="pointedType")]
HB.structure Definition PointedType := {T of isPointed T}.



(**************************** Function extension *****************************)

Definition extend (A : Type) (B : A -> pointedType) (S : set A)
  (f : forall a : S, B a) : forall a : A, B a :=
  fun x =>
  match CEM (x \in S) with
  | left xs => f x
  | right _ => pt
  end.

Elpi Accumulate coercion.db lp:{{

coercion _ V T E {{ @extend (lp:A : Type) (lp:B : lp:A -> pointedType)
                            (lp:X : set lp:A) lp:V }} :-
  coq.unify-eq T
    {{ forall a : @memType lp:A lp:X,
      @PointedType.sort (lp:B (@MemType.sort lp:A lp:X a)) }}
    ok,
  coq.unify-eq E {{ forall a : lp:A, @PointedType.sort (lp:B a) }} ok.

}}.
Elpi Typecheck coercion.

Check fun (A : Type) (B : pointedType) (S : set A) (f : S -> B) => f : A -> B.
Check fun (A : Type) (B : pointedType) (S : set A) (f : S -> B) (x : A) =>
  (f : A -> B) x : B.

Definition support {A : Type} {B : A -> pointedType}
  (f : forall a : A, B a) : set A :=
  [set x | f x <> pt].

Definition supported_on {A : Type} (S : set A)
  (B : A -> pointedType)  :=
  [set f : forall a, B a | forall t : support f, t \in S].

Goal forall (A : Type) (S : set A) (B : A -> pointedType)
  (f : forall a : S, B a), f \in (supported_on S B).
Proof.
move=> A S B f; rewrite setE /= => [[a /=]]; rewrite setE /extend.
by case: (CEM _).
Qed.

(* placing x at level 0 avoids seeing parentheses                            *)
Notation "x" := (MemType.sort x) (x at level 0, at level 0, only printing).
Notation "x" := (@MemType.Pack _ _ x _)
  (x at level 0, at level 0, only printing).

