From HB Require Import structures.

HB.mixin Record M A := { x: nat }.
HB.structure Definition S := { X of M X}.

HB.factory Record f A := { y : nat }.
HB.builders Context T of f T.
HB.instance Definition _ := M.Build T (y + 1).
HB.end.

Search "HB_unnamed".
(* This shows:
  Builders_5.HB_unnamed_factory_7
HB_unnamed_factory_2 *)

#[hnf] HB.instance Definition _ := f.Build nat (3 + 2).
Search "HB_unnamed".
(* This shows:
  HB_unnamed_factory_9
  HB_unnamed_mixin_11
*)
Search "Datatypes_nat".
Print Datatypes_nat__canonical__hnf_S.
Print HB_unnamed_mixin_11.

HB.instance Definition _ := f.Build bool (3 + 2).
Print Datatypes_bool__canonical__hnf_S.
Search "HB_unnamed_mixin".
(* There is no other unnamed mixin here apart from mixin_11 *)
(* Print HB_unnamed_mixin_16. *)

