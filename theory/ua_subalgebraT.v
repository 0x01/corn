(* This is an almost verbatim copy of ua_subalgebra, but with predicates in Type
instead of Prop (and with carrier sigT instead of sig).

Hopefully one day Coq's universe polymorphism will permit a merge of sig and sigT,
at which point we may try to merge ua_subalgebra and ua_subalgebraT as well. *)

Set Automatic Introduction.

Require Import
  RelationClasses Morphisms Program
  universal_algebra ua_homomorphisms canonical_names util theory.categories abstract_algebra.
Require
  categories.algebra.

Section subalgebras.

  Context `{Algebra sign A} (P: Π s, A s → Type).

  (* We begin by describing what it means for P to be a proper closed subset: *)

  Fixpoint op_closed {o: OpType (sorts sign)}: op_type A o → Type :=
    match o with
    | ne_list.one x => P x
    | ne_list.cons x y => λ d => Π z, P _ z → op_closed (d z)
    end.

  Definition op_closed_proper:
   Π (Pproper: Π s x x', x = x' → iffT (P s x) (P s x')) o,
   Π x x', x = x' → iffT (@op_closed o x) (@op_closed o x').
  Proof with intuition.
   induction o; simpl; intros x y E.
    intuition.
   split; intros...
    apply (IHo (x z))...
    apply E...
   apply (IHo (y z))...
   symmetry.
   apply E...
  Qed.

  Class ClosedSubset: Type :=
    { subset_proper: Π s x x', x = x' → iffT (P s x) (P s x')
    ; subset_closed: Π o, op_closed (algebra_op o) }.

  (* Now suppose P is closed in this way. *)

  Context `{ClosedSubset}.

  (* Our new algebra's elements are just those for which P holds: *)

  Definition carrier s := sigT (P s). 

  Hint Unfold carrier: typeclass_instances.

  (* We can implement closed operations in the new algebra: *)

  Fixpoint close_op {d}: Π (o: op_type A d), op_closed o → op_type carrier d :=
    match d with
    | ne_list.one _ => λ o c => existT _ o (c)
    | ne_list.cons _ _ => λ o c X => close_op (o (projT1 X)) (c (projT1 X) (projT2 X))
    end.

  Global Instance impl: AlgebraOps sign carrier := λ o => close_op (algebra_op o) (subset_closed o).

  (* By showing that these ops are proper, we get our new algebra: *)
  Instance: Π d, Equiv (op_type carrier d).
   intro.
   apply op_type_equiv.
   intro.
   apply sigT_relation.
   apply e.
  Defined.

  Definition close_op_proper d (o0 o1: op_type A d)
    (P: op_closed o0) (Q: op_closed o1): o0 = o1 → close_op o0 P = close_op o1 Q.
  Proof with intuition.
   induction d; simpl in *...
   intros [x p] [y q] U.
   apply (IHd _ _ (P0 x p) (Q y q)), H2...
  Qed.

  Global Instance subalgebra: Algebra sign carrier.
  Proof. constructor. apply _. intro. apply close_op_proper, algebra_propers. Qed.

End subalgebras.
