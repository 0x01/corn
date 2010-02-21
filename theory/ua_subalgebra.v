Set Automatic Introduction.

Require Import
  RelationClasses Morphisms Program
  universal_algebra canonical_names theory.categories abstract_algebra.
Require
  categories.algebra forget_algebra.

Section subalgebras.

  Context `{Algebra sign A} (P: Π s, A s → Prop).

  (* We begin by describing what it means for P to be a proper closed subset: *)

  Fixpoint op_closed {o: OpType (sorts sign)}: op_type (sorts sign) A o → Prop :=
    match o with
    | constant x => P x
    | function x y => λ d => Π z, P _ z → op_closed (d z)
    end.

  Global Instance op_closed_proper: Π `{Π s, Proper (equiv ==> iff) (P s)} o, Proper (equiv ==> iff) (@op_closed o).
  Proof with intuition.
   induction o; simpl; intros x y E.
    rewrite E...
   split; intros.
    apply (IHo (x z))... apply E...
   apply (IHo _ (y z))... apply E...
  Qed.

  Class ClosedSubset: Prop :=
    { subset_proper:> Π s, Proper (equiv ==> iff) (P s)
    ; subset_closed: Π o, op_closed (algebra_op sign o) }.

  (* Now suppose P is closed in this way. *)

  Context `{ClosedSubset}.

  (* Our new algebra's elements are just those for which P holds: *)

  Definition carrier s := sig (P s). 

  Hint Unfold carrier: typeclass_instances.

  (* We can implement closed operations in the new algebra: *)

  Program Fixpoint close_op {d}: Π (o: op_type (sorts sign) A d), op_closed o → op_type (sorts sign) carrier d :=
    match d with
    | constant _ => λ o c => exist _ o (c)
    | function x y => λ o c X => close_op (o X) (c X (proj2_sig X))
    end.

  Global Instance impl: AlgebraOps sign carrier := λ o => close_op (algebra_op sign o) (subset_closed o).

  (* By showing that these ops are proper, we get our new algebra: *)

  Definition close_op_proper d (o0 o1: op_type (sorts sign) A d)
    (P: op_closed o0) (Q: op_closed o1): o0 = o1 → close_op o0 P = close_op o1 Q.
  Proof with intuition.
   induction d; simpl in *...
   intros [x p] [y q] U.
   apply (IHd _ _ (P0 x p) (Q y q)), H2...
  Qed.

  Global Instance subalgebra: Algebra sign carrier.
  Proof. constructor. apply _. intro. apply close_op_proper, algebra_propers, _. Qed.

  (* And we have the obvious projection morphism: *)

  Definition proj s := @proj1_sig (A s) (P s).

  Global Instance: HomoMorphism sign carrier A proj.
  Proof with try apply _.
   constructor...
    constructor...
    firstorder.
   intro.
   unfold impl, algebra_op.
   generalize (subset_closed o).
   unfold algebra_op.
   generalize (H o).
   induction (sign o); simpl; intuition.
  Qed.

  (* Which is mono because proj is injective. *)

  Instance: Injective (proj i).
  Proof. firstorder. Qed.

  Global Instance: Mono (algebra.arrow _ proj).
  Proof.
   apply forget_algebra.mono.
   apply categories.product.mono.
   intro. apply setoid.mono.
   simpl. apply _.
  Qed. (* this really should be completely automatic. *)

End subalgebras.
