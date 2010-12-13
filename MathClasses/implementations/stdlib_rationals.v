Require
  signed_binary_positive_integers Field QArith.Qfield theory.fields.
Require Import
  Ring Morphisms QArith_base
  abstract_algebra theory.rings interfaces.rationals canonical_names
  theory.rationals.

(* canonical names for relations/operations/constants: *)
Instance Q_eq: Equiv Q := Qeq.
Instance Q_0 : RingZero Q := 0%Q.
Instance Q_1 : RingOne Q := 1%Q.
Instance Q_inv : GroupInv Q := Qopp.
Instance Q_plus : RingPlus Q := Qplus.
Instance Q_mult : RingMult Q := Qmult.
Program Instance Q_mult_inv : MultInv Q := Qinv.

(* properties: *)

Instance: Setoid Q.

Instance: Field Q.
Proof fields.from_stdlib_field_theory Qfield.Qsft.

(* order: *)
(*
Instance: Transitive Qle := Qle_trans.
Instance: Reflexive Qle := Qle_refl.
Instance Qle_PreOrder: PreOrder Qle.
Instance: AntiSymmetric Qle := Qle_antisym.
Instance: PartialOrder Qle.
Instance: Order Q := Qle.

Instance: RingOrder q_equiv Qplus Qmult 0%Q Qle.
Proof with auto.
 constructor; try apply _; intros.
  apply Qplus_le_compat...
  reflexivity.
 apply Qmult_le_0_compat...
Qed.

Instance: OrdField Q.
*)
(* misc: *)
Instance: ∀ x y: Q, Decision (x = y) := Qeq_dec.

Instance: Proper ((=) ==> (=)) inject_Z. 
Proof. intros x y H. rewrite H. reflexivity. Qed.

Instance: Ring_Morphism inject_Z. 
Proof.
  repeat (split; try apply _).
  intros x y. repeat red. simpl. repeat rewrite Zmult_1_r. reflexivity.
Qed.

Instance: Injective inject_Z.
Proof.
 constructor. 2: apply _.
 intros x y. change (x * 1 = y * 1 → x = y). do 2 rewrite mult_1_r. intuition.
Qed.

Let inject p := inject_Z (fst p) * / inject_Z (snd p).

Instance: Setoid_Morphism inject.
Proof.
 constructor; try apply _.
 intros ?? E. unfold inject. rewrite E. reflexivity.
Qed.

Instance: Inverse inject := λ x, (Qnum x, Zpos (Qden x)).

Instance: Surjective (λ p, inject_Z (fst p) * / inject_Z (snd p)).
Proof.
 constructor. 2: apply _.
 intros [num den] q E. rewrite <- E. unfold Basics.compose, id.
 simpl. rewrite Qmake_Qdiv. reflexivity.
Qed.

Instance Qrat: Rationals Q.
Proof alt_Build_Rationals _ _ inject_Z _ _.

(* Relation to dec_mult_inv *)
Program Instance Qinv_dec_mult: DecMultInv Q := Qinv.
Next Obligation.
  split; intros E. 
   apply Qmult_inv_r; trivial.
  rewrite E. reflexivity.
Qed.
