Require
  theory.naturals theory.integers orders.orders.
Require Import 
  Program Morphisms Setoid Ring
  abstract_algebra interfaces.additional_operations.

(* * Properties of Cut off Minus *)
Section cut_minus_properties.
  Context `{SemiRing R} `{cm : !CutMinus R}.

  Context `{∀ (x y : R), Decision (x ≤ y)} 
    `{∀ (x y : R), Decision (x = y)} 
    `{!TotalOrder (≤)} 
    `{!LeftCancellation (=) (λ x, True) (+)}.

  Add Ring SR: (rings.stdlib_semiring_theory R).

  Global Instance cut_minus_proper: Proper ((=) ==> (=) ==> (=)) cut_minus.
  Proof with auto; try reflexivity.
    intros x1 x2 E y1 y2 F.
    unfold cut_minus, cut_minus_sig. 
    destruct cm as [z1 [Ez1 Fz1]]. destruct cm as [z2 [Ez2 Fz2]]. simpl.
    rewrite E, F in Ez1, Fz1. clear E F x1 y1.
    destruct (orders.precedes_or_precedes_neq x2 y2).
    rewrite Fz1, Fz2...
    apply (right_cancellation (+) y2)...
    rewrite Ez1, Ez2...
  Qed.

  Lemma cut_minus_precedes_neq x y : y < x → (x ∸y) + y = x.
  Proof.
    unfold cut_minus, cut_minus_sig. destruct cm. simpl. tauto.
  Qed.

  Lemma cut_minus_0 x y : x ≤ y → (x ∸y) = 0.
  Proof.
    unfold cut_minus, cut_minus_sig. destruct cm. simpl. tauto.
  Qed.

  Lemma cut_minus_precedes x y : y ≤ x → (x ∸y) + y = x.
  Proof.
    intros E. destruct ((proj2 (orders.precedes_neq_precedes y x)) E) as [F|].
    rewrite F, cut_minus_0. ring. reflexivity.
    apply cut_minus_precedes_neq. assumption.
  Qed.  

  Lemma cut_minus_diag x : x ∸ x = 0.
  Proof.
    apply cut_minus_0. reflexivity.
  Qed.

  Lemma cut_minus_rightidentity x : 0 ≤ x → x ∸ 0 = x.
  Proof.
    intros E.
    rewrite <-(rings.plus_0_r (x ∸ 0)).
    apply cut_minus_precedes. assumption.
  Qed.

  Lemma cut_minus_leftabsorb x : 0 ≤ x → 0 ∸ x = 0.
  Proof.
    intros E.
    apply cut_minus_0. assumption.
  Qed.

  Lemma cut_minus_rightabsorb x : x ≤ 0 → x ∸ 0 = 0.
  Proof.
    intros E.
    apply cut_minus_0. assumption.
  Qed.

  Lemma cut_minus_positive x y : 0 ≤ x ∸ y.
  Proof with auto.
    destruct (total_order x y) as [E|E].
    apply orders.equiv_precedes. symmetry. apply cut_minus_0...
    apply (right_cancellation (+) y)...
    rewrite cut_minus_precedes; ring_simplify...
  Qed.

  Lemma cut_minus_precedes_trans x y z : y ≤ x → z ≤ y → (x ∸ y) + (y ∸ z) = x ∸ z.
  Proof with auto; try reflexivity. 
    intros. 
    apply (right_cancellation (+) z)...
    rewrite <-associativity. 
    repeat rewrite cut_minus_precedes... 
    transitivity y...
  Qed.

  Lemma cut_minus_plus_distr x1 x2 y1 y2 : y1 ≤ x1 → y2 ≤ x2 
     → (x1 ∸ y1) + (x2 ∸ y2) = (x1 + x2) ∸ (y1 + y2).
  Proof with auto.
    intros E F.
    apply (right_cancellation (+) (y1 + y2))...
    rewrite cut_minus_precedes.
    setoid_replace (x1 ∸ y1 + (x2 ∸ y2) + (y1 + y2)) with (((x1 ∸ y1) + y1) + ((x2 ∸ y2) + y2)) by ring.
    repeat rewrite cut_minus_precedes... reflexivity. 
    apply semiring.sr_precedes_plus_compat...
  Qed.

  Lemma cut_minus_plus_l_rev x y z : y ∸ z = (x + y) ∸ (x + z).
  Proof with auto; try reflexivity.
    destruct (total_order y z) as [E|E].
    repeat rewrite cut_minus_0... 
    apply semiring.sr_precedes_plus_compat_l...
    apply (right_cancellation (+) (x + z))...
    setoid_replace (y ∸ z + (x + z)) with ((y ∸ z + z) + x) by ring.
    repeat rewrite cut_minus_precedes... apply commutativity.
    apply semiring.sr_precedes_plus_compat_l...
  Qed.

  Lemma cut_minus_plus_r_rev x y z : y ∸ z = (y + x) ∸ (z + x).
  Proof with auto; try reflexivity.
    rewrite (commutativity y x), (commutativity z x).
    apply cut_minus_plus_l_rev.
  Qed.

  (* The following lemmas are quite ad hoc... Distill some useful, possibly smaller, lemmas from it and clean it up somehow *)
  Lemma cut_minus_plus_toggle1 x y z : x ≤ y → z ≤ y → (y ∸ x) + (x ∸ z) = (y ∸ z) + (z ∸ x).
  Proof with auto.
    intros. destruct (total_order x z).
    rewrite (cut_minus_0 x z), cut_minus_precedes_trans... ring.
    rewrite (cut_minus_0 z x), cut_minus_precedes_trans... ring.
  Qed.

  Lemma cut_minus_plus_toggle2 x y z : y ≤ x → y ≤ z →  (x ∸ z) + (z ∸ y) = (z ∸ x) + (x ∸ y).
  Proof with auto.
    intros. destruct (total_order x z).
    rewrite (cut_minus_0 x z), cut_minus_precedes_trans... ring.
    rewrite (cut_minus_0 z x)... ring_simplify. apply cut_minus_precedes_trans...
  Qed.

  Lemma cut_minus_plus_toggle3 x1 x2 y1 y2 : x1 ≤ y1 → y2 ≤ x2 
     → (y1 ∸ x1) + ((x1 + x2) ∸ (y1 + y2)) = (x2 ∸ y2) + ((y1 + y2) ∸ (x1 + x2)).
  Proof with auto.
    intros E F.
    apply (right_cancellation (+) (x1 + y2))...
    setoid_replace (y1 ∸ x1 + (x1 + x2 ∸ (y1 + y2)) + (x1 + y2))
       with ((y1 ∸ x1) + x1 + (x1 + x2 ∸ (y1 + y2)) + y2) by ring.
    rewrite cut_minus_precedes...
    setoid_replace (x2 ∸ y2 + (y1 + y2 ∸ (x1 + x2)) + (x1 + y2))
       with ((x2 ∸ y2) + y2 + (y1 + y2 ∸ (x1 + x2)) + x1) by ring.
    rewrite cut_minus_precedes...
    destruct (total_order (x1 + x2) (y1 + y2)).
    rewrite (cut_minus_0 (x1 + x2) (y1 + y2))...
    setoid_replace (x2 + (y1 + y2 ∸ (x1 + x2)) + x1) with 
      ((y1 + y2 ∸ (x1 + x2)) + (x1 + x2)) by ring.
    rewrite cut_minus_precedes... ring.
    rewrite (cut_minus_0 (y1 + y2) (x1 + x2))...
    setoid_replace (y1 + (x1 + x2 ∸ (y1 + y2)) + y2) with 
      ((x1 + x2 ∸ (y1 + y2)) + (y1 + y2)) by ring.
    rewrite cut_minus_precedes... ring.
  Qed.

  Lemma cut_minus_zeros_precedes x y : x ≤ y → (y ∸ x) + (x ∸ 0) + (0 ∸ y) = (y ∸ 0) + (0 ∸ x).
  Proof with auto; try reflexivity.
    intros E.
    destruct (total_order 0 x) as [F|F]; destruct (total_order 0 y) as [G|G].
    repeat (rewrite cut_minus_rightidentity by auto).
      repeat (rewrite cut_minus_leftabsorb by auto).
      rewrite cut_minus_precedes...
    rewrite (cut_minus_rightidentity x)... rewrite (cut_minus_leftabsorb x)...
     rewrite (cut_minus_rightabsorb y)...
     rewrite cut_minus_precedes...
     rewrite commutativity. rewrite cut_minus_precedes... ring.
   rewrite (cut_minus_rightidentity y)... rewrite (cut_minus_rightabsorb x)...
   rewrite (cut_minus_leftabsorb y)...
   ring_simplify. apply (right_cancellation (+) x)...
    rewrite <-associativity.
    repeat rewrite cut_minus_precedes... ring.
   rewrite (cut_minus_rightabsorb x)...
     rewrite (cut_minus_rightabsorb y)... ring_simplify. rewrite commutativity.
     apply cut_minus_precedes_trans...
  Qed.

  (* The relation to ring minus *)
  Context `{GroupInv R} `{!Ring R} `{!RingMinus R}.
  Add Ring R: (rings.stdlib_ring_theory R).

  Lemma cut_minus_ring_minus (x y : R) : y ≤ x → x ∸ y = x - y.
  Proof with auto.
    intros E.
    apply (right_cancellation (+) y)... ring_simplify.
    apply cut_minus_precedes...
  Qed.

  Lemma cut_minus_ring_inv (x : R) : x ≤ 0 → 0 ∸ x = -x.
  Proof with auto.
    intros E. rewrite <-(rings.plus_0_l (-x)). 
    rewrite cut_minus_ring_minus... ring.
  Qed.

End cut_minus_properties.

(* * Default implementation for Rings *)
Section cut_minus_default.
  Context `{Ring R} 
    `{!AntiSymmetric (≤)}
    `{prec_dec : ∀ (x y : R), Decision (x ≤ y)} 
    `{!RingMinus R}.

  Add Ring R2: (rings.stdlib_ring_theory R).

  Global Program Instance default_cut_minus: CutMinus R | 10 := λ x y, exist _ ( 
    if decide(x ≤ y) then 0 else x - y
  ) _.
  Next Obligation with auto.
    case (decide (x ≤ y)); intros E; split; intros F...
    ring_simplify. apply (antisymmetry (≤))...
      apply orders.precedes_neq_weaken...
    reflexivity.
    ring.
    contradiction.
  Qed.

End cut_minus_default.
   