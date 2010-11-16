Set Automatic Introduction.

Require Import
  Ring Program Morphisms
  abstract_algebra canonical_names.
Require
 theory.setoids varieties.monoid.

(* * Ring Minus *)
Section ring_minus_properties.
  Context `{Ring R} `{minus : !RingMinus R}.

  Lemma ring_minus_correct x y : x - y = x + -y.
  Proof.
    unfold ring_minus. unfold ring_minus_sig. 
    destruct minus as [z E]. simpl. auto.
  Qed.

  Global Instance: Proper ((=) ==> (=) ==> (=)) ring_minus.
  Proof.
    intros x1 y1 E1 x2 y2 E2.
    rewrite (ring_minus_correct x1 x2). rewrite ring_minus_correct.
    rewrite E1, E2. reflexivity.
  Qed.
End ring_minus_properties.

Program Instance default_ring_minus `{Ring R}: RingMinus R | 10 := λ x y, x + -y.
Next Obligation. reflexivity. Qed.

Section group_props. Context `{Group}.

  Lemma inv_involutive x: - - x = x.
  Proof.
   rewrite <- (monoid_left_id _ x) at 2.
   rewrite <- (ginv_l (- x)).
   rewrite <- associativity.
   rewrite ginv_l.
   rewrite right_identity.
   reflexivity.
  Qed.

  Global Instance: Injective group_inv.
  Proof.
   constructor.
    intros x y E.
    rewrite <- (inv_involutive x), <- (inv_involutive y), E. reflexivity.
   constructor; apply _.
  Qed.

  Lemma inv_zero: - mon_unit = mon_unit.
  Proof. rewrite <- (ginv_l mon_unit) at 2. rewrite right_identity. reflexivity. Qed.

End group_props.

Lemma sg_inv_distr `{AbGroup} x y: - (x & y) = - x & - y.
Proof.
 rewrite <- (left_identity (- x & - y)).
 rewrite <- (ginv_l (x & y)).
 rewrite <- associativity.
 rewrite <- associativity.
 rewrite (commutativity (- x) (- y)).
 rewrite (associativity y).
 rewrite ginv_r.
 rewrite left_identity.
 rewrite ginv_r.
 rewrite right_identity.
 reflexivity.
Qed.

Lemma stdlib_semiring_theory R `{SemiRing R} : Ring_theory.semi_ring_theory 0 1 ring_plus ring_mult equiv.
Proof with try reflexivity.
  constructor; intros.
         apply left_identity.
        apply commutativity.
       apply associativity.
      apply left_identity.
     apply left_absorb.
    apply commutativity.
   apply associativity.
  apply distribute_r.
Qed.

Section semiring_props.
  Context `{SemiRing R}.

  Global Instance plus_0_r: RightIdentity ring_plus 0 := right_identity.
  Global Instance plus_0_l: LeftIdentity ring_plus 0 := left_identity.
  Global Instance mult_1_l: LeftIdentity ring_mult 1 := left_identity.
  Global Instance mult_1_r: RightIdentity ring_mult 1 := right_identity.

  Global Instance mult_0_r: RightAbsorb ring_mult 0.
  Proof. intro. rewrite commutativity. apply left_absorb. Qed.

  Global Instance: Monoid_Morphism (r *).
  Proof.
   repeat (constructor; try apply _).
    apply distribute_l.
   apply right_absorb.
  Qed.

  Context {Rel} {proper : Proper ((=) ==> (=) ==> iff) Rel}.
  Timeout 3 Global Instance ring_plus_left_cancel_right `{!LeftCancellation Rel (λ x, True) (+) } : RightCancellation Rel (λ x, True) (+).
  Proof.
    intros z _ x y E.
    apply (left_cancellation (+) z). auto.
    rewrite (commutativity z x), (commutativity z y). assumption.
  Qed.

  Global Instance ring_mult_left_cancel_right `{!LeftCancellation Rel (λ x, x ≠ 0) ring_mult } : 
    RightCancellation Rel (λ x, x ≠ 0) ring_mult.
  Proof.
    intros z z_nonzero x y E. 
    apply (left_cancellation ring_mult z). assumption.
    rewrite (commutativity z x), (commutativity z y). assumption.
  Qed.

End semiring_props.

Section semiringmor_props. Context `{SemiRing_Morphism}.

  Lemma preserves_0: f 0 = 0.
  Proof. intros. apply (@preserves_mon_unit _ _ _ _ _ _ _ _ f _). Qed.
  Lemma preserves_1: f 1 = 1.
  Proof. intros. apply (@preserves_mon_unit _ _ _ _ _ _ _ _ f _). Qed.
  Lemma preserves_mult: ∀ x y, f (x * y) = f x * f y.
  Proof. intros. apply preserves_sg_op. Qed.
  Lemma preserves_plus: ∀ x y, f (x + y) = f x + f y.
  Proof. intros. apply preserves_sg_op. Qed.

End semiringmor_props.

Lemma stdlib_ring_theory R `{Ring R} `{minus : !RingMinus R} : 
  Ring_theory.ring_theory 0 1 ring_plus ring_mult (@ring_minus _ _ _ _ minus) group_inv equiv.
Proof.
 constructor; intros.
         apply left_identity.
        apply commutativity.
       apply associativity.
      apply left_identity.
     apply commutativity.
    apply associativity.
   apply distribute_r.
  rewrite ring_minus_correct. reflexivity.
 apply (ginv_r x).
Qed.

Section ring_props. 
  Context `{Ring R}.

  Add Ring R: (stdlib_ring_theory R).

  Instance: LeftAbsorb ring_mult 0.
  Proof. intro. ring. Qed.

  Global Instance Ring_Semi: SemiRing R.
  Proof. repeat (constructor; try apply _). Qed.

  (* Hm, are the following really worth having as lemmas? *)

  Lemma plus_opp_r x: x + -x = 0. Proof. ring. Qed.
  Lemma plus_opp_l x: -x + x = 0. Proof. ring. Qed.
  Lemma plus_mul_distribute_r x y z: (x + y) * z = x * z + y * z. Proof. ring. Qed.
  Lemma plus_mul_distribute_l x y z: x * (y + z) = x * y + x * z. Proof. ring. Qed.
  Lemma opp_swap x y: x + - y = - (y + - x). Proof. ring. Qed.
  Lemma plus_opp_distr x y: - (x + y) = - x + - y. Proof. ring. Qed.
  Lemma ring_opp_mult a: -a = -(1) * a. Proof. ring. Qed.
  Lemma ring_distr_opp_mult a b: -(a * b) = -a * b. Proof. ring. Qed.
  Lemma ring_opp_mult_opp a b: -a * -b = a * b. Proof. ring. Qed.
  Lemma opp_0: -0 = 0. Proof. ring. Qed.
  Lemma ring_distr_opp a b: -(a+b) = -a+-b. Proof. ring. Qed.

  Lemma equal_by_zero_sum x y: x + - y = 0 → x = y.
  Proof. intro E. rewrite <- (plus_0_l y). rewrite <- E. ring. Qed.

  Global Instance: LeftCancellation (=) (λ x, True) (+).
  Proof.
   intros z _ x y E.
   rewrite <- plus_0_l.
   rewrite <- (plus_opp_l z).
   rewrite <- associativity.
   rewrite E.
   ring.
  Qed.

  Lemma units_dont_divide_zero (x: R) `{!RingMultInverse x} `{!RingUnit x}: ¬ ZeroDivisor x.
    (* todo: we don't want to have to mention RingMultInverse *)
  Proof with try ring.
   intros [x_nonzero [z [z_nonzero xz_zero]]].
   apply z_nonzero.
   transitivity (1 * z)...
   rewrite <- ring_unit_mult_inverse.
   transitivity (x * z * ring_mult_inverse x)...
   rewrite xz_zero...
  Qed.

  Lemma mult_ne_zero `{!NoZeroDivisors R}: ∀ (x y: R), x ≠ 0 → y ≠ 0 → x * y ≠ 0.
  Proof. repeat intro. apply (no_zero_divisors x). split; eauto. Qed.

  Global Instance ring_mult_left_cancel `{!NoZeroDivisors R} `{∀ x y, Stable (x = y)} :
    LeftCancellation (=) (λ x, x ≠ 0) ring_mult.
  Proof with intuition.
   intros z z_nonzero x y E.
   apply stable.
   intro U.
   apply (mult_ne_zero z (x +- y) z_nonzero).
    intro. apply U. apply equal_by_zero_sum...
   rewrite distribute_l, E. ring.
  Qed.

End ring_props.

Section ringmor_props. 
  Context `{Ring_Morphism A B f}.

  Lemma preserves_opp x: f (- x) = - f x.
  Proof. intros. apply preserves_inv. Qed.

  Global Instance Ring_Semi_Morphism: SemiRing_Morphism f.
  Proof. destruct H. constructor; apply _. Qed.

End ringmor_props.

Section from_stdlib_ring_theory.
  Context
    `{H: @ring_theory R zero one pl mu mi op e}
    `{!@Setoid R e}
    `{!Proper (e ==> e ==> e) pl}
    `{!Proper (e ==> e ==> e) mu}
    `{!Proper (e ==> e) op}.

  Add Ring R2: H.

  Definition from_stdlib_ring_theory: @Ring R e pl mu zero one op.
  Proof.
   repeat (constructor; try assumption); repeat intro
   ; unfold equiv, mon_unit, sg_op, group_inv; ring.
  Qed.

End from_stdlib_ring_theory.

Section morphism_composition.

  Context (A B C: Type)
    `{!RingMult A} `{!RingPlus A} `{!RingOne A} `{!RingZero A} `{!Equiv A}
    `{!RingMult B} `{!RingPlus B} `{!RingOne B} `{!RingZero B} `{!Equiv B}
    `{!RingMult C} `{!RingPlus C} `{!RingOne C} `{!RingZero C} `{!Equiv C}
    (f: A → B) (g: B → C).

  Global Instance id_semiring_morphism `{!SemiRing A}: SemiRing_Morphism id.

  Global Instance compose_semiring_morphisms
    `{!SemiRing_Morphism f} `{!SemiRing_Morphism g}: SemiRing_Morphism (g ∘ f).
  Proof.
   fold (g ∘ f).
   constructor; try apply _.
    apply semiringmor_a.
   apply semiringmor_b.
  Qed.

  Context `{!GroupInv A} `{!GroupInv B} `{!GroupInv C}.

  Global Instance id_ring_morphism `{!Ring A}: Ring_Morphism id.
  Proof. repeat (constructor; try apply _); reflexivity. Qed.

  Global Instance compose_ring_morphisms
    `{!Ring_Morphism f} `{!Ring_Morphism g}: Ring_Morphism (g ∘ f).
  Proof.
   pose proof (ringmor_a f).
   pose proof (ringmor_b f).
   pose proof (ringmor_b g).
   repeat (constructor; try apply _); intros.
   unfold compose.
   do 2 rewrite preserves_opp. reflexivity.
  Qed.

End morphism_composition.
