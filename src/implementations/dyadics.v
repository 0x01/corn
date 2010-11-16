(** 
  The dyadic rationals are numbers of the shape [m * 2 ^ e] with [m : Z] and [e : Z] 
   for some [Integers] implementation [Z]. These numbers form a ring and can be 
   embedded into any [Rationals] implementation [Q]. 
*)

Require
  theory.integers theory.rings theory.fields.
Require Import
  Morphisms Ring Program RelationClasses Setoid
  abstract_algebra 
  interfaces.integers interfaces.naturals interfaces.rationals
  interfaces.additional_operations 
  theory.cut_minus theory.bit_shift
  positive_integers_naturals.

Record Dyadic Z := dyadic { mant: Z; expo: Z }.
Implicit Arguments dyadic [[Z]].
Implicit Arguments mant [[Z]].
Implicit Arguments expo [[Z]].

Infix "#" := dyadic (at level 80).
Instance: Params (@dyadic) 2.

Section dyadics.
  Context `{Integers Z}.
  Add Ring Z: (rings.stdlib_ring_theory Z).

  Context `{equiv_dec : ∀ (x y : Z), Decision (x = y)}  
    `{precedes_dec : ∀ (x y : Z), Decision (x ≤ y)}
    `{!NatPow Z (Pos Z)} 
    `{!ShiftLeft Z (Pos Z)}
    `{!RingMinus Z}.

  Let Dyadic := Dyadic Z.

  Instance: Proper ((=) ==> (=) ==> (=)) (∸). Proof. apply _. Qed.

  Hint Resolve (@orders.precedes_flip Z _ _).

  (* Dirty hack to avoid having sigma times all over *)
  Program Let cut_minus_ZPos (x y : Z) : Pos Z := exist _ (x ∸ y) _.
  Next Obligation. apply cut_minus_positive. Qed.
  Infix "--" := cut_minus_ZPos (at level 50, left associativity).

  Ltac unfold_cut_minus := unfold equiv, ZPos_equiv, cut_minus_ZPos; simpl.

  Instance: Proper ((=) ==> (=) ==> (=)) cut_minus_ZPos.
  Proof. intros x1 x2 E y1 y2 F. unfold_cut_minus. apply cut_minus_proper; auto. Qed.

  Lemma shiftl_cut_minus_0 {x y n} : x ≤ y → n ≪ (x -- y) = n.
  Proof. 
    intros. assert (x -- y = 0) as E. unfold_cut_minus. apply cut_minus_0. assumption.
    rewrite E. apply right_identity.
  Qed.

  (** * Equality *)
  Global Instance dy_eq: Equiv Dyadic := λ x y,
    mant x ≪ (expo x -- expo y) = mant y ≪ (expo y -- expo x).

  Instance: Reflexive dy_eq.
  Proof.
    intro. unfold equiv, dy_eq. reflexivity.
  Qed.

  Instance: Symmetric dy_eq.
  Proof.
    intros x y E. unfold equiv, dy_eq in *.
    rewrite E. reflexivity.
  Qed.

  Instance: Transitive dy_eq.
  Proof with eauto; try reflexivity.
    intros x y z E1 E2. unfold equiv, dy_eq in *.
    destruct (total_order (expo x) (expo y)) as [F|F];
      rewrite (shiftl_cut_minus_0 F) in E1; 
      destruct (total_order (expo y) (expo z)) as [G|G];
      rewrite (shiftl_cut_minus_0 G) in E2... 
    (* expo x ≤ expo y, expo y ≤ expo z *)
    rewrite E1, E2. repeat rewrite <-shiftl_sum_exp. 
    apply shiftl_proper... unfold_cut_minus. 
    rewrite (cut_minus_0 (expo x)). ring_simplify. 
    apply cut_minus_precedes_trans... transitivity (expo y)...
    (* expo x ≤ expo y, expo y ≤ expo z *)
    rewrite E1, <-E2. repeat rewrite <-shiftl_sum_exp. 
    apply shiftl_proper... unfold_cut_minus. 
    apply cut_minus_plus_toggle1...
    (* expo y ≤ expo x, expo y ≤ expo z *)
    apply (shiftl_inj (expo x -- expo y))... unfold flip.
    rewrite shiftl_order, E1, E2. repeat rewrite <-shiftl_sum_exp. 
    apply shiftl_proper... unfold_cut_minus. 
    rewrite commutativity. apply cut_minus_plus_toggle2...
    (* expo y ≤ expo x, expo z ≤ expo y *)
    rewrite <-E2, <-E1. repeat rewrite <-shiftl_sum_exp.
    apply shiftl_proper... unfold_cut_minus. 
    rewrite (cut_minus_0 (expo z)). ring_simplify. 
    symmetry. apply cut_minus_precedes_trans... transitivity (expo y)...
  Qed.  
  
  Instance: Equivalence dy_eq.
  Instance: Setoid Dyadic.

  (* Equalitity is decidable *)
  Lemma dy_eq_dec_aux (x y : Dyadic) p : 
    mant x = mant y ≪ exist _ (expo y - expo x) p ↔ x = y.
  Proof with auto.
    pose proof (proj1 (semiring.sr_precedes_0_minus _  _) p).
    split; intros E. 
    (* → *)
    unfold equiv, dy_eq.
    rewrite E, <-shiftl_sum_exp.
    apply shiftl_proper. reflexivity.
    unfold_cut_minus.
    rewrite cut_minus_0, cut_minus_ring_minus...
    ring.
    (* ← *)
    unfold equiv, dy_eq in E.
    apply (shiftl_inj (expo x -- expo y)). unfold flip.
    rewrite E, <-shiftl_sum_exp.
    apply shiftl_proper. reflexivity.
    unfold_cut_minus.
    rewrite (cut_minus_0 (expo x) (expo y)), (cut_minus_ring_minus (expo y) (expo x))...
    ring.
  Qed.

   Lemma dy_eq_dec_aux_neg (x y : Dyadic) p : 
     mant x ≠ mant y ≪ exist _ (expo y - expo x) p ↔ x ≠ y.
   Proof. split; intros E; intro; apply E; eapply dy_eq_dec_aux; eassumption. Qed.

  Global Program Instance dy_eq_dec : ∀ (x y: Dyadic), Decision (x = y) := λ x y,
     if decide (expo x ≤ expo y) 
     then if decide (mant x = mant y ≪ exist _ (expo y - expo x) _) then left _ else right _ 
     else if decide (mant x ≪ exist _ (expo x - expo y) _ = mant y) then left _ else right _.
  Next Obligation. eapply semiring.sr_precedes_0_minus. assumption. Qed.
  Next Obligation. eapply dy_eq_dec_aux; eauto. Qed.
  Next Obligation. eapply dy_eq_dec_aux_neg; eauto. Qed.
  Next Obligation. apply semiring.sr_precedes_0_minus. auto. Qed.
  Next Obligation. symmetry. eapply dy_eq_dec_aux. symmetry. eassumption. Qed.
  Next Obligation. apply not_symmetry. eapply dy_eq_dec_aux_neg. apply not_symmetry. eassumption. Qed.

  Instance dyadic_proper: Proper ((=) ==> (=) ==> (=)) dyadic.
  Proof.
    intros x1 y1 E1 x2 y2 E2.
    unfold equiv, dy_eq. simpl.
    rewrite E1, E2. reflexivity.
  Qed.

  (* Ad hoc min function, it would be nicer to formalize some lattice theory *)
  Definition min (x y : Z) := if (decide (x ≤ y)) then x else y.
  
  Instance: Commutative min.
  Proof with auto; try reflexivity.
    intros x y. unfold min. 
    case (decide (x ≤ y)); case (decide (y ≤ x)); intros; apply (antisymmetry (≤))...
  Qed.

  Instance: Associative min.
  Proof with auto; try reflexivity; try contradiction.
     intros x y z. unfold min.
     case (decide (y ≤ z)); intros E1; case (decide (x ≤ y)); intros E2; 
       case (decide (x ≤ z)); intros E3; case (decide (y ≤ z)); intros E4...
     destruct E3. transitivity y...
     destruct E4. transitivity x...
  Qed.
  
  Lemma sr_precedes_min_l (x y : Z) : x ≤ y → min x y = x.
  Proof with auto.
    intros E. unfold min.
    case (decide (x ≤ y)). reflexivity. contradiction.
  Qed.
  
  Lemma sr_precedes_min_r (x y : Z) : y ≤ x → min x y = y.
  Proof with auto.
    intros E. rewrite commutativity. apply sr_precedes_min_l...
  Qed.

  (** * Basic operations *)
  Global Program Instance dy_plus: RingPlus Dyadic := λ x y, 
    if decide (expo x ≤ expo y)
    then mant x + (mant y ≪ exist _ (expo y - expo x) _) # min (expo x) (expo y)
    else (mant x ≪ exist _ (expo x - expo y) _) + mant y # min (expo x) (expo y).
  Next Obligation. apply semiring.sr_precedes_0_minus. assumption. Qed.
  Next Obligation. apply semiring.sr_precedes_0_minus. auto. Qed.

  (* The following plus function is less efficient, because it involves computing [decide (expo x ≤ expo y)] twice.
    Yet, it is much more convinient to reason with. *)
  Definition dy_plus_alt (x y : Dyadic) : Dyadic := 
    mant x ≪ (expo x -- expo y) + mant y ≪ (expo y -- expo x) # min (expo x) (expo y).
  
  Lemma dy_plus_alt_correct x y : dy_plus x y = dy_plus_alt x y.
  Proof with auto; try reflexivity.
    unfold dy_plus, dy_plus_alt.
    case (decide (expo x ≤ expo y)); intros E; 
      apply dyadic_proper;
      try apply sg_mor;
      try apply shiftl_proper...
    symmetry. apply shiftl_cut_minus_0...
    unfold_cut_minus. rewrite cut_minus_ring_minus...
    unfold_cut_minus. rewrite cut_minus_ring_minus... 
    symmetry. apply shiftl_cut_minus_0...
  Qed.

  Global Instance dy_opp: GroupInv Dyadic := λ x, -mant x # expo x.

  Global Instance dy_mult: RingMult Dyadic := λ x y, mant x * mant y # expo x + expo y.

  Global Instance dy_0: RingZero Dyadic := 0 # 0.
  Global Instance dy_1: RingOne Dyadic := 1 # 0.

  (* * General properties *)
  Lemma nonzero_mant x : x ≠ 0 → mant x ≠ 0.
  Proof.
    intros E F. apply E. unfold equiv, dy_eq. simpl.
    rewrite F.
    do 2 rewrite left_absorb. reflexivity.
  Qed.

  (* * Properties of min and minus *)
  Lemma min_minus1 x y z : x ∸ min y z = x ∸ y + (min x y ∸ z). 
  Proof with eauto; try ring.
    unfold min.
    case (decide (x ≤ y)); case (decide (y ≤ z)); intros F G.
    rewrite (cut_minus_0 x z)... transitivity y...
    rewrite (cut_minus_0 x y)...
    rewrite (cut_minus_0 y z)...
    symmetry. apply cut_minus_precedes_trans...
  Qed.
  
  Lemma min_minus2 x y z : y ∸ z + (min y z ∸ x) = y ∸ x + (min x y ∸ z).
  Proof with eauto; try ring.
    unfold min.
    case (decide (x ≤ y)); case (decide (y ≤ z)); intros.
    repeat rewrite (cut_minus_0 _ z)... transitivity y...
    apply cut_minus_plus_toggle1... 
    repeat rewrite (cut_minus_0 _ x)...
    repeat rewrite (cut_minus_0 _ x)...
    transitivity y...
  Qed.

  Lemma min_minus3 x y z : (x + min y z) ∸ min (x + y) (x + z) = min (x + y) (x + z) ∸ (x + min y z).
  Proof with auto; try reflexivity.
    destruct (total_order y z) as [G1|G1].
    rewrite (sr_precedes_min_l y z), (sr_precedes_min_l (x + y) (x + z))...
    apply semiring.sr_precedes_plus_compat_l...
    rewrite (sr_precedes_min_r y z), (sr_precedes_min_r (x + y) (x + z))...
    apply semiring.sr_precedes_plus_compat_l...
  Qed.

  Lemma min_minus4 x1 x2 y1 y2 : 
    y1 ∸ x1 + (x1 ∸ x2 + (min x1 x2 ∸ min y1 y2)) = y1 ∸ y2 + (min y1 y2 ∸ min x1 x2) + (x1 ∸ y1).
  Proof with auto.
    unfold min.
    case (decide (x1 ≤ x2)); case (decide (y1 ≤ y2)); intros.
    (* case 1*)
    rewrite (cut_minus_0 x1 x2), (cut_minus_0 y1 y2)... ring.
    (* case 2 *)
    rewrite (cut_minus_0 x1 x2)... 
    destruct (total_order x1 y2) as [G3|G3]; rewrite (cut_minus_0 _ _ G3)... 
    rewrite (cut_minus_0 _ y1)... 
      ring_simplify. symmetry. apply cut_minus_precedes_trans... 
      transitivity y2...
    ring_simplify. symmetry. 
    rewrite commutativity. apply cut_minus_plus_toggle2...    
    (* case 3 *)
    rewrite (cut_minus_0 y1 y2)...
    destruct (total_order x1 y1) as [G3|G3]; rewrite (cut_minus_0 _ _ G3)... 
    rewrite (cut_minus_0 _ y1)... 
      ring_simplify. apply cut_minus_precedes_trans... 
      transitivity x1...
    ring_simplify. 
    rewrite (commutativity (y1 ∸ x2)). apply cut_minus_plus_toggle1...
    (* case 4 *)
    destruct (total_order x1 y1) as [G3|G3];
      rewrite (cut_minus_0 _ _ G3);
      destruct (total_order x2 y2) as [G4|G4];
      rewrite (cut_minus_0 _ _ G4); ring_simplify.
    rewrite cut_minus_precedes_trans... symmetry. apply cut_minus_precedes_trans...
    rewrite cut_minus_precedes_trans... apply cut_minus_precedes_trans... transitivity x1...
    symmetry. rewrite commutativity. rewrite cut_minus_precedes_trans... 
      apply cut_minus_precedes_trans... transitivity y2...
    rewrite cut_minus_precedes_trans... symmetry. rewrite commutativity. 
      apply cut_minus_precedes_trans...
  Qed.

  Lemma dy_plus_proper_aux n m x1 x2 y1 y2 : n ≪ (x1 -- y1) = m ≪ (y1 --x1) → 
    n ≪ (x1 -- x2 + (min x1 x2 -- min y1 y2)) = m ≪ (y1 -- y2 + (min y1 y2 -- min x1 x2)).
  Proof with auto; try reflexivity.
    intros E.
    apply (shiftl_inj (x1 -- y1)). unfold flip. 
    rewrite shiftl_order. rewrite E. 
    repeat rewrite <-shiftl_sum_exp. apply shiftl_proper...
    unfold_cut_minus.
    apply min_minus4.
  Qed.

  (* * Properties of plus *)
  Instance dy_plus_alt_proper: Proper ((=) ==> (=) ==> (=)) dy_plus_alt.
  Proof with auto; try reflexivity.
    intros x1 y1 E1 x2 y2 E2.
    unfold equiv, dy_eq, dy_plus_alt in *. simpl.
    do 2 rewrite shiftl_sum_base. 
    repeat rewrite <-shiftl_sum_exp.
    apply sg_mor. 
    apply dy_plus_proper_aux...
    rewrite (commutativity (expo x1) (expo x2)), (commutativity (expo y1) (expo y2)). 
    apply dy_plus_proper_aux...
  Qed.

  Instance dy_plus_proper: Proper ((=) ==> (=) ==> (=)) dy_plus.
  Proof.
    repeat intro. do 2 rewrite dy_plus_alt_correct.
    apply dy_plus_alt_proper; auto.
  Qed.

  Instance: Associative dy_plus.
  Proof with auto; try reflexivity; try ring.
    intros x y z. do 4 rewrite dy_plus_alt_correct. 
    unfold equiv, dy_eq, dy_plus_alt. simpl. 
    apply shiftl_proper...
    2: rewrite associativity...
    repeat rewrite shiftl_sum_base. 
    repeat rewrite <-shiftl_sum_exp. 
    rewrite associativity.
    repeat apply sg_mor; apply shiftl_proper; unfold_cut_minus...
    apply min_minus1.
    apply min_minus2.
    rewrite (commutativity (expo y) (expo z)), (commutativity (expo x) (expo y)).
    symmetry. apply min_minus1.
  Qed.

  Instance: Commutative dy_plus.
  Proof with auto; try reflexivity. 
    repeat intro. do 2 rewrite dy_plus_alt_correct.
    unfold dy_plus, equiv, dy_eq. simpl.
    apply shiftl_proper...
    apply commutativity...
    rewrite commutativity...
  Qed.

  Instance: SemiGroup Dyadic (op:=dy_plus).

  Lemma dyadic_left_identity (x : Dyadic) : 0 + x = x.
  Proof with auto; try reflexivity.
    rewrite dy_plus_alt_correct.
    unfold equiv, dy_eq, sg_op, dy_plus_alt. simpl.
    rewrite left_absorb, left_identity. rewrite <-shiftl_sum_exp.
    apply shiftl_proper... unfold_cut_minus.
    destruct (total_order (expo x) 0) as [F|F].
    repeat rewrite sr_precedes_min_r... rewrite cut_minus_rightabsorb... ring.
    repeat rewrite sr_precedes_min_l... rewrite cut_minus_leftabsorb... ring.
  Qed.

  Program Instance: Monoid Dyadic (op:=dy_plus) (unit:=dy_0).
  Next Obligation. repeat intro. apply dyadic_left_identity. Qed.
  Next Obligation. repeat intro. rewrite commutativity. apply dyadic_left_identity. Qed.
  
  (* * Properties of opp *)
  Instance: Proper ((=) ==> (=)) dy_opp.
  Proof.
    intros x y E.
    unfold equiv, dy_eq, dy_opp in *. simpl.
    do 2 rewrite opp_shiftl.
    rewrite E. reflexivity.
  Qed.

  Lemma dyadic_ginv (x : Dyadic) : - x + x = 0.
  Proof.
    rewrite dy_plus_alt_correct.
    unfold equiv, dy_eq, sg_op, dy_plus_alt. simpl.
    rewrite left_absorb. rewrite shiftl_sum_base. 
    do 2 rewrite <-shiftl_sum_exp.
    rewrite opp_shiftl. ring.
  Qed.

  Program Instance: Group Dyadic.
  Next Obligation. apply dyadic_ginv. Qed.
  Next Obligation. rewrite commutativity. apply dyadic_ginv. Qed.

  Program Instance: AbGroup Dyadic.
  
  (* * Properties of mult *)
  Instance: Proper ((=) ==> (=) ==> (=)) dy_mult.
  Proof with auto; try reflexivity.
    intros x1 y1 E1 x2 y2 E2.
    unfold equiv, dy_eq, dy_mult in *. simpl. 
    destruct (total_order (expo x1) (expo y1)) as [F|F];
      destruct (total_order (expo x2) (expo y2)) as [G|G];
      rewrite (shiftl_cut_minus_0 F) in E1; 
      rewrite (shiftl_cut_minus_0 G) in E2...
    (* expo x ≤ expo y, expo y ≤ expo z *)
    rewrite E1, E2. 
    rewrite mult_r_shiftl_shiftl, mult_l_shiftl_shiftl. 
    apply shiftl_proper... unfold_cut_minus. 
    rewrite (cut_minus_0 (expo x1 + expo x2)). ring_simplify.
    apply cut_minus_plus_distr...
    apply semiring.sr_precedes_plus_compat...
    (* expo x ≤ expo y, expo y ≤ expo z *)
    rewrite E1, <-E2. 
    rewrite mult_r_shiftl_shiftl, mult_l_shiftl_shiftl. 
    apply shiftl_proper... unfold_cut_minus. 
    apply cut_minus_plus_toggle3...
    (* expo y ≤ expo x, expo y ≤ expo z *)
    rewrite <-E1, E2. 
    rewrite mult_r_shiftl_shiftl, mult_l_shiftl_shiftl. 
    apply shiftl_proper... unfold_cut_minus. 
    symmetry. apply cut_minus_plus_toggle3...
    (* expo y ≤ expo x, expo z ≤ expo y *)
    rewrite <-E2, <-E1. 
    rewrite mult_r_shiftl_shiftl, mult_l_shiftl_shiftl. 
    apply shiftl_proper... unfold_cut_minus.
    rewrite (cut_minus_0 (expo y1 + expo y2)). ring_simplify.
    symmetry. apply cut_minus_plus_distr...
    apply semiring.sr_precedes_plus_compat...
  Qed.

  Instance: Associative dy_mult.
  Proof.
   repeat intro. unfold ring_mult, dy_mult, equiv, dy_eq. simpl.
   apply shiftl_proper. ring. unfold_cut_minus. apply cut_minus_proper; ring. 
  Qed.

  Instance: Commutative dy_mult.
  Proof.
    repeat intro. unfold ring_mult, dy_mult, equiv, dy_eq. simpl.
    apply shiftl_proper. ring. unfold_cut_minus. apply cut_minus_proper; ring. 
  Qed.

  Instance: SemiGroup Dyadic (op:=dy_mult).

  Lemma dyadic_mult_left_identity (x : Dyadic) : 1 * x = x.
  Proof with try reflexivity.
    unfold equiv, dy_eq, dy_mult. simpl.
    rewrite left_identity. rewrite left_identity...
  Qed.

  Program Instance: Monoid Dyadic (op:=dy_mult) (unit:=dy_1).
  Next Obligation. repeat intro. apply dyadic_mult_left_identity. Qed.
  Next Obligation. repeat intro. rewrite commutativity. apply dyadic_mult_left_identity. Qed.

  Instance: CommutativeMonoid Dyadic (op:=dy_mult) (unit:=dy_1).

  Lemma dyadic_distr_l (x y z : Dyadic) : x * (y + z) = (x * y) + (x * z).
  Proof with auto; try reflexivity.
    do 2 rewrite dy_plus_alt_correct.
    unfold equiv, dy_eq, dy_mult, dy_plus_alt; simpl.
    apply shiftl_proper...
    do 2 rewrite <-mult_shiftl.
    rewrite <-distribute_l. repeat apply sg_mor...
    apply shiftl_proper... unfold_cut_minus. apply cut_minus_plus_l_rev.
    apply shiftl_proper... unfold_cut_minus. apply cut_minus_plus_l_rev.
    unfold_cut_minus. apply min_minus3.
  Qed.

  Instance: Distribute dy_mult dy_plus.
  Proof with try reflexivity.
    split; intros x y z.
    apply dyadic_distr_l.
    rewrite commutativity, (commutativity x z), (commutativity y z).
    apply dyadic_distr_l.
  Qed.

  Global Instance: Ring Dyadic.
(*
  (** 
   * Embedding into the rationals
   If we already have a [Rationals] implementation [Q], then we can embed [Dyadic]
   into it. That is, we have an injective ring morphism [DtoQ : Dyadic → Q].
  *)
  Context `{Rationals Q}.
  Add Field Q: (fields.stdlib_field_theory Q).

  (* We don't make (Z >-> Q) a coercion because it could be computationally expensive
   and we want to see where it's called. *)
  Context (ZtoQ: Z → Q) `{!Ring_Morphism ZtoQ}.
  
  (* We use binary division because that might have a more efficient implementation. *)
  Context `{fd : !FieldDiv Q}.

  Program Definition EtoQ (n : Pos Z) : { z : Q | z ≠ 0 } := ZtoQ (1 ≪ n).
  Next Obligation with intuition.
    intros E.
    apply (shiftl_nonzero 1 n).
    apply not_symmetry. apply zero_ne_one.
    apply (injective ZtoQ).
    rewrite rings.preserves_0...
  Qed.

  Global Instance EtoQ_proper: Proper ((=) ==> (=)) EtoQ.
  Proof.
    intros x y E.
    unfold EtoQ. unfold equiv, sig_equiv, sig_relation. simpl.
    rewrite E. reflexivity.
  Qed.
 
  Definition DtoQ (d: Dyadic): Q := ZtoQ (mant d ≪ (expo d -- 0)) // EtoQ (0 -- expo d).

  Global Instance: Proper ((=) ==> (=)) DtoQ.
  Proof with auto; try reflexivity.
    intros x y E.
    unfold DtoQ, EtoQ. simpl. 
    do 2 rewrite additional_operations.field_div_correct.
    apply fields.equal_quotients. simpl.
    do 2 rewrite <-rings.preserves_mult.
    apply sm_proper.
    do 2 rewrite mult_shiftl.
    do 2 rewrite right_identity.
    unfold equiv, dy_eq in E.
    destruct (total_order (expo x) (expo y)) as [F|F]; rewrite (shiftl_cut_minus_0 F) in E.
    rewrite E. do 3 rewrite <-shiftl_sum_exp.
    apply shiftl_proper... unfold_cut_minus. ring_simplify. apply test...
    rewrite <-E. do 3 rewrite <-shiftl_sum_exp.
    apply shiftl_proper... unfold_cut_minus. symmetry. ring_simplify. apply test...
  Qed.

  Lemma EtoQ_plus_mult x y :  EtoQ (x + y) = (EtoQ x) * (EtoQ y).
  Proof.
    intros.
    unfold equiv, sig_equiv, sig_relation, EtoQ. simpl.
    rewrite <-rings.preserves_mult.
    rewrite <-mult_shiftl_1.
    rewrite shiftl_sum_exp.
    reflexivity.
  Qed.

  Lemma EtoQ_zero_one : EtoQ 0 = 1.
  Proof.
    unfold equiv, sig_equiv, sig_relation, EtoQ. simpl.
    rewrite right_identity.
    rewrite rings.preserves_1.
    reflexivity.
  Qed.

  Lemma EtoQ_quotients a b c d : 
    ZtoQ a / EtoQ b + ZtoQ c / EtoQ d = ZtoQ (a ≪ d + c ≪ b) / EtoQ (b + d).
  Proof.
    rewrite rings.preserves_plus.
    do 3 rewrite additional_operations.field_div_correct.
    rewrite fields.quotients. simpl.
    repeat rewrite <-rings.preserves_mult.
    repeat rewrite <-mult_shiftl_1.
    rewrite EtoQ_plus_mult. 
    reflexivity.
  Qed.

  Lemma DtoQ_preserves_plus x y : DtoQ (x + y) = DtoQ x + DtoQ y.
  Proof.
    unfold ring_plus at 1. unfold dy_plus at 1.
    unfold DtoQ. simpl.
    rewrite shiftl_sum_base.
    (* rewrite (commutativity (mant y ≪ expo x) _).*)
    symmetry. apply EtoQ_quotients.
  Qed.
  
  Lemma DtoQ_preserves_zero : DtoQ 0 = 0.
  Proof. 
    unfold DtoQ. simpl.
    rewrite field_div_correct. 
    rewrite preserves_0. ring.
  Qed.
  
  Lemma DtoQ_preserves_group_inv x : DtoQ (-x) = -DtoQ x.
  Proof. 
    unfold DtoQ. simpl.
    do 2 rewrite field_div_correct.
    rewrite preserves_inv. ring.
  Qed.

  Lemma DtoQ_preserves_mult x y : DtoQ (x * y) = DtoQ x * DtoQ y.
  Proof. 
    unfold ring_mult at 1. unfold dy_mult at 1.
    unfold DtoQ. simpl.
    do 3 rewrite field_div_correct. 
    rewrite preserves_mult.
    rewrite EtoQ_plus_mult. 
    rewrite <-mult_inv_distr.
    ring.
  Qed.

  Lemma DtoQ_preserves_one : DtoQ 1 = 1.
  Proof. 
    unfold DtoQ. simpl.
    rewrite field_div_correct.
    rewrite preserves_1. rewrite EtoQ_zero_one.
    apply mult_inverse'.
  Qed.

  Instance: Ring_Morphism DtoQ.
  Proof. 
    repeat (split; try apply _).
    exact DtoQ_preserves_plus.
    exact DtoQ_preserves_zero.
    exact DtoQ_preserves_group_inv.
    exact DtoQ_preserves_mult.
    exact DtoQ_preserves_one.
  Qed.

  Instance: Injective DtoQ.
  Proof with auto.
    split; try apply _.
    intros x y E.
    unfold equiv, dy_eq. unfold DtoQ in E. unfold EtoQ in E.
    do 2 rewrite field_div_correct in E.
    apply equal_quotients in E. simpl in E.
    do 2 rewrite <-preserves_mult in E.
    do 2 rewrite <-mult_shiftl_1 in E.
    symmetry. apply (injective ZtoQ)...
  Qed.
*)
End dyadics.
