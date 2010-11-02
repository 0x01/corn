(* nasty because Zplus depends on Pminus which is a bucket of FAIL *)

Require 
  interfaces.naturals theory.naturals peano_naturals.
Require Import
  BinInt Morphisms Ring Arith
  abstract_algebra interfaces.integers
  theory.categories theory.rings 
  signed_binary_positives. 

(* canonical names: *)
Instance z_equiv: Equiv BinInt.Z := eq.
Instance: RingPlus BinInt.Z := BinInt.Zplus.
Instance: RingZero BinInt.Z := BinInt.Z0.
Instance: RingOne BinInt.Z := BinInt.Zpos BinPos.xH.
Instance: RingMult BinInt.Z := BinInt.Zmult.
Instance: GroupInv BinInt.Z := BinInt.Zopp.
  (* some day we'd like to do this with [Existing Instance] *)

(* propers: *)
Instance: Proper (equiv ==> equiv ==> equiv) BinInt.Zplus.
Proof. unfold equiv, z_equiv. repeat intro. subst. reflexivity. Qed.
Instance: Proper (equiv ==> equiv ==> equiv) BinInt.Zmult.
Proof. unfold equiv, z_equiv. repeat intro. subst. reflexivity. Qed.
Instance: Proper (equiv ==> equiv) BinInt.Zopp.
Proof. unfold equiv, z_equiv. repeat intro. subst. reflexivity. Qed.

(* properties: *)
Instance: Associative BinInt.Zplus := BinInt.Zplus_assoc.
Instance: Associative BinInt.Zmult := BinInt.Zmult_assoc.
Instance: Commutative BinInt.Zplus := BinInt.Zplus_comm.
Instance: Commutative BinInt.Zmult := BinInt.Zmult_comm.
Instance: Distribute BinInt.Zmult BinInt.Zplus :=
  { distribute_l := BinInt.Zmult_plus_distr_r; distribute_r := BinInt.Zmult_plus_distr_l }.
Instance: LeftIdentity BinInt.Zplus 0 := BinInt.Zplus_0_l.
Instance: RightIdentity BinInt.Zplus 0 := BinInt.Zplus_0_r.
Instance: LeftIdentity BinInt.Zmult 1 := BinInt.Zmult_1_l.
Instance: RightIdentity BinInt.Zmult 1 := BinInt.Zmult_1_r.

(* structures: *)
Instance: Equivalence (@eq BinInt.Z). (* this should not be necessary, seems like a regression bug *)
Instance: Setoid BinInt.Z.
Instance: SemiGroup _ (op:=BinInt.Zplus).
Instance: SemiGroup _ (op:=BinInt.Zmult).
Instance: Monoid _ (op:=BinInt.Zplus) (unit:=BinInt.Z0).
Instance: Monoid _ (op:=BinInt.Zmult) (unit:=BinInt.Zpos BinPos.xH).
Instance: CommutativeMonoid _ (op:=BinInt.Zmult) (unit:=BinInt.Zpos BinPos.xH).
Instance: @Group _ _ (BinInt.Zplus) (BinInt.Z0) _
  := { ginv_l := BinInt.Zplus_opp_l; ginv_r := BinInt.Zplus_opp_r }.
Instance: AbGroup BinInt.Z (op:=BinInt.Zplus) (unit:=BinInt.Z0).
Program Instance: Ring BinInt.Z.

(* misc: *)
Instance: ∀ x y: BinInt.Z, Decision (x = y) := ZArith_dec.Z_eq_dec.

Add Ring Z: (stdlib_ring_theory BinInt.Z).

Definition map_Z `{RingPlus R} `{RingZero R} `{RingOne R} `{GroupInv R} (z: Z): R :=
  match z with
  | Z0 => 0
  | Zpos p => map_pos p
  | Zneg p => - map_pos p
  end.

Instance inject: IntegersToRing Z := λ B _ _ _ _ _, @map_Z B _ _ _ _.

Section for_another_ring.

  Context `{Ring R}.

  Add Ring R: (stdlib_ring_theory R).

  Lemma preserves_opp x: map_Z (- x) = - map_Z x.
  Proof with try reflexivity.
   destruct x; simpl...
    rewrite opp_0...
   rewrite inv_involutive...
  Qed.

  Lemma preserves_Zplus x y: map_Z (x + y) = map_Z x + map_Z y.
  Proof with try reflexivity; try assumption; try ring.
   destruct x; simpl; intros...
    destruct y; simpl...
     apply preserves_Pplus.
    case_eq (Pcompare p p0 Eq); intros; simpl.
      rewrite (Pcompare_Eq_eq _ _ H0)...
     rewrite preserves_Pminus...
    apply preserves_Pminus.
    unfold Plt.
    rewrite (ZC1 _ _ H0)...
   destruct y; simpl...
    case_eq (Pcompare p p0 Eq); intros; simpl.
      rewrite (Pcompare_Eq_eq _ _ H0)...
     rewrite preserves_Pminus...
    rewrite preserves_Pminus...
    unfold Plt.
    rewrite (ZC1 _ _ H0)...
   rewrite preserves_Pplus...
  Qed.

  Lemma preserves_Zmult x y: map_Z (x * y) = map_Z x * map_Z y.
  Proof with try reflexivity; try ring.
   destruct x; simpl; intros...
    destruct y; simpl...
     apply preserves_Pmult.
    rewrite preserves_Pmult...
   destruct y; simpl...
    rewrite preserves_Pmult...
   rewrite preserves_Pmult...
  Qed.

  Instance: Proper (equiv ==> equiv)%signature map_Z.
  Proof. unfold equiv, z_equiv. repeat intro. subst. reflexivity. Qed.

  Hint Resolve preserves_Zplus preserves_Zmult preserves_opp.
  Hint Constructors Monoid_Morphism SemiGroup_Morphism Group_Morphism Ring_Morphism.

  Global Instance map_Z_ring_mor: Ring_Morphism map_Z.
  Proof. repeat (constructor; auto with typeclass_instances; try reflexivity; try apply _). Qed.

  Section with_another_morphism.

    Context map_Z' `{!Ring_Morphism (map_Z': Z → R)}.

    Let agree_on_0: map_Z Z0 = map_Z' Z0.
    Proof. symmetry. apply preserves_0. Qed.

    Let agree_on_1: map_Z 1%Z = map_Z' 1%Z.
    Proof. symmetry. apply preserves_1. Qed.

    Let agree_on_positive p: map_Z (Zpos p) = map_Z' (Zpos p).
    Proof with try reflexivity.
     induction p; simpl.
       rewrite IHp.
       rewrite xI_in_ring_terms.
       rewrite agree_on_1.
       do 2 rewrite <- preserves_sg_op...
      rewrite IHp.
      rewrite xO_in_ring_terms.
      rewrite <- preserves_sg_op...
     apply agree_on_1.
    Qed.

    Let agree_on_negative p: map_Z (Zneg p) = map_Z' (Zneg p).
    Proof with try reflexivity.
     intros.
     replace (Zneg p) with (- (Zpos p))...
     do 2 rewrite preserves_inv.
     rewrite <- agree_on_positive...
    Qed.

    Lemma same_morphism: integers_to_ring Z R = map_Z'.
    Proof.
     intros [].
       apply agree_on_0.
      apply agree_on_positive.
     apply agree_on_negative.
    Qed.

  End with_another_morphism.

End for_another_ring.

Instance: Initial (ring.object Z).
Proof.
  apply integer_initial. intros. apply same_morphism. auto.
Qed.

Instance: Integers Z.

(* The Peano naturals can be embedded into Z *)
Instance: Proper ((=) ==> (=)) Z_of_nat.
Proof.
  intros x y E.
  rewrite E. reflexivity.
Qed.

Instance: SemiRing_Morphism Z_of_nat.
Proof.
  repeat (split; try apply _).
  exact Znat.inj_plus.
  exact Znat.inj_mult.
Qed.

(* Relate <= on Z to our ≤ *)
(* Figure out whether the standard library contains lemmas to make the following proofs shorter.
  There should be, because these proofs look horrible... *)
Lemma sr_precedes_Zle (x y : Z) : x ≤ y → (x <= y)%Z.
Proof with auto with zarith.
  intros [z Ez].
  rewrite <-(theory.naturals.to_semiring_unique Z Z_of_nat) in Ez.
  generalize dependent x. induction z; intros.
  apply Zorder.Zeq_le. rewrite <-Ez...
  apply Zorder.Zle_succ_le.
  apply IHz. rewrite Znat.inj_S in Ez. rewrite <-Ez.
  apply Zplus_succ_comm.
Qed.

Lemma Zle_sr_precedes (x y : Z) : (x <= y)%Z → x ≤ y.
Proof with auto with zarith.
  intros E.
  destruct (Zorder.Zle_lt_or_eq x y E) as [E2 | E2].
  destruct (Zcompare.Zcompare_Gt_spec y x) as [z Ez].
    apply Zcompare.Zcompare_Gt_Lt_antisym.
    pose proof (Zcompare.Zlt_compare x y E2). 
    destruct ((x ?= y)%Z); try contradiction...
  exists (nat_of_P z).
  rewrite <-(theory.naturals.to_semiring_unique Z Z_of_nat)...
  rewrite <-Znat.Zpos_eq_Z_of_nat_o_nat_of_P, <-Ez.
  replace ((y + - x)%Z) with (y + -x) by reflexivity. ring.
  exists (0%nat).
  rewrite <-(theory.naturals.to_semiring_unique Z Z_of_nat)...
  rewrite Znat.inj_0. rewrite E2. apply Zplus_0_r.
Qed.
