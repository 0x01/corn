Require Import CRArith CRtrans CRconst Qmetric Utf8.
Require Import ProductMetric CompleteProduct CPoly_Newton.
Require Import metric2.Classified Program.
Require Import Qpossec.

Open Scope uc_scope.
Notation "X × Y" := (ProductMS X Y) (at level 40).
Notation "f >> g" := (Cbind_slow f ∘ g) (at level 50). (* TODO fix *)
Notation "x >>= f" := (Cbind_slow f x) (at level 50).
Notation "( f , g )" := (together f g).
Notation "'ℚ'" := Q_as_MetricSpace.

Section IVP.

 Implicit Arguments diag [X].

 (* initial value problem is a diff. eqn. y'(t) = F(t, y(t))
    with initial conditions that $y(t_0)=y_0$; so this is what
    is specified here: *)
 Variable F: ℚ × ℚ --> CR.
 Variable t₀ y₀ : ℚ.
 Variable integrate: Q → Q → ℚ --> CR → CR.

 Section Picard.

 (* the function x ↦ F(x,u(x)) for some u:ℚ --> CR *)
 Definition vxfx (u:ℚ --> CR) : (ℚ --> CR) :=
   F >> Couple ∘ (Cunit, u) ∘ diag.
 
 (* Φ(u) := t ↦ y₀ + ∫_t₀^t F(x,u(x)) dx *)
 Definition Phi_raw u (t:ℚ) : CR := ((Cunit y₀) + integrate t₀ t (vxfx u)) % CR.

 Definition Phi_uc u: is_UniformlyContinuousFunction (Phi_raw u) (λ (ε:Qpos), ε).
 Admitted.

 Definition Phi : (ℚ --> CR) → (ℚ --> CR) :=
   λ u, (Build_UniformlyContinuousFunction (Phi_uc u)).

(*
   at this point we have Φ : A → A an operator on A,
   where A is the banach space of UCF of type ℚ → CR

   We want to state that it is a contraction map
   on this space, for this we need the operator norm on A.

   P := (Φ ∘ Φ ∘ ⋯ ∘ Φ) then is the picard operator.
 
   And let P¹ := Φ , Pⁿ := Φ ∘ Pⁿ⁻¹
  
   From the Lipschitz constant [c] and precision [ε] we can
   then compute [n] such that (P u ≈ Pⁿ u).

   TODO: class/record for Contractions
   TODO: Is (-->) a metric space with operator norm?
*)
 End Picard.


 Section BanachIteration.

 Variable A:Type.
 Variable L:A → A.

 (* TODO use stdlib function *)
 Fixpoint ncomp (n:nat) : A → A :=
   match n with
   | O => λ x, x
   | S m => λ x, L (ncomp m x)
   end.

 End BanachIteration.

 Implicit Arguments ncomp [A].

 Example ex1: ncomp (λ x, x+3) 4 0 = 12 % Z.
  now compute.
 Qed.

 Definition picard := ncomp Phi.
End IVP.

Section SimpsonTest.

 Require Import SimpsonIntegration.

 Definition integration (a:Q) (b:Q) (f:ℚ --> CR) : CR :=
   if Qeq_bool a b then
     (0%CR)
   else
     let M := 3 in simpson_integral f M a (QabsQpos (b - a)).

 Definition spicard F t₀ y₀:= picard F t₀ y₀ integration.

End SimpsonTest.


Section TestIVP.
 (* [y' = y] *)
 Definition F_raw : ℚ × ℚ → CR := λ p, Cunit (snd p).
 
 Lemma F_uc : (is_UniformlyContinuousFunction F_raw (λ ε, ε / (2#1)) % Qpos).
 Admitted.
  
 Definition F := Build_UniformlyContinuousFunction F_uc.
  
 Definition t₀ := 0 : ℚ.
 Definition y₀ := 1 : ℚ.

End TestIVP.


Open Scope Q_scope.

Definition eval (n:positive) (r:CR) : Z :=
 let m := (iter_pos n _ (Pmult 10) 1%positive) in
 let (a,b) := (approximate r (1#m)%Qpos)*m in
 Zdiv a b.

Definition exp n := spicard F t₀ y₀ n Cunit.

Time Eval vm_compute in eval 3 (exp 4 (1#2)).
(*
     = 1646
     : Z
Finished transaction in 97. secs (96.96606u,0.084005s)
*)


(*
Definition h := const_uc (5#7:Q_as_MetricSpace).
Definition const_1 : CR --> CR := Cbind QPrelengthSpace (const_uc (1:Q_as_MetricSpace)).
Definition h' := uc_compose (scale (11#13)) h.

Require Import Integration.
Require Import SimpsonIntegration.

Time Eval vm_compute in (eval 3 (1 + (Integrate h' 0 (1#2)))%CR).
Time Eval vm_compute in (eval 3 (1 + (simpson_integral h' 1 0 (1#2)))%CR).

Time Eval vm_compute in (eval 3 (Picard_raw (@const_uc Q_as_MetricSpace (1#1)) 1)).
Time Eval vm_compute in (eval 3 (picard 1 1)).
Time Eval vm_compute in (eval 2 (picard 2 1)).

End example.

*)