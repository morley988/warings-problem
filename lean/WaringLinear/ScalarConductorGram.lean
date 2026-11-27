import WaringLinear.ScalarSampleGram
import WaringLinear.ExactConductor

/-! # The cyclic conductor decomposition for actual rational Fourier fibres -/
noncomputable section
open scoped BigOperators Classical ComplexConjugate
namespace WaringLinear

/-- The reduced denominator of the difference of two q-lifts always divides q. -/
theorem kernel_difference_order_dvd (q : ℕ) (a b : (circleCover q).ker) :
    addOrderOf (a.val-b.val)∣q := by
  rw [addOrderOf_dvd_iff_nsmul_eq_zero,smul_sub]
  have ha : q • a.val=0 := AddMonoidHom.mem_ker.mp a.property
  have hb : q • b.val=0 := AddMonoidHom.mem_ker.mp b.property
  simp [ha,hb]

/-- Filtering a Gram form by a conductor condition is the corresponding
finite sum over ordered pairs, before any absolute values have been taken. -/
theorem gramForm_restrict {ι : Type*} [Fintype ι] (A : ι→ι→ℂ)
    (w : ι→ℂ) (P : ι×ι→Prop) [DecidablePred P] :
    gramForm (fun a b => if P (a,b) then A a b else 0) w =
      ∑ u∈Finset.univ.filter P,conj (w u.1)*w u.2*A u.1 u.2 := by
  simp only [gramForm,Finset.sum_filter,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp

/-- A bound for the complete low-denominator blocks together with the
actual exponential-sum bounds at every higher reduced denominator controls
all large samples, uniformly over the lift centre x. The divisor factor
comes from exact Möbius inversion inside each quadratic form. -/
theorem scalar_fibre_from_conductors
    (box s : Finset ℕ) (hs : s⊆box) (q k M : ℕ) (hq : 0<q)
    (X C E z σ : ℝ) (hX : 1≤X) (hC : 0≤C) (hE : 0≤E) (hz : 0≤z)
    (hc : (box.card:ℝ)≤X) (hslack : 32*E≤X^(σ-2*z))
    (hblock : ∀ (d:ℕ),d∣q → d≤M → ∀ (t:Finset (circleCover q).ker) (w:t→ℂ),
      ‖gramForm (fun a b:t =>
        if addOrderOf (a.1.val-b.1.val)∣d then scalarPowerSum box k (a.1.val-b.1.val)
        else 0) w‖ ≤ (C*X)*∑i,‖w i‖^2)
    (hhigh : ∀ a b : (circleCover q).ker, M<addOrderOf (a.val-b.val) →
      ‖scalarPowerSum box k (a.val-b.val)‖ ≤ E*X^(1-σ))
    (x : ScalarTorus) :
    scalarFibreMass q hq X z (scalarPowerSum s k) x ≤
      ((18+8*z*Real.logb 2 X)*((q.divisors.card:ℝ)^2*C))*X^2 := by
  classical
  let A (a b:ScalarTorus) := if addOrderOf (a-b)≤M then scalarPowerSum box k (a-b) else 0
  let B (a b:ScalarTorus) := if M<addOrderOf (a-b) then scalarPowerSum box k (a-b) else 0
  apply classical_correlation_fibre box s hs q k hq X _ E z σ hX (by positivity) hE hz hc hslack A B
  · intro a b
    by_cases h : addOrderOf (a.val-b.val)≤M
    · simp only [A,B,if_pos h,if_neg (not_lt.mpr h),add_zero]
    · simp only [A,B,if_neg h,if_pos (lt_of_not_ge h),zero_add]
  · intro t w
    let r (u:t×t) := addOrderOf (u.1.1.val-u.2.1.val)
    let H (a b:t) := scalarPowerSum box k (a.1.val-b.1.val)
    let u (v:t×t) := conj (w v.1)*w v.2*H v.1 v.2
    let W := ∑i,‖w i‖^2
    have hW : 0≤W := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hblock' (d : ℕ) (hd:d∈q.divisors) (hM:d≤M) :
        ‖∑v∈Finset.univ.filter (fun v => r v∣d),u v‖≤(C*X)*W := by
      rw [←gramForm_restrict H w (fun v => r v∣d)]
      exact hblock d (Nat.mem_divisors.mp hd).1 hM t w
    have raw := conductor_cutoff_sum r u q M ((C*X)*W) hq.ne' (by positivity)
      (fun v => kernel_difference_order_dvd _ _ _) hblock'
    change ‖gramForm (fun a b:t => if r (a,b)≤M then H a b else 0) w‖≤_
    rw [gramForm_restrict H w (fun v => r v≤M)]
    exact raw.trans_eq (by dsimp [W]; ring)
  · intro a b
    by_cases h : M<addOrderOf (a.val-b.val)
    · simpa [B,h] using hhigh a b h
    · simp [B,h]
      positivity

#print axioms scalar_fibre_from_conductors
end WaringLinear
