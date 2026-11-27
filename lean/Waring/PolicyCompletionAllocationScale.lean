import Waring.PolicyCompletionLoss
import Waring.SampledQuadraticSecondAsymptotic

/-! # Uniform transport from the ambient scale to actual integer cutoffs -/

noncomputable section
open scoped BigOperators
namespace Waring.PolicyCompletionAllocationScale
open ResourceDifferencingCap

theorem rpow_comparable {x y K B t : ℝ} (hx : 0<x) (hy : 0<y) (hK : 1≤K)
    (hyx : y≤K*x) (hxy : x≤K*y) (ht : |t|≤B) : y^t≤K^B*x^t := by
  have hKp : 0<K := zero_lt_one.trans_le hK
  by_cases ht0 : 0≤t
  · calc
      _ ≤ (K*x)^t := Real.rpow_le_rpow hy.le hyx ht0
      _ = K^t*x^t := Real.mul_rpow hKp.le hx.le
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le hK ((le_abs_self t).trans ht)) (Real.rpow_nonneg hx.le _)
  · have ht0' : t≤0 := (lt_of_not_ge ht0).le
    have hh := Real.rpow_le_rpow_of_exponent_nonpos hx hxy ht0'
    rw [Real.mul_rpow hKp.le hy.le] at hh
    have hm := mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hKp.le (-t))
    have hc : K^(-t)*K^t=1 := by rw [← Real.rpow_add hKp]; simp
    have hb : y^t≤K^(-t)*x^t := by simpa only [← mul_assoc,hc,one_mul] using hm
    exact hb.trans (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hK ((neg_le_abs t).trans ht)) (Real.rpow_nonneg hx.le _))

def scaledConstants {j ρ} [Fintype ρ] (R : Allocation j ρ) (J : ℝ) (hJ : 0≤J) : Allocation j ρ :=
  { R with constant := fun r => R.constant r*J
           constant_nonneg := fun r => mul_nonneg (R.constant_nonneg r) hJ }

@[simp] theorem scaledConstants_saving {j ρ} [Fintype ρ] (R : Allocation j ρ)
    (J : ℝ) (hJ : 0≤J) : (scaledConstants R J hJ).totalSaving=R.totalSaving := rfl

theorem totalSaving_abs_le {j ρ} [Fintype ρ] (R : Allocation j ρ)
    {B : ℝ} (hB : 0≤B) (hb : ∀ r,|R.saving r|≤B) : |R.totalSaving|≤B := by
  calc
    _ ≤ ∑ r,|R.weight r*R.saving r| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ r,R.weight r*|R.saving r| := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [abs_mul,abs_of_nonneg (R.weight_nonneg r)]
    _ ≤ ∑ r,R.weight r*B := Finset.sum_le_sum (fun r _ => mul_le_mul_of_nonneg_left (hb r) (R.weight_nonneg r))
    _ = (∑ r,R.weight r)*B := (Finset.sum_mul ..).symm
    _ ≤ B := by simpa only [one_mul] using mul_le_mul_of_nonneg_right R.mass_le hB

theorem scaledConstants_totalConstant_le {j ρ} [Fintype ρ] (R : Allocation j ρ)
    {J : ℝ} (hJ : 1≤J) :
    (scaledConstants R J (zero_le_one.trans hJ)).totalConstant≤R.totalConstant*J := by
  have hprod : (scaledConstants R J (zero_le_one.trans hJ)).totalConstant=
      R.totalConstant*J^(∑ r,R.weight r) := by
    simp only [Allocation.totalConstant,scaledConstants]
    simp_rw [Real.mul_rpow (R.constant_nonneg _) (zero_le_one.trans hJ)]
    rw [Finset.prod_mul_distrib,← Real.rpow_sum_of_nonneg (zero_le_one.trans hJ)
      (fun r _ => R.weight_nonneg r)]
  rw [hprod]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_self_of_one_le hJ R.mass_le) R.totalConstant_nonneg

/-- Resource savings may be negative. A compact height range gives a fixed
absolute bound, so replacing P by the literal center cutoff changes only a
finite uniform constant, not any saving or frozen source parameter. -/
theorem moments_at_comparable_cutoff {j ρ σ} [Fintype ρ] [Fintype σ]
    (R : Allocation j ρ) (f : Option (Fin j) → σ → ℝ)
    {P N K B δ : ℝ} (hP : 0<P) (hN : 0<N) (hK : 1≤K) (hB : 0≤B)
    (hPN : P≤K*N) (hNP : N≤K*P) (hδ : 0≤δ) (hδ1 : δ≤1)
    (hbound : ∀ r,|R.saving r|≤B)
    (hmom : ∀ r,FiniteResourceHolder.average (fun x => (f (R.factor r) x)^(R.order r))≤
      R.constant r*P^(δ-R.saving r)) :
    ∀ r,FiniteResourceHolder.average (fun x => (f (R.factor r) x)^(R.order r))≤
      (R.constant r*K^(B+1))*N^(δ-R.saving r) := by
  intro r
  have he : |δ-R.saving r|≤B+1 := by
    have h := abs_sub_le δ 0 (R.saving r)
    simp only [sub_zero,zero_sub,abs_neg,abs_of_nonneg hδ] at h
    exact h.trans (by linarith [hbound r])
  have hp := rpow_comparable hN hP hK hPN hNP he
  calc
    _ ≤ R.constant r*P^(δ-R.saving r) := hmom r
    _ ≤ R.constant r*(K^(B+1)*N^(δ-R.saving r)) := mul_le_mul_of_nonneg_left hp (R.constant_nonneg r)
    _ = _ := by ring

theorem capped_exponent_abs {S B δ d : ℝ} (hB : 0≤B) (hS : |S|≤B)
    (hδ : 0≤δ) (hδ1 : δ≤1) (hd : 1≤d) : |δ/d-min 1 S/d|≤B+2 := by
  have hdpos : 0<d := zero_lt_one.trans_le hd
  have hmin : |min 1 S|≤B+1 := by
    apply abs_le.mpr
    constructor
    · apply le_min <;> linarith [(abs_le.mp hS).1]
    · exact (min_le_left _ _).trans (by linarith)
  rw [← sub_div,abs_div,abs_of_pos hdpos]
  calc
    _ ≤ (B+2)/d := div_le_div_of_nonneg_right
      ((abs_sub_le δ 0 (min 1 S)).trans (by simpa only [sub_zero,zero_sub,abs_neg,abs_of_nonneg hδ] using
        (show |δ|+|min 1 S|≤B+2 by rw [abs_of_nonneg hδ]; linarith))) hdpos.le
    _ ≤ _ := div_le_self (by linarith) hd

/-- The original completion logarithm at a fixed multiple of P is bounded
by any positive ambient power, uniformly in the actual integer cutoff. -/
theorem completionLoss_scaled {D ε : ℝ} (hD : 1≤D) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ P : ℝ,1≤P → 2*D≤P → ∀ N : ℕ,0<N → (N:ℝ)≤D*P →
      CartesianPolynomialBounds.completionLoss N≤C*P^ε := by
  obtain ⟨C,hC,hlog⟩ := DyadicLogLoss.logLoss_pow_le_rpow 1 hε
  refine ⟨12*C,by positivity,?_⟩
  intro P hP hDP N hN hNP
  have hNR : (0:ℝ)<N := by exact_mod_cast hN
  have h2N : 2*(N:ℝ)≤P^(2:ℝ) := by
    rw [Real.rpow_two]
    nlinarith
  have hbound := SampledQuadraticSecondAsymptotic.logLoss_polynomial_range hP
    (show (0:ℝ)<2*(N:ℝ) by positivity) (show (0:ℝ)≤2 by norm_num) h2N
  have hh : DyadicLogLoss.logLoss P≤C*P^ε := by simpa only [pow_one] using hlog P hP
  unfold CartesianPolynomialBounds.completionLoss
  change 4*DyadicLogLoss.logLoss (2*(N:ℝ))≤_
  nlinarith

#print axioms rpow_comparable
#print axioms moments_at_comparable_cutoff
#print axioms completionLoss_scaled
end Waring.PolicyCompletionAllocationScale
