import Waring.RestrictedSmoothUniformity
import Waring.RestrictedSmoothBlockArcs
import Mathlib.NumberTheory.Harmonic.Bounds

/-! # Uniform summation of the actual shorter smooth moments -/

noncomputable section
open scoped BigOperators
namespace Waring.RestrictedSmoothArcs
open SmoothMoments RestrictedSmoothFactorization

theorem quotient_power_sum_le_harmonic {X R lam : ℝ} (hX : 1 ≤ X) (hlam : 1 ≤ lam) :
    (∑ z ∈ smoothNumbers X R,(X/(z : ℝ))^lam) ≤ X^lam*(harmonic ⌊X⌋₊ : ℝ) := by
  classical
  have hX0 : 0 ≤ X := zero_le_one.trans hX
  calc
    _ ≤ ∑ z ∈ smoothNumbers X R,X^lam*(z : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro z hz
      have hz1 : (1 : ℝ) ≤ z := by exact_mod_cast (mem_smoothNumbers.mp hz).1.1
      have hzp : 0 < (z : ℝ) := zero_lt_one.trans_le hz1
      have hpow : (z : ℝ) ≤ (z : ℝ)^lam := by
        simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hz1 hlam
      rw [Real.div_rpow hX0 hzp.le,← div_eq_mul_inv]
      exact div_le_div_of_nonneg_left (Real.rpow_nonneg hX0 _) hzp hpow
    _ ≤ ∑ z ∈ Finset.Icc 1 ⌊X⌋₊,X^lam*(z : ℝ)⁻¹ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      exact fun _ _ _ => by positivity
    _ = _ := by
      rw [harmonic_eq_sum_Icc,Rat.cast_sum,Finset.mul_sum]
      simp only [Rat.cast_inv,Rat.cast_natCast]

theorem quotient_power_sum_epsilon {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ P X R lam : ℝ,1 ≤ P → 1 ≤ X → X ≤ P → 1 ≤ lam →
      (∑ z ∈ smoothNumbers X R,(X/(z : ℝ))^lam) ≤ C*P^ε*X^lam := by
  refine ⟨1+1/ε,by positivity,?_⟩
  intro P X R lam hP hX hXP hlam
  have hP0 : 0 ≤ P := zero_le_one.trans hP
  have hp : 1 ≤ P^ε := Real.one_le_rpow hP hε.le
  have hH : (harmonic ⌊X⌋₊ : ℝ) ≤ (1+1/ε)*P^ε := by
    calc
      _ ≤ 1+Real.log X := harmonic_floor_le_one_add_log X hX
      _ ≤ 1+Real.log P := add_le_add_left (Real.log_le_log (zero_lt_one.trans_le hX) hXP) _
      _ ≤ 1+P^ε/ε := add_le_add_left (Real.log_le_rpow_div hP0 hε) _
      _ ≤ P^ε+P^ε/ε := add_le_add_right hp _
      _ = _ := by ring
  calc
    _ ≤ X^lam*(harmonic ⌊X⌋₊ : ℝ) := quotient_power_sum_le_harmonic hX hlam
    _ ≤ X^lam*((1+1/ε)*P^ε) := mul_le_mul_of_nonneg_left hH (Real.rpow_nonneg (zero_le_one.trans hX) _)
    _ = _ := by ring

/-- One uniform smoothness choice controls every shorter moment appearing
after the prime-support commutation and integer dilation. -/
theorem sum_shorter_moments_epsilon {k s : ℕ} {lam ε : ℝ}
    (hadm : AdmissibleExponent k s lam) (hlam : 1 ≤ lam) (hε : 0 < ε) :
    ∃ η : ℝ,0 < η ∧ ∃ C : ℝ,0 < C ∧ ∀ P : ℝ,1 ≤ P →
      ∀ R : ℝ,1 ≤ R → R ≤ P^η → ∀ X : ℝ,1 ≤ X → X ≤ P →
      ∀ π : ℕ,1 ≤ π → (π : ℝ) ≤ R →
      (∑ z ∈ smoothNumbers X R,smoothMoment k s (X/(z : ℝ)) π) ≤ C*P^ε*X^lam := by
  obtain ⟨η,hη,A,hA,hbound⟩ := admissibleExponent_uniform_shorter hadm (half_pos hε)
  obtain ⟨D,hD,hsum⟩ := quotient_power_sum_epsilon (half_pos hε)
  refine ⟨η,hη,A*D,mul_pos hA hD,?_⟩
  intro P hP R hR hRP X hX hXP π hπ hπR
  have hPp : 0 < P := zero_lt_one.trans_le hP
  have hπ1 : (1 : ℝ) ≤ π := by exact_mod_cast hπ
  calc
    _ ≤ ∑ z ∈ smoothNumbers X R,A*P^(ε/2)*(X/(z : ℝ))^lam := by
      apply Finset.sum_le_sum
      intro z hz
      have hz' := (mem_smoothNumbers.mp hz).1
      have hz1 : (1 : ℝ) ≤ z := by exact_mod_cast hz'.1
      have hzp : 0 < (z : ℝ) := zero_lt_one.trans_le hz1
      have hzX : (z : ℝ) ≤ X := (Nat.cast_le.mpr hz'.2).trans (Nat.floor_le (zero_le_one.trans hX))
      exact hbound P hP π hπ1 (hπR.trans hRP) (X/(z : ℝ))
        ((one_le_div hzp).mpr hzX) ((div_le_self (zero_le_one.trans hX) hz1).trans hXP)
    _ = A*P^(ε/2)*∑ z ∈ smoothNumbers X R,(X/(z : ℝ))^lam := (Finset.mul_sum _ _ _).symm
    _ ≤ A*P^(ε/2)*(D*P^(ε/2)*X^lam) :=
      mul_le_mul_of_nonneg_left (hsum P X R lam hP hX hXP hlam) (by positivity)
    _ = A*D*(P^(ε/2)*P^(ε/2))*X^lam := by ring
    _ = _ := by rw [← Real.rpow_add hPp,add_halves]

#print axioms sum_shorter_moments_epsilon
end Waring.RestrictedSmoothArcs
