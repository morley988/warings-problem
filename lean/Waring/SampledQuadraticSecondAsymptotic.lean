import Waring.SampledQuadraticSecond
import Waring.DivisorBound
import Waring.DyadicLogLoss

/-!
# The genuine centered sampled quadratic second-moment resource

The divisor and logarithmic estimates discharge every auxiliary counting
premise. The result is uniform for all real common linear modulations and all
finite centered summation sets, with a fixed integer leading coefficient.
-/

noncomputable section
open scoped BigOperators
namespace Waring.SampledQuadraticSecondAsymptotic

/-- A polynomial upper bound for the sampling range controls its logarithm
by the ambient length logarithm. -/
theorem logLoss_polynomial_range {P H A : ℝ} (hP : 1 ≤ P) (hH : 0 < H)
    (hA : 0 ≤ A) (hHA : H ≤ P^A) :
    DyadicLogLoss.logLoss H ≤ (A+1)*DyadicLogLoss.logLoss P := by
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hlog := Real.log_le_log hH hHA
  rw [Real.log_rpow hPpos] at hlog
  have hlogP : 0 ≤ Real.log P := Real.log_nonneg hP
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hdiv := div_le_div_of_nonneg_right hlog hlog2.le
  have hquot : 0 ≤ Real.log P/Real.log 2 := div_nonneg hlogP hlog2.le
  unfold DyadicLogLoss.logLoss
  rw [mul_div_assoc] at hdiv
  nlinarith

/-- Actual centered quadratic second moment in the manuscript's minor range:
`H≥P` and intrinsic height `L≥P`. No second-moment, divisor, reciprocal,
transference, or completion estimate is assumed.

The one real modulation `t` is common to every sampled `h`; it is deliberately
not replaced by a function of `h`. -/
theorem sampled_second_moment_epsilon (A : ℝ) (hA : 0 ≤ A) (c : ℕ) (hc : 0 < c)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P → ∀ H : ℕ,
      P ≤ (H : ℝ) → (H : ℝ) ≤ P^A → ∀ α t : ℝ, ∀ S : Finset ℤ,
      (∀ z ∈ S, |(z : ℝ)| ≤ P) →
      P ≤ RationalHeight.height ((H : ℝ)*P^2) α →
      SampledQuadraticSecond.sampledMoment S ((c : ℝ)*α) t H ≤
        C*P^(1+ε)*H := by
  let δ := ε/4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨Cd, hCd, hdiv⟩ := DivisorBound.divisor_count_le_cutoff_rpow hδ
  obtain ⟨Cl, hCl, hlog⟩ := DyadicLogLoss.logLoss_pow_le_rpow 1 (half_pos hε)
  let K := Cd*(A+1)*Cl
  let C := 6+1024*((c : ℝ)+3)*K
  have hA1 : 0 < A+1 := by linarith
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro P hP H hPH hHA α t S hS hPL
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hHpos : (0 : ℝ) < H := hPpos.trans_le hPH
  have hP2 : 1 ≤ P^2 := by nlinarith
  let D := Cd*(P^2)^δ
  have hD : 0 < D := by dsimp [D]; positivity
  have hdivD : ∀ n : ℕ, 0 < n → (n : ℝ) ≤ P^2 → (n.divisors.card : ℝ) ≤ D :=
    fun n hn hnP => hdiv (P^2) hP2 n hn hnP
  have hDpow : D = Cd*P^(ε/2) := by
    dsimp [D]
    rw [← Real.rpow_natCast P 2, ← Real.rpow_mul hPpos.le]
    norm_num only [Nat.cast_ofNat]
    have heq : (2 : ℝ)*δ = ε/2 := by dsimp [δ]; ring
    rw [heq]
  have hFH : DyadicLogLoss.logLoss (H : ℝ) ≤ (A+1)*Cl*P^(ε/2) := by
    have hb := logLoss_polynomial_range hP hHpos hA hHA
    have hp : DyadicLogLoss.logLoss P ≤ Cl*P^(ε/2) := by simpa using hlog P hP
    have hm := mul_le_mul_of_nonneg_left hp hA1.le
    exact hb.trans (by simpa only [mul_assoc] using hm)
  have hprod : D*DyadicLogLoss.logLoss (H : ℝ) ≤ K*P^ε := by
    calc
      D*DyadicLogLoss.logLoss (H : ℝ) ≤ D*((A+1)*Cl*P^(ε/2)) :=
        mul_le_mul_of_nonneg_left hFH hD.le
      _ = K*(P^(ε/2)*P^(ε/2)) := by rw [hDpow]; dsimp [K]; ring
      _ = K*P^ε := by
        rw [← Real.rpow_add hPpos]
        congr 2
        ring
  have hPeps : 1 ≤ P^ε := Real.one_le_rpow hP hε.le
  have hcoeff : 6+1024*D*((c : ℝ)+3)*DyadicLogLoss.logLoss (H : ℝ) ≤ C*P^ε := by
    have hm := mul_le_mul_of_nonneg_left hprod
      (show 0 ≤ 1024*((c : ℝ)+3) by positivity)
    dsimp [C]
    nlinarith
  have hb := SampledQuadraticSecond.sampledMoment_z2_centered_integer_coefficient_log
    S α t D P c H hc hS hD.le hdivD hP hPH hPL
  calc
    SampledQuadraticSecond.sampledMoment S ((c : ℝ)*α) t H ≤
        (6+1024*D*((c : ℝ)+3)*DyadicLogLoss.logLoss (H : ℝ))*P*H := hb
    _ ≤ (C*P^ε)*P*H :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoeff hPpos.le) hHpos.le
    _ = C*P^(1+ε)*H := by rw [Real.rpow_add hPpos, Real.rpow_one]; ring

#print axioms sampled_second_moment_epsilon
end Waring.SampledQuadraticSecondAsymptotic
