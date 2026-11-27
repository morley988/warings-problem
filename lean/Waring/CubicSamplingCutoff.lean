import Waring.CubicCoefficientSampling

/-! # Elimination of the auxiliary cutoff in refined cubic sampling -/

noncomputable section

namespace Waring.CubicCoefficientSampling
open Waring.RationalHeight Waring.SampledLinearSecondMoment

def samplingCutoff (H N J : ℕ) : ℝ :=
  min (N:ℝ) (min (J:ℝ) (Real.sqrt ((N:ℝ)*J)/(4*Real.sqrt ((H:ℝ)^3))))

theorem samplingCutoff_spec (H N J : ℕ) (hH : 0 < H) (hN : 0 < N) (hJ : 0 < J) :
    0 < samplingCutoff H N J ∧ samplingCutoff H N J ≤ N ∧
      samplingCutoff H N J ≤ J ∧ samplingCutoff H N J ≤ Real.sqrt ((N:ℝ)*J) ∧
      2*samplingCutoff H N J*Real.sqrt ((H:ℝ)^3*((N:ℝ)*J))/((N:ℝ)*J) < 1 := by
  have hHp : (0:ℝ) < H := by exact_mod_cast hH
  have hNp : (0:ℝ) < N := by exact_mod_cast hN
  have hJp : (0:ℝ) < J := by exact_mod_cast hJ
  have hH1 : (1:ℝ) ≤ H := by exact_mod_cast hH
  have hU : 0 < (N:ℝ)*J := mul_pos hNp hJp
  have hR : 0 < Real.sqrt ((H:ℝ)^3) := Real.sqrt_pos.mpr (pow_pos hHp 3)
  have hS : 0 < Real.sqrt ((N:ℝ)*J) := Real.sqrt_pos.mpr hU
  have hR1 : 1 ≤ Real.sqrt ((H:ℝ)^3) :=
    Real.le_sqrt_of_sq_le (by simpa using one_le_pow₀ hH1 (n := 3))
  have hcap : 0 < Real.sqrt ((N:ℝ)*J)/(4*Real.sqrt ((H:ℝ)^3)) := by positivity
  have hYp : 0 < samplingCutoff H N J := lt_min hNp (lt_min hJp hcap)
  have hYN : samplingCutoff H N J ≤ (N:ℝ) := min_le_left _ _
  have hYJ : samplingCutoff H N J ≤ (J:ℝ) := (min_le_right _ _).trans (min_le_left _ _)
  have hYcap : samplingCutoff H N J ≤ Real.sqrt ((N:ℝ)*J)/(4*Real.sqrt ((H:ℝ)^3)) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hYroot : samplingCutoff H N J ≤ Real.sqrt ((N:ℝ)*J) := by
    apply hYcap.trans
    apply (div_le_iff₀ (by positivity : (0:ℝ)<4*Real.sqrt ((H:ℝ)^3))).mpr
    nlinarith
  refine ⟨hYp,hYN,hYJ,hYroot,?_⟩
  have hhalf : 2*samplingCutoff H N J*Real.sqrt ((H:ℝ)^3*((N:ℝ)*J))/((N:ℝ)*J) ≤ (1:ℝ)/2 := by
    calc
      _ ≤ 2*(Real.sqrt ((N:ℝ)*J)/(4*Real.sqrt ((H:ℝ)^3)))*
          Real.sqrt ((H:ℝ)^3*((N:ℝ)*J))/((N:ℝ)*J) := by
        apply div_le_div_of_nonneg_right _ hU.le
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hYcap (by norm_num)) (Real.sqrt_nonneg _)
      _ = (1:ℝ)/2 := by
        rw [Real.sqrt_mul (show (0:ℝ) ≤ (H:ℝ)^3 by positivity)]
        have hs := Real.sq_sqrt hU.le
        field_simp
        nlinarith
  linarith

theorem samplingCutoff_reciprocal (H N J : ℕ) (hH : 0 < H) (hN : 0 < N) (hJ : 0 < J) :
    1 / samplingCutoff H N J ≤
      1/(N:ℝ)+1/(J:ℝ)+4*Real.sqrt ((H:ℝ)^3)/Real.sqrt ((N:ℝ)*J) := by
  have hHp : (0:ℝ)<H := by exact_mod_cast hH
  have hNp : (0:ℝ)<N := by exact_mod_cast hN
  have hJp : (0:ℝ)<J := by exact_mod_cast hJ
  have hR : 0 < Real.sqrt ((H:ℝ)^3) := Real.sqrt_pos.mpr (pow_pos hHp 3)
  have hS : 0 < Real.sqrt ((N:ℝ)*J) := Real.sqrt_pos.mpr (mul_pos hNp hJp)
  have hn0 : 0 ≤ 1/(N:ℝ) := by positivity
  have hj0 : 0 ≤ 1/(J:ℝ) := by positivity
  have hq0 : 0 ≤ 4*Real.sqrt ((H:ℝ)^3)/Real.sqrt ((N:ℝ)*J) := by positivity
  unfold samplingCutoff
  by_cases hn : (N:ℝ) ≤ min (J:ℝ) (Real.sqrt ((N:ℝ)*J)/(4*Real.sqrt ((H:ℝ)^3)))
  · rw [min_eq_left hn]
    linarith
  · rw [min_eq_right (le_of_not_ge hn)]
    by_cases hj : (J:ℝ) ≤ Real.sqrt ((N:ℝ)*J)/(4*Real.sqrt ((H:ℝ)^3))
    · rw [min_eq_left hj]
      linarith
    · rw [min_eq_right (le_of_not_ge hj)]
      have heq : 1/(Real.sqrt ((N:ℝ)*J)/(4*Real.sqrt ((H:ℝ)^3))) =
          4*Real.sqrt ((H:ℝ)^3)/Real.sqrt ((N:ℝ)*J) := by field_simp
      rw [heq]
      linarith

/-- An unconditional finite refined coefficient-sampling inequality. The
only displayed nonuniform factor is the divisor count of a minimizing
denominator; `DivisorBound.lean` controls it by any positive power. -/
theorem cubic_sampling_explicit (α : ℝ) (H N J : ℕ) (c : ℕ → ℂ) (σ : ℕ → ℝ)
    (hH : 0 < H) (hN : 0 < N) (hJ : 0 < J) :
    ∃ r : ℚ, cost ((H:ℝ)^3*((N:ℝ)*J)) α r = height ((H:ℝ)^3*((N:ℝ)*J)) α ∧
      cubicSecondMoment α H N J c σ ≤
        2048*(2+Real.log (J:ℝ)/Real.log 2)*coefficientEnergy N c*(H:ℝ)*((N:ℝ)*J)*
          (1/(N:ℝ)+1/(J:ℝ)+4*Real.sqrt ((H:ℝ)^3)/Real.sqrt ((N:ℝ)*J)+
            (r.den.divisors.card:ℝ)*(H:ℝ)^2/height ((H:ℝ)^3*((N:ℝ)*J)) α) := by
  obtain ⟨hY,hYN,hYJ,hYr,hsize⟩ := samplingCutoff_spec H N J hH hN hJ
  obtain ⟨r,hr,hb⟩ := cubic_sampling_with_cutoff α H N J c σ hH hN hJ hY hYN hYJ hYr hsize
  refine ⟨r,hr,hb.trans ?_⟩
  have hW : 0 ≤ 2+Real.log (J:ℝ)/Real.log 2 := by
    have hJ1 : (1:ℝ)≤J := by exact_mod_cast hJ
    have hl := Real.log_nonneg hJ1
    have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  apply mul_le_mul_of_nonneg_left
  · exact add_le_add_right (samplingCutoff_reciprocal H N J hH hN hJ) _
  · have he := coefficientEnergy_nonneg N c
    positivity

#print axioms cubic_sampling_explicit

end Waring.CubicCoefficientSampling
