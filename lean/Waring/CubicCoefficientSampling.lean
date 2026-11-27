import Waring.CubicHeightSampling

/-!
# Refined coefficient sampling: a finite estimate for actual exponential sums

The explicit cutoff version below combines the proved linear second-moment
estimate with actual rational-height sampling along cubes. Constants and the
divisor factor remain displayed before asymptotic simplification.
-/

noncomputable section
open scoped BigOperators

namespace Waring.CubicCoefficientSampling
open Waring.RationalHeight Waring.SampledLinearSecondMoment Waring.QuadraticModulation

def cubicSecondMoment (α : ℝ) (H N J : ℕ) (c : ℕ → ℂ) (σ : ℕ → ℝ) : ℝ :=
  ∑ h ∈ Finset.Icc 1 H, ∑ j ∈ Finset.range J,
    ‖∑ n ∈ Finset.range N, c n * e (α*(h:ℝ)^3*((j:ℝ)+σ h)*n)‖^2

theorem cubic_sampling_with_cutoff (α : ℝ) (H N J : ℕ) (c : ℕ → ℂ) (σ : ℕ → ℝ)
    (hH : 0 < H) (hN : 0 < N) (hJ : 0 < J) {Y : ℝ} (hY : 0 < Y)
    (hYN : Y ≤ N) (hYJ : Y ≤ J) (hYroot : Y ≤ Real.sqrt ((N:ℝ)*J))
    (hsize : 2*Y*Real.sqrt ((H:ℝ)^3*((N:ℝ)*J))/((N:ℝ)*J) < 1) :
    ∃ r : ℚ, cost ((H:ℝ)^3*((N:ℝ)*J)) α r = height ((H:ℝ)^3*((N:ℝ)*J)) α ∧
      cubicSecondMoment α H N J c σ ≤
        2048*(2+Real.log (J:ℝ)/Real.log 2)*coefficientEnergy N c*(H:ℝ)*((N:ℝ)*J)*
          (1/Y+(r.den.divisors.card:ℝ)*(H:ℝ)^2/height ((H:ℝ)^3*((N:ℝ)*J)) α) := by
  let U : ℝ := (N:ℝ)*J
  let W : ℝ := 2+Real.log (J:ℝ)/Real.log 2
  let E : ℝ := coefficientEnergy N c
  let K : ℝ := 256*W*E
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hJ1 : (1:ℝ) ≤ J := by exact_mod_cast hJ
  have hU : 1 ≤ U := one_le_mul_of_one_le_of_one_le hN1 hJ1
  have hUp : 0 < U := zero_lt_one.trans_le hU
  have hW : 0 ≤ W := by
    have hl := Real.log_nonneg hJ1
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    dsimp [W]
    positivity
  have hE : 0 ≤ E := coefficientEnergy_nonneg N c
  have hK : 0 ≤ K := by dsimp [K]; positivity
  obtain ⟨r, hr, hrecip⟩ := CubicHeightSampling.cubic_reciprocal_sum H hH hU hY hsize
  refine ⟨r, hr, ?_⟩
  let L := height ((H:ℝ)^3*U) α
  let D : ℝ := r.den.divisors.card
  have hL : 0 < L := height_pos _ _
  have hcard : ((Finset.Icc 1 H).card : ℝ) = H := by simp
  have hsingle (h : ℕ) :
      (∑ j ∈ Finset.range J,
        ‖∑ n ∈ Finset.range N, c n*e (α*(h:ℝ)^3*((j:ℝ)+σ h)*n)‖^2) ≤
        K*(U/height U (α*(h:ℝ)^3)+(N:ℝ)+J+height U (α*(h:ℝ)^3)) := by
    have hh := sampledSecondMoment_shifted_intrinsic_real_log (α*(h:ℝ)^3) (σ h) N J c hN hJ
    convert hh using 1 <;> dsimp [K,U,W,E] <;> ring
  have hsumheight : (∑ h ∈ Finset.Icc 1 H, height U (α*(h:ℝ)^3)) ≤ (H:ℝ)*Real.sqrt U := by
    calc
      _ ≤ ∑ h ∈ Finset.Icc 1 H, Real.sqrt U :=
        Finset.sum_le_sum (fun h _ => height_le_sqrt hU _)
      _ = _ := by simp
  have hsumformula : (∑ h ∈ Finset.Icc 1 H,
      (U/height U (α*(h:ℝ)^3)+(N:ℝ)+J+height U (α*(h:ℝ)^3))) =
      U*(∑ h ∈ Finset.Icc 1 H, 1/height U (α*(h:ℝ)^3)) +
        (H:ℝ)*((N:ℝ)+J) + ∑ h ∈ Finset.Icc 1 H, height U (α*(h:ℝ)^3) := by
    simp only [div_eq_mul_inv, one_mul, Finset.sum_add_distrib]
    rw [← Finset.mul_sum]
    simp only [Finset.sum_const, nsmul_eq_mul, hcard]
    ring
  have hNbound : (N:ℝ) ≤ U/Y := by
    apply (le_div_iff₀ hY).mpr
    dsimp [U]
    exact mul_le_mul_of_nonneg_left hYJ (by positivity)
  have hJbound : (J:ℝ) ≤ U/Y := by
    apply (le_div_iff₀ hY).mpr
    dsimp [U]
    have hh := mul_le_mul_of_nonneg_right hYN (show (0:ℝ) ≤ J by positivity)
    nlinarith
  have hrootbound : Real.sqrt U ≤ U/Y := by
    apply (le_div_iff₀ hY).mpr
    have hs := Real.sq_sqrt hUp.le
    have hh := mul_le_mul_of_nonneg_left hYroot (Real.sqrt_nonneg U)
    nlinarith
  have hrest : (H:ℝ)*((N:ℝ)+J)+(H:ℝ)*Real.sqrt U ≤ 3*(H:ℝ)*(U/Y) := by
    have hh : (N:ℝ)+J+Real.sqrt U ≤ 3*(U/Y) := by linarith
    have hm := mul_le_mul_of_nonneg_left hh (show (0:ℝ)≤H by positivity)
    nlinarith
  have hshape : (∑ h ∈ Finset.Icc 1 H,
      (U/height U (α*(h:ℝ)^3)+(N:ℝ)+J+height U (α*(h:ℝ)^3))) ≤
      8*(H:ℝ)*U*(1/Y+D*(H:ℝ)^2/L) := by
    rw [hsumformula]
    calc
      _ ≤ U*((H:ℝ)/Y+8*D*(H:ℝ)^3/L)+(H:ℝ)*((N:ℝ)+J)+(H:ℝ)*Real.sqrt U := by
        apply add_le_add
        · exact add_le_add_right (mul_le_mul_of_nonneg_left hrecip hUp.le) _
        · exact hsumheight
      _ ≤ U*((H:ℝ)/Y+8*D*(H:ℝ)^3/L)+3*(H:ℝ)*(U/Y) := by linarith
      _ = 4*(H:ℝ)*U/Y+8*D*(H:ℝ)^3*U/L := by ring
      _ ≤ 8*(H:ℝ)*U/Y+8*D*(H:ℝ)^3*U/L := by
        have hh : 4*(H:ℝ)*U ≤ 8*(H:ℝ)*U :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (by norm_num : (4:ℝ) ≤ 8) (by positivity)) hUp.le
        exact add_le_add_right (div_le_div_of_nonneg_right hh hY.le) _
      _ = _ := by ring
  calc
    cubicSecondMoment α H N J c σ ≤ K * ∑ h ∈ Finset.Icc 1 H,
        (U/height U (α*(h:ℝ)^3)+(N:ℝ)+J+height U (α*(h:ℝ)^3)) := by
      unfold cubicSecondMoment
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun h _ => hsingle h)
    _ ≤ K*(8*(H:ℝ)*U*(1/Y+D*(H:ℝ)^2/L)) := mul_le_mul_of_nonneg_left hshape hK
    _ = _ := by dsimp [K,W,E,U,D,L]; ring

#print axioms cubic_sampling_with_cutoff

end Waring.CubicCoefficientSampling
