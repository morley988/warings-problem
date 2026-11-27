import Waring.SampledQuadratic
import Waring.DivisorBound
import Waring.DyadicLogLoss

/-!
# The sampled quadratic fourth moment with a uniform epsilon loss

The actual divisor bound and logarithmic estimates discharge every analytic
premise in the explicit finite theorem. The shift range is allowed to grow
as any fixed power `H ≤ P^B`. Constants depend only on that power, the fixed
integer leading coefficient and epsilon, and are uniform in the real phase,
all linear modulations and all sampled integer intervals.
-/

noncomputable section

open scoped BigOperators

namespace Waring.SampledQuadraticAsymptotic

theorem combine_log_factors {C D F E X Y : ℝ}
    (hC : 0 ≤ C) (hD : 1 ≤ D) (hF : 1 ≤ F) (hE : E ≤ 2 * F)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    C * F ^ 2 * (X + 4 * (256 * D * E) * F * X + 24 * (256 * D * E) * Y) ≤
      (C * 12288) * (D * F ^ 4) * (X + Y) := by
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  have hF0 : 0 ≤ F := zero_le_one.trans hF
  have hF2 : 1 ≤ F ^ 2 := by nlinarith
  have hFF : F ≤ F ^ 2 := by nlinarith
  have hDF : 1 ≤ D * F ^ 2 := by nlinarith
  have hK : 256 * D * E ≤ 512 * D * F := by
    have hh := mul_le_mul_of_nonneg_left hE (show 0 ≤ 256 * D by positivity)
    nlinarith
  have hfirst : 1 + 4 * (256 * D * E) * F ≤ 12288 * D * F ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right hK (show 0 ≤ 4 * F by positivity)
    nlinarith
  have hsecond : 24 * (256 * D * E) ≤ 12288 * D * F ^ 2 := by
    calc
      _ ≤ 12288 * D * F := by nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_left hFF (by positivity)
  have hinner : X + 4 * (256 * D * E) * F * X + 24 * (256 * D * E) * Y ≤
      (12288 * D * F ^ 2) * (X + Y) := by
    calc
      _ = (1 + 4 * (256 * D * E) * F) * X + (24 * (256 * D * E)) * Y := by ring
      _ ≤ (12288 * D * F ^ 2) * X + (12288 * D * F ^ 2) * Y :=
        add_le_add (mul_le_mul_of_nonneg_right hfirst hX)
          (mul_le_mul_of_nonneg_right hsecond hY)
      _ = _ := by ring
  have hh := mul_le_mul_of_nonneg_left hinner (mul_nonneg hC (sq_nonneg F))
  convert hh using 1
  ring

/-- Bounding the polynomial-sized divisor cutoff while retaining the exact
real exponent. -/
theorem cutoff_power_bound {P H B δ : ℝ} (hP : 1 ≤ P) (hH : 0 ≤ H)
    (hHB : H ≤ P ^ B) (hδ : 0 ≤ δ) :
    (2 * H * P) ^ δ ≤ (2 : ℝ) ^ δ * P ^ ((B + 1) * δ) := by
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hbase : 2 * H * P ≤ 2 * P ^ (B + 1) := by
    calc
      2 * H * P ≤ 2 * P ^ B * P :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hHB (by norm_num)) hPpos.le
      _ = _ := by rw [Real.rpow_add hPpos, Real.rpow_one]; ring
  calc
    _ ≤ (2 * P ^ (B + 1)) ^ δ :=
      Real.rpow_le_rpow (by positivity) hbase hδ
    _ = _ := by
      rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hPpos.le _),
        ← Real.rpow_mul hPpos.le]

/-- Fully proved Q5 in the manuscript's epsilon-loss form, for actual
quadratic exponential sums. There is no divisor, pointwise, reciprocal-sum,
short-height counting, or transference estimate among the hypotheses.
-/
theorem sampled_fourth_moment_epsilon (B : ℝ) (hB : 0 ≤ B) (c : ℕ) (hc : 0 < c)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 2 ≤ P → ∀ H : ℝ, 1 ≤ H → H ≤ P ^ B →
      ∀ α : ℝ, ∀ s : Finset ℕ, ∀ a b : ℕ → ℤ, ∀ t : ℕ → ℝ,
      (∀ h ∈ s, 0 < h ∧ (h : ℝ) ≤ H) →
      (∀ h ∈ s, a h ≤ b h) →
      (∀ h ∈ s, (((b h + 1 - a h).toNat : ℕ) : ℝ) ≤ P) →
      let L := RationalHeight.height (H * P ^ 2) α
      (∑ h ∈ s, ‖∑ z ∈ Finset.Icc (a h) (b h),
        QuadraticModulation.e ((c : ℝ) * ((h : ℝ) * α) * (z : ℝ) ^ 2 + t h * z)‖ ^ 4) ≤
        C * P ^ ε * (H * P ^ 2 + P ^ 4 * min (H / L) (H ^ 2 / L ^ 2)) := by
  let δ := ε / (2 * (B + 1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hδeq : (B + 1) * δ = ε / 2 := by dsimp [δ]; field_simp
  obtain ⟨Cd, hCd, hdiv⟩ := DivisorBound.divisor_count_le_cutoff_rpow hδ
  have hCd1 : 1 ≤ Cd := by
    have hh := hdiv 1 le_rfl 1 (by decide) (by norm_num)
    simpa using hh
  obtain ⟨Cl, hCl, hlog⟩ := DyadicLogLoss.logLoss_pow_le_rpow 4 (half_pos hε)
  let C0 : ℝ := 1179648 * (c : ℝ) ^ 2
  let C : ℝ := (C0 * 12288) * (Cd * (2 : ℝ) ^ δ * Cl)
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hC0 : 0 < C0 := by dsimp [C0]; positivity
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro P hP H hH hHB α s a b t hs hab hlength
  let L := RationalHeight.height (H * P ^ 2) α
  let F := 2 + Real.log P / Real.log 2
  let E := 2 + 2 * Real.log P / Real.log 2
  let D := Cd * (2 * H * P) ^ δ
  let X := H * P ^ 2
  let Y := P ^ 4 * min (H / L) (H ^ 2 / L ^ 2)
  have hP1 : 1 ≤ P := (by norm_num : (1 : ℝ) ≤ 2).trans hP
  have hPpos : 0 < P := zero_lt_one.trans_le hP1
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hcut : 1 ≤ 2 * H * P := by nlinarith
  have hcutpow : 1 ≤ (2 * H * P) ^ δ := Real.one_le_rpow hcut hδ.le
  have hD1 : 1 ≤ D := by dsimp [D]; nlinarith
  have hD0 : 0 ≤ D := zero_le_one.trans hD1
  have hF1 : 1 ≤ F := by
    have hl : 0 ≤ Real.log P := Real.log_nonneg hP1
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    dsimp [F]
    have hh : 0 ≤ Real.log P / Real.log 2 := div_nonneg hl hl2.le
    linarith
  have hE : E ≤ 2 * F := DyadicLogLoss.doubled_log_le P
  have hLpos : 0 < L := RationalHeight.height_pos _ _
  have hX0 : 0 ≤ X := by dsimp [X]; positivity
  have hY0 : 0 ≤ Y := by dsimp [Y]; positivity
  have hdivD : ∀ n ∈ Finset.Icc 1 ⌊2 * H * P⌋₊, (n.divisors.card : ℝ) ≤ D := by
    intro n hn
    rcases Finset.mem_Icc.mp hn with ⟨hnpos, hnupper⟩
    exact hdiv (2 * H * P) hcut n hnpos
      ((show (n : ℝ) ≤ ⌊2 * H * P⌋₊ by exact_mod_cast hnupper).trans
        (Nat.floor_le (zero_le_one.trans hcut)))
  have hDpower : D ≤ (Cd * (2 : ℝ) ^ δ) * P ^ (ε / 2) := by
    have hh := mul_le_mul_of_nonneg_left (cutoff_power_bound hP1 hH0 hHB hδ.le) hCd.le
    rw [hδeq] at hh
    simpa only [D, mul_assoc] using hh
  have hFpower : F ^ 4 ≤ Cl * P ^ (ε / 2) := hlog P hP1
  have hpower : D * F ^ 4 ≤ (Cd * (2 : ℝ) ^ δ * Cl) * P ^ ε := by
    calc
      D * F ^ 4 ≤ ((Cd * (2 : ℝ) ^ δ) * P ^ (ε / 2)) * (Cl * P ^ (ε / 2)) :=
        mul_le_mul hDpower hFpower (pow_nonneg (zero_le_one.trans hF1) _) (by positivity)
      _ = (Cd * (2 : ℝ) ^ δ * Cl) * (P ^ (ε / 2) * P ^ (ε / 2)) := by ring
      _ = _ := by rw [← Real.rpow_add hPpos]; congr 2 <;> ring
  have hsample := SampledQuadratic.sampled_fourth_moment s a b t c (α := α) hc hH hP hD0 hs hab hlength hdivD
  calc
    _ ≤ (C0 * F ^ 2) * (H * P ^ 2 + P ^ 4 *
        (4 * (256 * D * E) * H / P ^ 2 * F + 24 * (256 * D * E) *
          min (H / L) (H ^ 2 / L ^ 2))) := hsample
    _ = C0 * F ^ 2 * (X + 4 * (256 * D * E) * F * X + 24 * (256 * D * E) * Y) := by
      dsimp [X, Y]
      field_simp
      ring
    _ ≤ (C0 * 12288) * (D * F ^ 4) * (X + Y) :=
      combine_log_factors hC0.le hD1 hF1 hE hX0 hY0
    _ ≤ (C0 * 12288) * ((Cd * (2 : ℝ) ^ δ * Cl) * P ^ ε) * (X + Y) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpower (by positivity)) (add_nonneg hX0 hY0)
    _ = _ := by dsimp [C]; ring

#print axioms sampled_fourth_moment_epsilon

end Waring.SampledQuadraticAsymptotic
