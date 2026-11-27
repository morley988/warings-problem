import Waring.FixedCoefficientPhase
import Mathlib.Data.Nat.Prime.Basic

/-!
# The small smoothness range and nonnegativity of genuine exponents

For R<2 the positive R-smooth set is exactly {1} once P>=1. Its moments
are exactly one. This handles the small-R boundary of the doubling adapter
and proves that a genuinely admissible full exponent cannot be negative.
-/

noncomputable section
namespace Waring.SmoothMoments

theorem smoothNumbers_eq_one_of_lt_two {P R : ℝ} (hP : 1 ≤ P) (hR : R < 2) :
    smoothNumbers P R={1} := by
  classical
  ext n
  rw [Finset.mem_singleton]
  constructor
  · intro hn
    rcases mem_smoothNumbers.mp hn with ⟨⟨hnpos,hnP⟩,hsmooth⟩
    by_contra hn1
    have hprime := Nat.minFac_prime hn1
    have hbound := hsmooth n.minFac hprime (Nat.minFac_dvd n)
    have htwo : (2 : ℝ) ≤ n.minFac := by exact_mod_cast hprime.two_le
    linarith
  · rintro rfl
    apply mem_smoothNumbers.mpr
    refine ⟨⟨le_rfl,Nat.le_floor (by simpa using hP)⟩,?_⟩
    intro q hq hdiv
    have hq1 : q ≤ 1 := Nat.le_of_dvd (by norm_num) hdiv
    have hq2 := hq.two_le
    omega

theorem norm_smoothWeyl_eq_one_of_lt_two (k : ℕ) {P R : ℝ}
    (hP : 1 ≤ P) (hR : R < 2) (α : ℝ) : ‖smoothWeyl k P R α‖=1 := by
  simp only [smoothWeyl,smoothNumbers_eq_one_of_lt_two hP hR,Finset.sum_singleton,norm_phase]

theorem smoothMoment_eq_one_of_lt_two (k p : ℕ) {P R : ℝ}
    (hP : 1 ≤ P) (hR : R < 2) : smoothMoment k p P R=1 := by
  simp only [smoothMoment,norm_smoothWeyl_eq_one_of_lt_two k hP hR,one_pow]
  norm_num

/-- The actual uniform smooth moment assertion forces its full exponent
to be nonnegative; this is not an additional source-table assumption. -/
theorem admissibleExponent_nonneg {k p : ℕ} {lam : ℝ}
    (hadm : AdmissibleExponent k p lam) : 0 ≤ lam := by
  by_contra hnonneg
  have hlam : lam < 0 := lt_of_not_ge hnonneg
  let δ := -lam/2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  obtain ⟨η,hη,C,hC,P₀,hP₀,hbound⟩ := hadm δ hδ
  let P := max P₀ (max 1 ((2*C)^(1/δ)))
  have hPP₀ : P₀ ≤ P := le_max_left _ _
  have hP1 : 1 ≤ P := (le_max_left _ _).trans (le_max_right _ _)
  have hPp : 0 < P := zero_lt_one.trans_le hP1
  have hlarge : 2*C ≤ P^δ := NormalizedCoefficient.fixed_constant_rpow_bound
    (by positivity) hδ ((le_max_right _ _).trans (le_max_right _ _))
  have hb := hbound P hPP₀ 1 le_rfl (Real.one_le_rpow hP1 hη.le)
  rw [smoothMoment_eq_one_of_lt_two k p hP1 (by norm_num : (1 : ℝ) < 2)] at hb
  have he : lam+δ = -δ := by dsimp [δ]; ring
  rw [he,Real.rpow_neg hPp.le,← div_eq_mul_inv] at hb
  have hup : P^δ ≤ C := by
    simpa only [one_mul] using (le_div_iff₀ (Real.rpow_pos_of_pos hPp δ)).mp hb
  linarith

#print axioms smoothMoment_eq_one_of_lt_two
#print axioms admissibleExponent_nonneg
end Waring.SmoothMoments
