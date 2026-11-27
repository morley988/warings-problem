import Waring.RestrictedSmoothArcs

/-! # Disjointness of the actual reduced rational bands -/

noncomputable section
namespace Waring.RestrictedSmoothArcs

def rationalBand (r : ℚ) (δ : ℝ) : Set ℝ :=
  {x | |(r.den : ℝ)*x-(r.num : ℝ)| ≤ δ}

theorem rationalBand_eq_Icc (r : ℚ) (δ : ℝ) :
    rationalBand r δ = Set.Icc ((r : ℝ)-δ/(r.den : ℝ)) ((r : ℝ)+δ/(r.den : ℝ)) := by
  have hd : 0 < (r.den : ℝ) := by exact_mod_cast r.pos
  ext x
  simp only [rationalBand,Set.mem_setOf_eq,Set.mem_Icc,abs_le,Rat.cast_def]
  rw [← sub_div,← add_div,div_le_iff₀ hd,le_div_iff₀ hd]
  constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith

theorem rationalBand_measurable (r : ℚ) (δ : ℝ) : MeasurableSet (rationalBand r δ) := by
  rw [rationalBand_eq_Icc]
  exact measurableSet_Icc

/-- An integer determinant prevents two distinct reduced rationals from
sharing a band once the denominator and width satisfy the source scale. -/
theorem rationalBand_unique {Q δ : ℝ} (hδ : 0 ≤ δ) (hsmall : 4*Q*δ ≤ 1)
    {r s : ℚ} (hr : (r.den : ℝ) ≤ Q) (hs : (s.den : ℝ) ≤ Q) {x : ℝ}
    (hxr : x ∈ rationalBand r δ) (hxs : x ∈ rationalBand s δ) : r=s := by
  have hd : |((r.num*(s.den : ℤ)-s.num*(r.den : ℤ) : ℤ) : ℝ)| ≤
      ((s.den : ℝ)+(r.den : ℝ))*δ := by
    calc
      _ = |(s.den : ℝ)*((r.den : ℝ)*x-r.num)-
          (r.den : ℝ)*((s.den : ℝ)*x-s.num)| := by
        rw [← abs_neg]
        congr 1
        push_cast
        ring
      _ ≤ |(s.den : ℝ)*((r.den : ℝ)*x-r.num)|+
          |(r.den : ℝ)*((s.den : ℝ)*x-s.num)| := abs_sub _ _
      _ ≤ (s.den : ℝ)*δ+(r.den : ℝ)*δ := by
        simp only [abs_mul,abs_of_nonneg (show (0 : ℝ) ≤ (s.den : ℝ) from Nat.cast_nonneg _),
          abs_of_nonneg (show (0 : ℝ) ≤ (r.den : ℝ) from Nat.cast_nonneg _)]
        exact add_le_add (mul_le_mul_of_nonneg_left hxr (Nat.cast_nonneg _))
          (mul_le_mul_of_nonneg_left hxs (Nat.cast_nonneg _))
      _ = _ := by ring
  have hbound : ((s.den : ℝ)+(r.den : ℝ))*δ ≤ (Q+Q)*δ := by gcongr
  have hlt : |((r.num*(s.den : ℤ)-s.num*(r.den : ℤ) : ℤ) : ℝ)| < 1 := by
    nlinarith
  have hltZ : |r.num*(s.den : ℤ)-s.num*(r.den : ℤ)| < (1 : ℤ) := by
    exact_mod_cast hlt
  have he : r.num*(s.den : ℤ)-s.num*(r.den : ℤ)=0 := by
    have hbounds := abs_lt.mp hltZ
    omega
  exact Rat.eq_iff_mul_eq_mul.mpr (sub_eq_zero.mp he)

theorem rationalBand_disjoint {Q δ : ℝ} (hδ : 0 ≤ δ) (hsmall : 4*Q*δ ≤ 1)
    {r s : ℚ} (hr : (r.den : ℝ) ≤ Q) (hs : (s.den : ℝ) ≤ Q) (hne : r ≠ s) :
    Disjoint (rationalBand r δ) (rationalBand s δ) := by
  apply Set.disjoint_left.mpr
  intro x hxr hxs
  exact hne (rationalBand_unique hδ hsmall hr hs hxr hxs)

theorem rationalBand_subset_three_periods (r : ℚ) {δ : ℝ} (hδ : δ ≤ 1)
    (hr0 : (0 : ℝ) ≤ r) (hr1 : (r : ℝ) ≤ 1) :
    rationalBand r δ ⊆ Set.Icc (-1 : ℝ) 2 := by
  have hd : (1 : ℝ) ≤ r.den := by exact_mod_cast r.pos
  have hdp : 0 < (r.den : ℝ) := by exact_mod_cast r.pos
  have hdiv : δ/(r.den : ℝ) ≤ 1 := (div_le_one hdp).mpr (hδ.trans hd)
  rw [rationalBand_eq_Icc]
  intro x hx
  exact ⟨by linarith [hx.1],by linarith [hx.2]⟩

#print axioms rationalBand_disjoint
end Waring.RestrictedSmoothArcs
