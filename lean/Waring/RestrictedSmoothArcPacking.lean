import Waring.RestrictedSmoothArcSeparation

/-! # Packing separated rational bands into complete periods -/

noncomputable section
open scoped BigOperators
open MeasureTheory
namespace Waring.RestrictedSmoothArcs

theorem rationalBand_integral_eq (r : ℚ) {δ : ℝ} (hδ : 0 ≤ δ) (F : ℝ → ℝ) :
    (∫ x in rationalBand r δ, F x) =
      ∫ β in -(δ/(r.den : ℝ))..δ/(r.den : ℝ), F ((r : ℝ)+β) := by
  have hd : 0 ≤ δ/(r.den : ℝ) := div_nonneg hδ (Nat.cast_nonneg _)
  rw [intervalIntegral.integral_comp_add_left]
  rw [rationalBand_eq_Icc,integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le (by linarith : (r : ℝ)+-(δ/(r.den : ℝ)) ≤ r+δ/(r.den : ℝ))]
  simp only [sub_eq_add_neg]

theorem periodic_three_periods {F : ℝ → ℝ} (hF : Continuous F)
    (hper : Function.Periodic F 1) :
    (∫ x in (-1 : ℝ)..2, F x) = 3*∫ x in (0 : ℝ)..1, F x := by
  have h := hper.intervalIntegral_add_zsmul_eq (3 : ℤ) (-1)
    (fun a b => hF.intervalIntegrable a b)
  have hp := hper.intervalIntegral_add_eq (-1) 0
  norm_num only [zero_add,neg_add_cancel,zsmul_eq_mul,Int.cast_ofNat,mul_one,
    show (-1 : ℝ)+3=2 by norm_num] at h hp
  rw [hp] at h
  exact h

/-- The sum of the actual arc integrals is controlled by three full periods.
All denominators, center ranges and separation conditions are literal. -/
theorem sum_rationalBand_integrals_le (A : Finset ℚ) {Q δ : ℝ}
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hsmall : 4*Q*δ ≤ 1)
    (hA : ∀ r ∈ A, (r.den : ℝ) ≤ Q ∧ (0 : ℝ) ≤ r ∧ (r : ℝ) ≤ 1)
    {F : ℝ → ℝ} (hF : Continuous F) (hper : Function.Periodic F 1)
    (hF0 : ∀ x, 0 ≤ F x) :
    (∑ r ∈ A, ∫ x in rationalBand r δ, F x) ≤
      3*∫ x in (0 : ℝ)..1, F x := by
  have hsub : (⋃ r ∈ A, rationalBand r δ) ⊆ Set.Icc (-1 : ℝ) 2 := by
    intro x hx
    obtain ⟨r,hr,hx⟩ := Set.mem_iUnion₂.mp hx
    exact rationalBand_subset_three_periods r hδ1 (hA r hr).2.1 (hA r hr).2.2 hx
  have hpair : Set.Pairwise (↑A : Set ℚ) (fun r s => Disjoint (rationalBand r δ) (rationalBand s δ)) := by
    intro r hr s hs hne
    exact rationalBand_disjoint hδ hsmall (hA r hr).1 (hA s hs).1 hne
  have hint : ∀ r ∈ A, IntegrableOn F (rationalBand r δ) := by
    intro r hr
    exact hF.integrableOn_Icc.mono_set
      (rationalBand_subset_three_periods r hδ1 (hA r hr).2.1 (hA r hr).2.2)
  calc
    _ = ∫ x in ⋃ r ∈ A, rationalBand r δ, F x :=
      (integral_biUnion_finset A (fun r _ => rationalBand_measurable r δ) hpair hint).symm
    _ ≤ ∫ x in Set.Icc (-1 : ℝ) 2, F x :=
      setIntegral_mono_set hF.integrableOn_Icc (Filter.Eventually.of_forall hF0)
        (Filter.Eventually.of_forall (fun x hx => hsub hx))
    _ = ∫ x in (-1 : ℝ)..2, F x := by
      rw [integral_Icc_eq_integral_Ioc,intervalIntegral.integral_of_le (by norm_num)]
    _ = _ := periodic_three_periods hF hper

#print axioms sum_rationalBand_integrals_le
end Waring.RestrictedSmoothArcs
