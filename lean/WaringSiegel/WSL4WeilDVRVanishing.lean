import WaringSiegel.WSL4WeilDVRRecursion

/-! # Linear-dominant mixed cubic sums vanish at every positive precision -/
noncomputable section
namespace WaringSiegel.WSL4Weil
open scoped BigOperators Classical
open IsLocalRing WSL4Local

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Finite (ResidueField R)]
attribute [local instance] quotientFintype residueFintype

theorem dvrCubicSum_linear_dominant_zero
    {π : R} (hπ : Irreducible π) (r : ℕ) (hr : 1≤r)
    (ψ : AddChar (R ⧸ maximalIdeal R^r) ℂ) (hψ : ψ.IsPrimitive)
    {a b : R} (ha : a∈maximalIdeal R) (hb : IsUnit b) :
    dvrCubicSum r ψ a b=0 := by
  have ha0 := (residue_eq_zero_iff a).mpr ha
  have hb0 := (residue_ne_zero_iff_isUnit b).mpr hb
  by_cases hr2 : 2≤r
  · rw [dvrCubicSum_last_digit hπ r hr2 ψ hψ a b]
    simp only [ha0,mul_zero,zero_mul,zero_add,hb0,Finset.filter_False,Finset.sum_empty]
  · have he : r=1 := by omega
    subst r
    have hamk : Ideal.Quotient.mk (maximalIdeal R^1) a=0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (by simpa only [pow_one] using ha)
    have hbmk : Ideal.Quotient.mk (maximalIdeal R^1) b≠0 := by
      intro h
      apply hb0
      apply (residue_eq_zero_iff b).mpr
      simpa only [pow_one] using Ideal.Quotient.eq_zero_iff_mem.mp h
    unfold dvrCubicSum mixedCubicSum
    simp only [hamk,zero_mul,zero_add]
    simpa only [AddChar.mulShift_apply] using
      AddChar.sum_eq_zero_of_ne_one (hψ hbmk)

theorem dvrZeroCubicSum_norm_le (n : ℕ)
    (ψ : AddChar (R ⧸ maximalIdeal R^(n+1)) ℂ) (a b : R) :
    ‖dvrZeroCubicSum (n+1) (by omega) ψ a b‖ ≤ (Nat.card (ResidueField R) : ℝ)^n := by
  have hc := residue_reduction_fiber_card (R:=R) n 0
  simp only [Nat.card_eq_fintype_card,Fintype.card_subtype] at hc
  unfold dvrZeroCubicSum
  calc
    _ ≤ ((Finset.univ.filter (fun x : R ⧸ maximalIdeal R^(n+1) =>
        localResidueReduction _ (Ideal.pow_le_self (by omega)) x=0)).card : ℝ) := by
      exact (norm_sum_le _ _).trans_eq (by simp)
    _ = _ := by rw [Nat.card_eq_fintype_card]; exact_mod_cast hc

theorem dvrCubicSum_valuation_one_zero
    {π : R} (hπ : Irreducible π) (n : ℕ) (hn : 1≤n)
    (ψ : AddChar (R ⧸ maximalIdeal R^(n+2)) ℂ) (hψ : ψ.IsPrimitive)
    (h3 : IsUnit (3 : R)) {a b : R} (ha : IsUnit a) (hb : IsUnit b) :
    dvrCubicSum (n+2) ψ a (π*b)=0 := by
  have hπm : π∈maximalIdeal R := by
    rw [hπ.maximalIdeal_eq]
    exact Ideal.mem_span_singleton_self π
  rw [dvrCubicSum_eq_zero_residue_of_linear_mem hπ (n+2) (by omega) ψ hψ h3 ha
    ((maximalIdeal R).mul_mem_right b hπm)]
  rw [dvrZeroCubicSum_scale hπ n 1 ψ a (π*b) (π*a) b (by intro y; ring)]
  have hp : (scaledQuotientCharacter hπ 2 n ψ).IsPrimitive := by
    apply (quotient_character_primitive_iff_exact_conductor _ _).mpr
    exact scaledQuotientCharacter_conductor hπ 2 n ψ
      ((quotient_character_primitive_iff_exact_conductor _ _).mp hψ)
  rw [dvrCubicSum_linear_dominant_zero hπ n hn _ hp
    ((maximalIdeal R).mul_mem_right a hπm) hb, mul_zero]

theorem dvrCubicSum_precision_two_nonunit_linear
    {π : R} (hπ : Irreducible π)
    (ψ : AddChar (R ⧸ maximalIdeal R^2) ℂ) (hψ : ψ.IsPrimitive)
    (h3 : IsUnit (3 : R)) {a b : R} (ha : IsUnit a) (hb : b∈maximalIdeal R) :
    ‖dvrCubicSum 2 ψ a b‖ ≤ Nat.card (ResidueField R) := by
  rw [dvrCubicSum_eq_zero_residue_of_linear_mem hπ 2 (by decide) ψ hψ h3 ha hb]
  simpa only [pow_one] using dvrZeroCubicSum_norm_le 1 ψ a b

end WaringSiegel.WSL4Weil

#print axioms WaringSiegel.WSL4Weil.dvrCubicSum_linear_dominant_zero
#print axioms WaringSiegel.WSL4Weil.dvrCubicSum_valuation_one_zero
