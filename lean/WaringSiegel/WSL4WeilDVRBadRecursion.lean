import WaringSiegel.WSL4WeilDVRUnits

/-! # Unit/nonunit decomposition at the exceptional cubic primes -/
noncomputable section
namespace WaringSiegel.WSL4Weil
open scoped BigOperators Classical
open IsLocalRing WSL4Local
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Finite (ResidueField R)]
attribute [local instance] quotientFintype residueFintype

theorem dvrCubicSum_split_units (r : ℕ) (hr : 1≤r)
    (ψ : AddChar (R ⧸ maximalIdeal R^r) ℂ) (a b : R) :
    dvrCubicSum r ψ a b=dvrUnitCubicSum r ψ a b+dvrZeroCubicSum r hr ψ a b := by
  unfold dvrCubicSum mixedCubicSum dvrUnitCubicSum dvrZeroCubicSum
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hu : IsUnit x
  · have hx : localResidueReduction (maximalIdeal R^r) (Ideal.pow_le_self (by omega)) x≠0 :=
      (localResidueReduction_ne_zero_iff_isUnit (maximalIdeal R^r) (Ideal.pow_le_self (by omega)) x).mpr hu
    simp only [if_pos hu,if_neg hx,add_zero]
  · have hx : localResidueReduction (maximalIdeal R^r) (Ideal.pow_le_self (by omega)) x=0 := by
      by_contra hx
      exact hu ((localResidueReduction_ne_zero_iff_isUnit (maximalIdeal R^r)
        (Ideal.pow_le_self (by omega)) x).mp hx)
    simp only [if_neg hu,if_pos hx,zero_add]

theorem dvrZeroCubicSum_unit_linear_zero
    {π : R} (hπ : Irreducible π) (n : ℕ) (hn : 1≤n)
    (ψ : AddChar (R ⧸ maximalIdeal R^(n+1)) ℂ) (hψ : ψ.IsPrimitive)
    (a : R) {b : R} (hb : IsUnit b) :
    dvrZeroCubicSum (n+1) (by omega) ψ a b=0 := by
  have hπm : π∈maximalIdeal R := by
    rw [hπ.maximalIdeal_eq]; exact Ideal.mem_span_singleton_self π
  rw [dvrZeroCubicSum_scale hπ n 0 ψ a b (π^2*a) b (by intro y; ring)]
  have hp : (scaledQuotientCharacter hπ 1 n ψ).IsPrimitive := by
    apply (quotient_character_primitive_iff_exact_conductor _ _).mpr
    exact scaledQuotientCharacter_conductor hπ 1 n ψ
      ((quotient_character_primitive_iff_exact_conductor _ _).mp hψ)
  have hpa : π^2*a∈maximalIdeal R := by
    apply (maximalIdeal R).mul_mem_right a
    simpa only [pow_two] using ((maximalIdeal R).mul_mem_right π hπm)
  rw [dvrCubicSum_linear_dominant_zero hπ n hn _ hp hpa hb,mul_zero]

theorem dvrZeroCubicSum_valuation_one_zero
    {π : R} (hπ : Irreducible π) (n : ℕ) (hn : 1≤n)
    (ψ : AddChar (R ⧸ maximalIdeal R^(n+2)) ℂ) (hψ : ψ.IsPrimitive)
    (a : R) {b : R} (hb : IsUnit b) :
    dvrZeroCubicSum (n+2) (by omega) ψ a (π*b)=0 := by
  have hπm : π∈maximalIdeal R := by
    rw [hπ.maximalIdeal_eq]; exact Ideal.mem_span_singleton_self π
  rw [dvrZeroCubicSum_scale hπ n 1 ψ a (π*b) (π*a) b (by intro y; ring)]
  have hp : (scaledQuotientCharacter hπ 2 n ψ).IsPrimitive := by
    apply (quotient_character_primitive_iff_exact_conductor _ _).mpr
    exact scaledQuotientCharacter_conductor hπ 2 n ψ
      ((quotient_character_primitive_iff_exact_conductor _ _).mp hψ)
  rw [dvrCubicSum_linear_dominant_zero hπ n hn _ hp
    ((maximalIdeal R).mul_mem_right a hπm) hb,mul_zero]

theorem dvrZeroCubicSum_three_step
    {π : R} (hπ : Irreducible π) (n : ℕ)
    (ψ : AddChar (R ⧸ maximalIdeal R^(n+3)) ℂ) (a b : R) :
    dvrZeroCubicSum (n+3) (by omega) ψ a (π^2*b)=
      (Nat.card (ResidueField R) : ℂ)^2*
        dvrCubicSum n (scaledQuotientCharacter hπ 3 n ψ) a b := by
  exact dvrZeroCubicSum_scale hπ n 2 ψ a (π^2*b) a b (by intro y; ring)

end WaringSiegel.WSL4Weil
#print axioms WaringSiegel.WSL4Weil.dvrCubicSum_split_units
#print axioms WaringSiegel.WSL4Weil.dvrZeroCubicSum_three_step
