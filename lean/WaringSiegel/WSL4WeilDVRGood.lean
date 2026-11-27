import WaringSiegel.WSL4WeilDVRGoodBase
import WaringSiegel.WSL4WeilGoodExponents

/-! # Sharp arbitrary-linear-twist cubic bounds at every good prime power

This combines the actual finite-field Weil bound, exact stationary-point
count, linear-dominant cancellation, and exact three-step recursion.
-/
noncomputable section
namespace WaringSiegel.WSL4Weil
open scoped BigOperators Classical
open IsLocalRing WSL4Local

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Finite (ResidueField R)]
attribute [local instance] quotientFintype residueFintype

theorem dvrCubicSum_good_bound
    {π : R} (hπ : Irreducible π)
    (h2 : IsUnit (2 : R)) (h3 : IsUnit (3 : R))
    (r : ℕ) (ψ : AddChar (R ⧸ maximalIdeal R^r) ℂ) (hψ : ψ.IsPrimitive)
    {a : R} (ha : IsUnit a) (b : R) :
    ‖dvrCubicSum r ψ a b‖ ≤ cubicGoodMajorant (Nat.card (ResidueField R)) r := by
  let q : ℝ := Nat.card (ResidueField R)
  have hq : 0<q := by dsimp [q]; exact_mod_cast (Nat.card_pos (α:=ResidueField R))
  have hq1 : 1≤q := by
    dsimp [q]
    exact_mod_cast (show 1≤Nat.card (ResidueField R) from Nat.card_pos)
  have H : ∀ r : ℕ, ∀ ψ : AddChar (R ⧸ maximalIdeal R^r) ℂ, ψ.IsPrimitive →
      ∀ a : R, IsUnit a → ∀ b : R, ‖dvrCubicSum r ψ a b‖ ≤ cubicGoodMajorant q r := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
      intro ψ hψ a ha b
      by_cases hr : r<3
      · interval_cases r
        · have ht := dvrCubicSum_trivial_norm_bound 0 ψ a b
          norm_num [cubicGoodMajorant,cubicGoodExponent] at ht ⊢
          linarith
        · simpa [cubicGoodMajorant,cubicGoodExponent,Real.sqrt_eq_rpow,q] using
            dvrCubicSum_precision_one_bound ψ hψ h3 ha b
        · simpa [cubicGoodMajorant,cubicGoodExponent,q] using
            dvrCubicSum_precision_two_bound hπ ψ hψ h2 h3 ha b
      have hr3 : 3≤r := by omega
      by_cases hb : IsUnit b
      · have hn : 1≤r/2 := by omega
        have hnm : r/2≤r-r/2 := by omega
        have he : r/2+(r-r/2)=r := by omega
        have hu := dvrCubicSum_norm_le_two_pow_of_unit_linear hπ (r/2) (r-r/2) hn hnm
        rw [he] at hu
        have hbnd := hu ψ hψ h2 h3 ha hb
        apply hbnd.trans
        change 2*q^(r-r/2) ≤ 2*q^(cubicGoodExponent r)
        rw [← Real.rpow_natCast q (r-r/2)]
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hq1 (cubicGoodExponent_ceil_half r (by omega)))
          (by norm_num)
      · obtain ⟨n,rfl⟩ : ∃ n : ℕ, r=n+3 := ⟨r-3,by omega⟩
        have hbm : b∈Ideal.span ({π} : Set R) := by
          rw [← hπ.maximalIdeal_eq]
          exact mem_nonunits_iff.mpr hb
        obtain ⟨c,rfl⟩ := Ideal.mem_span_singleton.mp hbm
        by_cases hc : IsUnit c
        · have hv := dvrCubicSum_valuation_one_zero hπ (n+1) (by omega)
          have he : n+1+2=n+3 := by omega
          rw [he] at hv
          rw [hv ψ hψ h3 ha hc,norm_zero]
          unfold cubicGoodMajorant
          positivity
        · have hcm : c∈Ideal.span ({π} : Set R) := by
            rw [← hπ.maximalIdeal_eq]
            exact mem_nonunits_iff.mpr hc
          obtain ⟨d,rfl⟩ := Ideal.mem_span_singleton.mp hcm
          have hp : (scaledQuotientCharacter hπ 3 n ψ).IsPrimitive := by
            apply (quotient_character_primitive_iff_exact_conductor _ _).mpr
            exact scaledQuotientCharacter_conductor hπ 3 n ψ
              ((quotient_character_primitive_iff_exact_conductor _ _).mp hψ)
          have hbnd := ih n (by omega) (scaledQuotientCharacter hπ 3 n ψ) hp a ha d
          rw [show π*(π*d)=π^2*d by ring,
            dvrCubicSum_three_step hπ n ψ hψ h3 ha d,norm_mul,norm_pow,Complex.norm_natCast]
          change q^2*‖dvrCubicSum n (scaledQuotientCharacter hπ 3 n ψ) a d‖ ≤
            cubicGoodMajorant q (n+3)
          rw [cubicGoodMajorant_add_three q hq n]
          exact mul_le_mul_of_nonneg_left hbnd (sq_nonneg q)
  exact H r ψ hψ a ha b

theorem dvrCubicSum_good_kappa_bound
    {π : R} (hπ : Irreducible π)
    (h2 : IsUnit (2 : R)) (h3 : IsUnit (3 : R))
    (e : ℕ) (ψ : AddChar (R ⧸ maximalIdeal R^(e+1)) ℂ) (hψ : ψ.IsPrimitive)
    {a : R} (ha : IsUnit a) (b : R) (C : ℝ) :
    ‖dvrCubicSum (e+1) ψ a b‖ ≤ (Nat.card (ResidueField R) : ℝ)^(e+1)*
      cubicKappaLocal (Nat.card (ResidueField R)) C true e := by
  rw [← cubicGoodMajorant_eq_norm_kappa _ C (by exact_mod_cast (Nat.card_pos (α:=ResidueField R))) e]
  exact dvrCubicSum_good_bound hπ h2 h3 (e+1) ψ hψ ha b

end WaringSiegel.WSL4Weil

#print axioms WaringSiegel.WSL4Weil.dvrCubicSum_good_bound
#print axioms WaringSiegel.WSL4Weil.dvrCubicSum_good_kappa_bound
