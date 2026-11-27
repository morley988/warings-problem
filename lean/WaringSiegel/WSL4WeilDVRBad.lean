import WaringSiegel.WSL4WeilDVRBadRecursion
import WaringSiegel.WSL4WeilBadExponents

/-! # Arbitrary-twist cubic bounds at ramified exceptional primes

The unit contribution has square-root growth with a fixed local constant.
The nonunit contribution either vanishes or obeys the exact three-step
recurrence.  The resulting constant is independent of the additive character,
linear twist, and quotient exponent.
-/
noncomputable section
namespace WaringSiegel.WSL4Weil
open scoped BigOperators Classical
open IsLocalRing WSL4Local
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [HenselianLocalRing R] [Finite (ResidueField R)]
attribute [local instance] quotientFintype residueFintype

def cubicBadBoundConstant (R : Type*) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] : ℝ :=
  cubicBadMajorantConstant (Nat.card (ResidueField R)) (cubicUnitBoundConstant R)

theorem cubicBadBoundConstant_nonneg : 0≤cubicBadBoundConstant R := by
  unfold cubicBadBoundConstant cubicBadMajorantConstant cubicUnitBoundConstant
  positivity

theorem dvrCubicSum_ramified_bound
    {π : R} (hπ : Irreducible π) (h2 : (2:R)≠0) (h3 : (3:R)≠0)
    (r : ℕ) (ψ : AddChar (R ⧸ maximalIdeal R^r) ℂ) (hψ : ψ.IsPrimitive)
    {a : R} (ha : IsUnit a) (b : R) :
    ‖dvrCubicSum r ψ a b‖ ≤ cubicBadBoundConstant R*
      (Nat.card (ResidueField R) : ℝ)^(2*(r:ℝ)/3) := by
  let q : ℝ := Nat.card (ResidueField R)
  let C := cubicUnitBoundConstant R
  have hq : 2≤q := by
    dsimp [q]
    exact_mod_cast (show 2≤Nat.card (ResidueField R) by
      rw [Nat.card_eq_fintype_card]; exact Fintype.one_lt_card)
  have hC : 0≤C := by dsimp [C,cubicUnitBoundConstant]; positivity
  have H : ∀r : ℕ,∀ψ : AddChar (R ⧸ maximalIdeal R^r) ℂ,ψ.IsPrimitive →
      ∀a : R,IsUnit a → ∀b : R,
      ‖dvrCubicSum r ψ a b‖+3*C*q^((r:ℝ)/2)≤
        cubicBadMajorantConstant q C*q^(2*(r:ℝ)/3) := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
      intro ψ hψ a ha b
      by_cases hr : r<3
      · exact cubicBadMajorant_base q C _ hq hC r (by omega)
          (dvrCubicSum_trivial_norm_bound r ψ a b)
      obtain ⟨n,rfl⟩ : ∃n : ℕ,r=n+3 := ⟨r-3,by omega⟩
      have hu := dvrUnitCubicSum_uniform_bound hπ h2 h3 (n+3) (by omega) ψ hψ ha b
      by_cases hb : IsUnit b
      · have hz := dvrZeroCubicSum_unit_linear_zero hπ (n+2) (by omega) ψ hψ a hb
        rw [dvrCubicSum_split_units (n+3) (by omega) ψ a b,hz,add_zero]
        exact cubicBadMajorant_unit_case q C _ hq hC (n+3) hu
      · have hbm : b∈Ideal.span ({π} : Set R) := by
          rw [← hπ.maximalIdeal_eq]
          exact mem_nonunits_iff.mpr hb
        obtain ⟨c,rfl⟩ := Ideal.mem_span_singleton.mp hbm
        by_cases hc : IsUnit c
        · have hz := dvrZeroCubicSum_valuation_one_zero hπ (n+1) (by omega) ψ hψ a hc
          rw [dvrCubicSum_split_units (n+3) (by omega) ψ a (π*c),hz,add_zero]
          exact cubicBadMajorant_unit_case q C _ hq hC (n+3) hu
        · have hcm : c∈Ideal.span ({π} : Set R) := by
            rw [← hπ.maximalIdeal_eq]
            exact mem_nonunits_iff.mpr hc
          obtain ⟨d,rfl⟩ := Ideal.mem_span_singleton.mp hcm
          have hp : (scaledQuotientCharacter hπ 3 n ψ).IsPrimitive := by
            apply (quotient_character_primitive_iff_exact_conductor _ _).mpr
            exact scaledQuotientCharacter_conductor hπ 3 n ψ
              ((quotient_character_primitive_iff_exact_conductor _ _).mp hψ)
          have hi := ih n (by omega) (scaledQuotientCharacter hπ 3 n ψ) hp a ha d
          have hs : ‖dvrCubicSum (n+3) ψ a (π*(π*d))‖≤
              C*q^(((n+3:ℕ):ℝ)/2)+q^2*‖dvrCubicSum n (scaledQuotientCharacter hπ 3 n ψ) a d‖ := by
            rw [dvrCubicSum_split_units (n+3) (by omega) ψ a (π*(π*d))]
            have he : π*(π*d)=π^2*d := by ring
            rw [he,dvrZeroCubicSum_three_step hπ n ψ a d]
            apply (norm_add_le _ _).trans
            rw [norm_mul,norm_pow,Complex.norm_natCast]
            exact add_le_add (by simpa only [he] using hu) le_rfl
          exact cubicBadMajorant_recursion q C _ _ hq hC n hs hi
  have h := H r ψ hψ a ha b
  have ht : 0≤3*C*q^((r:ℝ)/2) := by positivity
  exact (le_add_of_nonneg_right ht).trans h

theorem dvrCubicSum_ramified_kappa_bound
    {π : R} (hπ : Irreducible π) (h2 : (2:R)≠0) (h3 : (3:R)≠0)
    (e : ℕ) (ψ : AddChar (R ⧸ maximalIdeal R^(e+1)) ℂ) (hψ : ψ.IsPrimitive)
    {a : R} (ha : IsUnit a) (b : R) :
    ‖dvrCubicSum (e+1) ψ a b‖ ≤ (Nat.card (ResidueField R) : ℝ)^(e+1)*
      cubicKappaLocal (Nat.card (ResidueField R)) (cubicBadBoundConstant R) false e := by
  have hq : 0<(Nat.card (ResidueField R) : ℝ) := by exact_mod_cast (Nat.card_pos (α:=ResidueField R))
  have he : (Nat.card (ResidueField R) : ℝ)^(e+1)*
      cubicKappaLocal (Nat.card (ResidueField R)) (cubicBadBoundConstant R) false e=
      cubicBadBoundConstant R*(Nat.card (ResidueField R) : ℝ)^(2*((e+1:ℕ):ℝ)/3) := by
    unfold cubicKappaLocal
    simp only [Bool.false_eq_true,if_false]
    rw [← Real.rpow_natCast,mul_left_comm,← Real.rpow_add hq]
    congr 1
    congr 1
    push_cast
    ring
  rw [he]
  exact dvrCubicSum_ramified_bound hπ h2 h3 (e+1) ψ hψ ha b
end WaringSiegel.WSL4Weil

#print axioms WaringSiegel.WSL4Weil.dvrCubicSum_ramified_bound
#print axioms WaringSiegel.WSL4Weil.dvrCubicSum_ramified_kappa_bound
