import WaringSiegel.WSL4WeilDVRVanishing
import WaringSiegel.WSL3CubicKappaLocal

/-! # Residue-field and low-precision bases for the sharp cubic local bound -/
noncomputable section
namespace WaringSiegel.WSL4Weil
open scoped BigOperators Classical
open IsLocalRing WSL4Local

theorem primitive_comp_ringEquiv
    {A B : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) (ψ : AddChar B ℂ) (hψ : ψ.IsPrimitive) :
    (ψ.compAddMonoidHom e.toAddMonoidHom).IsPrimitive := by
  intro a ha he
  have ha' : e a≠0 := by
    intro h
    apply ha
    apply e.injective
    simpa only [map_zero] using h
  apply hψ ha'
  ext y
  obtain ⟨x,rfl⟩ := e.surjective y
  have h := congrArg (fun χ : AddChar A ℂ => χ x) he
  change ψ (e (a*x))=1 at h
  change ψ (e a*e x)=1
  simpa only [map_mul] using h

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Finite (ResidueField R)]
attribute [local instance] quotientFintype residueFintype

theorem dvrCubicSum_trivial_norm_bound (r : ℕ)
    (ψ : AddChar (R ⧸ maximalIdeal R^r) ℂ) (a b : R) :
    ‖dvrCubicSum r ψ a b‖ ≤ (Nat.card (ResidueField R) : ℝ)^r := by
  unfold dvrCubicSum mixedCubicSum
  calc
    _ ≤ (Fintype.card (R ⧸ maximalIdeal R^r) : ℝ) := (norm_sum_le _ _).trans_eq (by simp)
    _ = _ := by rw [← Nat.card_eq_fintype_card,dvr_power_quotient_card,Nat.cast_pow]

theorem dvrCubicSum_precision_one_bound
    (ψ : AddChar (R ⧸ maximalIdeal R^1) ℂ) (hψ : ψ.IsPrimitive)
    (h3 : IsUnit (3 : R)) {a : R} (ha : IsUnit a) (b : R) :
    ‖dvrCubicSum 1 ψ a b‖ ≤ 2*Real.sqrt (Nat.card (ResidueField R)) := by
  let e : (R ⧸ maximalIdeal R^1) ≃+* ResidueField R := Ideal.quotEquivOfEq (pow_one _)
  let φ := ψ.compAddMonoidHom e.symm.toAddMonoidHom
  have hφp : φ.IsPrimitive := primitive_comp_ringEquiv e.symm ψ hψ
  have hφ : φ≠1 := by
    intro he
    apply hφp (one_ne_zero : (1:ResidueField R)≠0)
    simpa only [AddChar.mulShift_one] using he
  have hchar : ringChar (ResidueField R)≠3 := by
    intro he
    have hz := CharP.cast_eq_zero (ResidueField R) (ringChar (ResidueField R))
    rw [he] at hz
    have hne : (3 : ResidueField R)≠0 := by
      simpa only [map_ofNat] using (h3.map (residue R)).ne_zero
    exact hne hz
  have hcomp : φ.compAddMonoidHom e.toAddMonoidHom=ψ := by
    ext x
    exact congrArg ψ (e.symm_apply_apply x)
  have hs := mixedCubicSum_ringEquiv e φ (Ideal.Quotient.mk _ a) (Ideal.Quotient.mk _ b)
  rw [hcomp] at hs
  have hea : e (Ideal.Quotient.mk _ a)=residue R a := Ideal.quotEquivOfEq_mk _ _
  have heb : e (Ideal.Quotient.mk _ b)=residue R b := Ideal.quotEquivOfEq_mk _ _
  rw [hea,heb] at hs
  unfold dvrCubicSum
  rw [hs,Nat.card_eq_fintype_card]
  exact norm_sum_mixed_cubic_le_of_char_ne_three hchar hφ
    ((residue_ne_zero_iff_isUnit a).mpr ha) (residue R b)

theorem dvrCubicSum_precision_two_bound
    {π : R} (hπ : Irreducible π)
    (ψ : AddChar (R ⧸ maximalIdeal R^2) ℂ) (hψ : ψ.IsPrimitive)
    (h2 : IsUnit (2 : R)) (h3 : IsUnit (3 : R)) {a : R} (ha : IsUnit a) (b : R) :
    ‖dvrCubicSum 2 ψ a b‖ ≤ 2*Nat.card (ResidueField R) := by
  by_cases hb : IsUnit b
  · simpa only [pow_one] using
      dvrCubicSum_norm_le_two_pow_of_unit_linear hπ 1 1 (by decide) (by decide) ψ hψ h2 h3 ha hb
  · have hbm : b∈maximalIdeal R := mem_nonunits_iff.mpr hb
    exact (dvrCubicSum_precision_two_nonunit_linear hπ ψ hψ h3 ha hbm).trans
      (by linarith [Nat.cast_nonneg (α:=ℝ) (Nat.card (ResidueField R))])

end WaringSiegel.WSL4Weil

#print axioms WaringSiegel.WSL4Weil.dvrCubicSum_precision_one_bound
#print axioms WaringSiegel.WSL4Weil.dvrCubicSum_precision_two_bound
