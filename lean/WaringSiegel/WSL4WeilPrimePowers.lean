import WaringSiegel.WSL4WeilDVRBad
import WaringSiegel.WSL3CubicKappaIdeal

/-! # Literal cubic sums with arbitrary twists on number-field prime powers -/
noncomputable section
namespace WaringSiegel.WSL4Weil
open scoped BigOperators Classical NumberField
open IsLocalRing
variable {K : Type*} [Field K] [NumberField K]
attribute [local instance] quotientFintype residueFintype

def cubicTwistExceptionalConstant (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : ℝ :=
  cubicBadBoundConstant (v.adicCompletionIntegers K)

theorem cubicTwistExceptionalConstant_pos
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : 0<cubicTwistExceptionalConstant v := by
  letI := completionIntegers_residueFinite v
  have hq : 0<(Nat.card (ResidueField (v.adicCompletionIntegers K)) : ℝ) := by
    exact_mod_cast (Nat.card_pos (α:=ResidueField (v.adicCompletionIntegers K)))
  unfold cubicTwistExceptionalConstant cubicBadBoundConstant cubicBadMajorantConstant cubicUnitBoundConstant
  positivity

theorem cubicTwistExceptionalConstant_nonneg
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : 0≤cubicTwistExceptionalConstant v := by
  exact (cubicTwistExceptionalConstant_pos v).le

theorem two_isUnit_of_six_residue_ne_zero
    {R : Type*} [CommRing R] [IsLocalRing R]
    (h6 : (6 : ResidueField R)≠0) : IsUnit (2:R) := by
  apply (residue_ne_zero_iff_isUnit (2:R)).mp
  simp only [map_ofNat]
  intro h2
  apply h6
  calc
    (6 : ResidueField R)=2*3 := by ring
    _ = 0 := by rw [h2,zero_mul]

theorem twistedCubicSum_prime_power_bound
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (e : ℕ)
    [Fintype (𝓞 K ⧸ v.asIdeal^(e+1))]
    (ψ χ : AddChar (𝓞 K ⧸ v.asIdeal^(e+1)) ℂ) (hψ : ψ.IsPrimitive) :
    ‖twistedPowerSum ψ χ 3‖ ≤ (Ideal.absNorm v.asIdeal : ℝ)^(e+1)*
      cubicKappaLocal (Ideal.absNorm v.asIdeal) (cubicTwistExceptionalConstant v)
        (cubicKappaGood v) e := by
  letI := completionIntegers_henselianLocalRing v
  letI := completionIntegers_residueFinite v
  letI := completionIntegers_charZero v
  let R := v.adicCompletionIntegers K
  let E := primePowerCompletionEquiv v (e+1)
  let φ := ψ.compAddMonoidHom E.symm.toAddMonoidHom
  let η := χ.compAddMonoidHom E.symm.toAddMonoidHom
  have hφ : φ.IsPrimitive := primitive_comp_ringEquiv E.symm ψ hψ
  have he : twistedPowerSum φ η 3=twistedPowerSum ψ χ 3 :=
    twistedPowerSum_ringEquiv E.symm ψ χ 3
  obtain ⟨b,hb⟩ := twistedPowerSum_eq_mixedCubicSum φ η hφ
  obtain ⟨b,rfl⟩ := Ideal.Quotient.mk_surjective b
  rw [← he,hb]
  change ‖dvrCubicSum (e+1) φ 1 b‖≤_
  obtain ⟨π,hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  by_cases h6 : (6 : ResidueField R)≠0
  · have h := dvrCubicSum_good_kappa_bound hπ
      (two_isUnit_of_six_residue_ne_zero h6) (three_isUnit_of_six_residue_ne_zero h6)
      e φ hφ isUnit_one b (cubicTwistExceptionalConstant v)
    simpa only [R,completion_residue_card_eq_absNorm,cubicKappaGood,decide_eq_true h6] using h
  · have h := dvrCubicSum_ramified_kappa_bound hπ (by norm_num) (by norm_num)
      e φ hφ isUnit_one b
    simpa only [R,completion_residue_card_eq_absNorm,cubicTwistExceptionalConstant,
      cubicKappaGood,decide_eq_false h6] using h
end WaringSiegel.WSL4Weil

#print axioms WaringSiegel.WSL4Weil.twistedCubicSum_prime_power_bound
