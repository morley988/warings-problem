import WaringSiegel.WSL4CenterProductSeries
import WaringSiegel.WSL3AuxiliaryRationalTail

/-! # Prime-uniform full main-term truncation for the literal auxiliary cubic series -/
noncomputable section
set_option maxHeartbeats 1200000
open NumberField NumberField.mixedEmbedding Module
open scoped NumberField Classical BigOperators
namespace WaringSiegel.WSL4Local
open WaringSiegel.WSL2 WaringSiegel.WSL3 WaringSiegel.WSL4
variable {K : Type*} [Field K] [NumberField K]

def auxiliaryProductMajorSeries (ρ R L : ℝ) (p : 𝓞 K) (hp : p≠0)
    (ν : 𝓞 K) (b : mixedSpace K) : ℂ :=
  productCenterSeries 3 8 ρ R L (fun q => rationalCenterAuxiliaryContribution q p hp ν) b

theorem auxiliaryProductMajorSeries_truncation
    (ρ R : ℝ) (hρ : 0<ρ) (hR : 0<R) :
    ∃ C : ℝ, 0<C ∧ ∀ (p : ℕ) (hp : p.Prime), 173≤p →
      ∀ (ν : 𝓞 K) (L : ℝ), 1≤L → ∀ b : mixedSpace K,
      let hp0 : (p:𝓞 K)≠0 := Nat.cast_ne_zero.mpr hp.ne_zero
      ‖auxiliaryProductMajorSeries ρ R L (p:𝓞 K) hp0 ν b -
        auxiliaryCubicSingularSeries (p:𝓞 K) hp0 ν *
          pairedWeightedSingularIntegral (integerLatticeSourceScale K) 3 8
            (smoothRootWeight ρ R) b‖ ≤ C*(p:ℝ)^(2*finrank ℚ K)/L^(5/4:ℝ) := by
  obtain ⟨C,hC,hbound⟩ := productCenterSeries_full_truncation_error (K:=K)
    3 7 (by norm_num) ρ R hρ hR (5/4:ℝ) (by norm_num)
  let D := cubicSharpUniformSingularSeriesConstant K
  have hD : 0<D := cubicSharpUniformSingularSeriesConstant_pos
  refine ⟨C*D,mul_pos hC hD,?_⟩
  intro p hp hp173 ν L hL b hp0
  have hgood : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      (p:𝓞 K)∈v.asIdeal → (6:𝓞 K)∉v.asIdeal ∧ 173≤Ideal.absNorm v.asIdeal := by
    intro v hv
    exact ⟨prime_above_large_rational_prime_avoids_six v hp (by omega) hv,
      hp173.trans (rational_prime_le_residue_norm v hp hv)⟩
  obtain ⟨hs,hb⟩ := rationalCenterAuxiliaryContribution_five_quarters_uniform_bound
    (p:𝓞 K) hp0 ν hgood
  have he := hbound (fun q => rationalCenterAuxiliaryContribution q (p:𝓞 K) hp0 ν)
    (D*(Ideal.absNorm (Ideal.span ({(p:𝓞 K)}:Set (𝓞 K))):ℝ)^2) hs hb L hL b
  rw [rationalCenterAuxiliaryContribution_tsum] at he
  change ‖auxiliaryProductMajorSeries ρ R L (p:𝓞 K) hp0 ν b - _‖≤_ at he
  apply he.trans_eq
  rw [ideal_absNorm_span_nat,Nat.cast_pow,← pow_mul,Nat.mul_comm (finrank ℚ K) 2]
  ring

#print axioms auxiliaryProductMajorSeries_truncation
end WaringSiegel.WSL4Local
