import WaringSiegel.WSL4MixedBoxGeometry
import WaringSiegel.WSL4ArchMixedFull

/-! # The original off-diagonal mixed count has the required sixth-moment scale -/
noncomputable section
set_option maxHeartbeats 1500000
open MeasureTheory Module NumberField NumberField.mixedEmbedding
open scoped NumberField BigOperators Classical nonZeroDivisors
namespace WaringSiegel.WSL4Local
open WaringSiegel.WSL2 WaringSiegel.WSL3 WaringSiegel.WSL3Poisson WaringSiegel.WSL4
variable {K : Type*} [Field K] [NumberField K]

theorem mixed_offdiagonal_box_bound (ε : ℝ) (hε : 0<ε)
    (B : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℝ) (hB : ∀ v,0<B v)
    (hfinite : ∀ (γ : K) (ξ : (inverseDifferent K*(traceConductor γ : FractionalIdeal (𝓞 K)⁰ K)⁻¹)),
      ‖fieldCenterCompleteSum 3 γ (mixedEmbedding K (ξ:K))‖ ≤
        ((traceConductor γ).absNorm:ℝ)*cubicKappa B ⟨traceConductor γ,traceConductor_ne_zero γ⟩) :
    ∃ C : ℝ, 0<C ∧ ∀ (P M : ℝ), 1≤M → M^7≤P →
      ∀ X A Y : Finset (𝓞 K),
      (∀ x ∈ X, ‖mixedEmbedding K (x:K)‖≤P) →
      (∀ m ∈ A, ∀ v : InfinitePlace K, M≤v (m:K)) →
      (∀ m ∈ A, ‖mixedEmbedding K (m:K)‖≤2*M) →
      (∀ y ∈ Y, ‖mixedEmbedding K (y:K)‖≤P/M) →
      (mixedCongruentOffdiagonalCount X A Y:ℝ) ≤
        C*(P^finrank ℚ K:ℝ)^((7:ℝ)/2+ε)*(M^finrank ℚ K:ℝ)^(-(9/2):ℝ) := by
  obtain ⟨C,hC,hbound⟩ := nearZeroMixedSIntegral_bound ε hε B hB hfinite
  let A₀ : ℝ := (((4:ℝ)^7)^finrank ℚ K:ℝ)^((7:ℝ)/2+ε)
  let A₁ : ℝ := ((4:ℝ)^finrank ℚ K:ℝ)^(-(9/2):ℝ)
  have hA₀ : 0<A₀ := by dsimp [A₀]; positivity
  have hA₁ : 0<A₁ := by dsimp [A₁]; positivity
  refine ⟨C*A₀*A₁,by positivity,fun P M hM hMP X A Y hX hAlo hAhi hY => ?_⟩
  have hM0 : 0<M := by linarith
  have hP0 : 0<P := lt_of_lt_of_le (pow_pos hM0 7) hMP
  have hM' : 1≤4*M := by linarith
  have hMP' : (4*M)^7≤(4:ℝ)^7*P := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left hMP (by positivity)
  have hb := hbound ((4:ℝ)^7*P) (4*M) hM' hMP'
  have hc := mixed_offdiagonal_le_rescaled_integral X A Y P M hP0 hM0 hX hAlo hAhi hY
  change _≤‖nearZeroMixedSIntegral (K:=K) _ _ _ _ _ _ _ _‖ at hc
  apply hc.trans
  apply hb.trans_eq
  rw [mul_pow,mul_pow,
    Real.mul_rpow (by positivity : 0≤((4:ℝ)^7)^finrank ℚ K)
      (pow_nonneg hP0.le _),
    Real.mul_rpow (by positivity : 0≤(4:ℝ)^finrank ℚ K)
      (pow_nonneg hM0.le _)]
  dsimp [A₀,A₁]
  ring

#print axioms mixed_offdiagonal_box_bound
end WaringSiegel.WSL4Local
