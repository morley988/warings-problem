import WaringSiegel.WSL4MixedDiagonalMoment
import WaringSiegel.WSL4MixedOffdiagonalBound
import WaringSiegel.WSL4MixedVolumeArithmetic

/-! # The actual congruent mixed count at the uniform sixth-moment scale -/
noncomputable section
set_option maxHeartbeats 1400000
open MeasureTheory Module NumberField NumberField.mixedEmbedding
open scoped NumberField BigOperators Classical nonZeroDivisors
namespace WaringSiegel.WSL4Local
open WaringSiegel.WSL2 WaringSiegel.WSL3 WaringSiegel.WSL3Poisson WaringSiegel.WSL4
variable {K : Type*} [Field K] [NumberField K]

theorem congruent_mixed_count_box_bound (ε : ℝ) (hε : 0<ε)
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
      ((∑ m:A,mixedResidueCongruentCount (m.val^3)
        (fun x:X=>x.val) (fun y:Y=>y.val)):ℝ) ≤
        C*(P^finrank ℚ K:ℝ)^((7:ℝ)/2+ε)*(M^finrank ℚ K:ℝ)^(-(9/2):ℝ) := by
  obtain ⟨CD,hCD,hd⟩ := mixed_diagonal_box_bound (K:=K) hε
  obtain ⟨CO,hCO,ho⟩ := mixed_offdiagonal_box_bound ε hε B hB hfinite
  refine ⟨CD*2^finrank ℚ K+CO,by positivity,?_⟩
  intro P M hM hMP X A Y hX hAlo hAhi hY
  obtain ⟨hP,hH,hR,hHP,hPH⟩ := mixed_scale_range hM hMP
  have hM0 : 0<M := by linarith
  have hP0 : 0<P := by linarith
  have hXplace : ∀ x∈X,∀ v:InfinitePlace K,v (x:K)≤P := by
    intro x hx v
    rw [← normAtPlace_apply]
    exact (normAtPlace_le_mixed_norm _ v).trans (hX x hx)
  have hAplace : ∀ m∈A,∀ v:InfinitePlace K,v (m:K)≤2*M := by
    intro m hm v
    rw [← normAtPlace_apply]
    exact (normAtPlace_le_mixed_norm _ v).trans (hAhi m hm)
  have hYplace : ∀ y∈Y,∀ v:InfinitePlace K,v (y:K)≤P/M := by
    intro y hy v
    rw [← normAtPlace_apply]
    exact (normAtPlace_le_mixed_norm _ v).trans (hY y hy)
  have hA0 : ∀ m∈A,m≠0 := by
    intro m hm hz
    let v : InfinitePlace K := Classical.choice inferInstance
    have hh := hAlo m hm v
    have hh' : M≤0 := by simpa [hz] using hh
    linarith
  have hYP : (M^finrank ℚ K)^7≤P^finrank ℚ K := by
    rw [← pow_mul,Nat.mul_comm (finrank ℚ K) 7,pow_mul]
    exact pow_le_pow_left₀ (pow_nonneg hM0.le 7) hMP _
  have harith := mixed_diagonal_volume_bound (P^finrank ℚ K) (M^finrank ℚ K) ε
    (pow_pos hP0 _) (one_le_pow₀ hM) hYP hε.le
  have hdiag := hd P (2*M) (P/M) hP (by linarith) hR X A Y hXplace hAplace hYplace
  have hdiag' : (A.card*X.card*cubicFourthBoxCount Y:ℝ) ≤
      (CD*2^finrank ℚ K)*(P^finrank ℚ K:ℝ)^((7:ℝ)/2+ε)*(M^finrank ℚ K:ℝ)^(-(9/2):ℝ) := by
    apply hdiag.trans
    rw [mul_pow,div_pow]
    have hh := mul_le_mul_of_nonneg_left harith (show 0≤CD*2^finrank ℚ K by positivity)
    simpa only [mul_assoc] using hh
  have heR := congrArg (fun n:ℕ => (n:ℝ)) (congruent_mixed_count_diagonal_split X A Y hA0)
  push_cast at heR
  rw [heR]
  have hoff := ho P M hM hMP X A Y hX hAlo hAhi hY
  exact (add_le_add hdiag' hoff).trans_eq (by ring)

#print axioms congruent_mixed_count_box_bound
end WaringSiegel.WSL4Local
