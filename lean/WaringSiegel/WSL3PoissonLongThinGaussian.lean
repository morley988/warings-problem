import WaringSiegel.WSL3PoissonLongThinDuality
import WaringSiegel.WSL2LongThinMajorDecay

/-!
# Exact long-thin Gaussian Poisson and transfer of the actual arc bounds

The original-side series is over the actual inverse different and algebraic
integers. Its quadratic form uses the literal trace-frequency map. The
Gaussian Fourier transform, both summability statements, the dual lattice,
and the covolume have all been proved, not retained as hypotheses.
-/

noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  WaringSiegel.WSL3
open scoped BigOperators Classical NumberField nonZeroDivisors RealInnerProductSpace
namespace WaringSiegel.WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

/-- The literal original Gaussian, including the true complex-place trace factors. -/
def longThinOriginalGaussian (θ : mixedSpace K) (P H : ℝ) (p : inverseDifferent K × 𝓞 K) : ℝ :=
  Real.exp (-(Real.pi^2) *
    (P^2 * ‖traceFrequency (mixedEmbedding K (p.1:K) + θ*mixedEmbedding K (p.2:K))‖^2 +
      (P*H)⁻¹^2 * ‖traceFrequency (mixedEmbedding K (p.2:K))‖^2))

theorem longThinOriginalGaussian_eq_norm (θ : mixedSpace K) (P H : ℝ)
    (p : inverseDifferent K × 𝓞 K) :
    longThinOriginalGaussian θ P H p = Real.exp (-(Real.pi^2) *
      ‖longThinOriginalPoint θ P H (mixedEmbedding K (p.1:K)) (mixedEmbedding K (p.2:K))‖^2) := by
  rw [longThinOriginalPoint_norm_sq]
  rfl

/-- Both true Gaussian lattice sums converge absolutely at every nonzero scale. -/
theorem longThin_gaussian_summable (θ : mixedSpace K) (P H : ℝ)
    (hP : P ≠ 0) (hH : H ≠ 0) :
    Summable (fun p : longThinDualDomain (inverseDifferent K) => longThinDualGaussian θ P H p) ∧
      Summable (longThinOriginalGaussian θ P H) := by
  let b := longThinBasis θ P H hP hH
  have hd := (longThinPairCoordinates (K:=K)).summable_iff.mpr
    (gaussian_real_equiv_integer_summable b.equivFunL.symm 1 le_rfl)
  have hd' : Summable (fun p : 𝓞 K × inverseDifferent K =>
      longThinDualGaussian θ P H (p.1,(p.2:K))) := by
    apply hd.congr
    intro p
    simp only [Function.comp_apply, b, longThinPair_coordinates, neg_mul, one_mul,
      longThinPoint_norm_sq, longThinDualGaussian]
  refine ⟨(longThinDomainEquiv (K:=K)).summable_iff.mpr hd', ?_⟩
  have hpi : 1 ≤ Real.pi^2 := by nlinarith [Real.two_le_pi]
  have ho := (longThinOriginalCoordinates (K:=K)).summable_iff.mpr
    (gaussian_real_equiv_integer_summable (basisDualCoordinates b) (Real.pi^2) hpi)
  apply ho.congr
  intro p
  dsimp only [Function.comp_apply, b]
  rw [longThinOriginal_basisDualCoordinates,
    ← longThinOriginalGaussian_eq_norm]

/-- Poisson summation for the actual long-thin lattice with the exact coefficient. -/
theorem poisson_longThin_gaussian (θ : mixedSpace K) (P H : ℝ)
    (hP : P ≠ 0) (hH : 0 < H) :
    (∑' p : inverseDifferent K × 𝓞 K, longThinOriginalGaussian θ P H p) =
      (H^(finrank ℚ K) / ((4:ℝ)^nrComplexPlaces K * Real.pi^(finrank ℚ K))) *
        (∑' p : longThinDualDomain (inverseDifferent K), longThinDualGaussian θ P H p) := by
  let b := longThinBasis θ P H hP hH.ne'
  have h := poisson_gaussian_one_basis_real b (finrank ℚ K) (doubleMixed_finrank (K:=K))
  have hd : (∑' n : DoubleIndex K → ℤ, Real.exp (-‖b.equivFunL.symm (intVector n)‖^2)) =
      ∑' p : longThinDualDomain (inverseDifferent K), longThinDualGaussian θ P H p := by
    rw [← (longThinPairCoordinates (K:=K)).tsum_eq,
      ← (longThinDomainEquiv (K:=K)).tsum_eq]
    apply tsum_congr
    intro p
    dsimp only [b]
    rw [longThinPair_coordinates, longThinPoint_norm_sq]
    rfl
  have ho : (∑' n : DoubleIndex K → ℤ,
      Real.exp (-(Real.pi^2)*‖basisDualCoordinates b (intVector n)‖^2)) =
      ∑' p : inverseDifferent K × 𝓞 K, longThinOriginalGaussian θ P H p := by
    rw [← (longThinOriginalCoordinates (K:=K)).tsum_eq]
    apply tsum_congr
    intro p
    dsimp only [b]
    rw [longThinOriginal_basisDualCoordinates, ← longThinOriginalGaussian_eq_norm]
  rw [hd, ho] at h
  dsimp only [b] at h
  rw [longThinBasis_covolume θ P H hP hH] at h
  rw [h]
  field_simp

/-- The verified minor-arc dual bound now bounds the actual original Gaussian sum. -/
theorem longThinOriginalGaussian_minor_bound
    (θ : mixedSpace K) (P H : ℝ) (hP : 1 ≤ P) (hH : 1 ≤ H) (hPH : P ≤ H^2)
    (hminor : ∀ γ : K, P^finrank ℚ K <
      (Ideal.absNorm (conductorIdeal (inverseDifferent K) γ) : ℝ) *
        productArcWeight (P^2*H) (θ-mixedEmbedding K γ)) :
    Summable (longThinOriginalGaussian θ P H) ∧
      (∑' p, longThinOriginalGaussian θ P H p) ≤
        (H^(finrank ℚ K) / ((4:ℝ)^nrComplexPlaces K * Real.pi^(finrank ℚ K))) *
          (2*longThinGaussianFactor K*longThinDualConstant (inverseDifferent K)) := by
  have hPp : 0 < P := by linarith
  have hHp : 0 < H := by linarith
  refine ⟨(longThin_gaussian_summable θ P H hPp.ne' hHp.ne').2, ?_⟩
  rw [poisson_longThin_gaussian θ P H hPp.ne' hHp]
  exact mul_le_mul_of_nonneg_left
    (longThinDualGaussian_summable_bound _ inverseDifferent_ne_zero θ P H hP hH hPH hminor).2
    (by positivity)

/-- The verified major factor is retained after actual Gaussian Poisson transfer. -/
theorem longThinOriginalGaussian_major_bound
    (θ : mixedSpace K) (P H : ℝ) (hP : 1 ≤ P) (hH : 1 ≤ H) (hPH : P ≤ H^2)
    (γ : K) (hmaj : θ ∈ productMajorArc (inverseDifferent K) (P^2*H) (P^finrank ℚ K) γ) :
    Summable (longThinOriginalGaussian θ P H) ∧
      (∑' p, longThinOriginalGaussian θ P H p) ≤
        (H^(finrank ℚ K) / ((4:ℝ)^nrComplexPlaces K * Real.pi^(finrank ℚ K))) *
          ((2*longThinGaussianFactor K*longThinDualConstant (inverseDifferent K))*
            longThinMajorFactor (inverseDifferent K) θ P H γ) := by
  have hPp : 0 < P := by linarith
  have hHp : 0 < H := by linarith
  refine ⟨(longThin_gaussian_summable θ P H hPp.ne' hHp.ne').2, ?_⟩
  rw [poisson_longThin_gaussian θ P H hPp.ne' hHp]
  exact mul_le_mul_of_nonneg_left
    (longThinMajorGaussian_summable_bound _ inverseDifferent_ne_zero θ P H hP hH hPH γ hmaj).2
    (by positivity)

/-- The bound applies outside the actual trace-torus major arcs, including cubic scaling. -/
theorem trace_longThinOriginalGaussian_minor_bound
    (θ : mixedSpace K) (P H : ℝ) (hP : 1 ≤ P) (hH : 1 ≤ H) (hPH : P ≤ H^2)
    (k : ℕ) (hk : 0 < k)
    (hminor : (Submodule.Quotient.mk θ : ArchimedeanTraceTorus K) ∉
      traceMajorArcUnion (P^2*H) ((k:ℝ)^finrank ℚ K * P^finrank ℚ K)) :
    Summable (longThinOriginalGaussian ((k:ℝ) • θ) P H) ∧
      (∑' p, longThinOriginalGaussian ((k:ℝ) • θ) P H p) ≤
        (H^(finrank ℚ K) / ((4:ℝ)^nrComplexPlaces K * Real.pi^(finrank ℚ K))) *
          (2*longThinGaussianFactor K*longThinDualConstant (inverseDifferent K)) := by
  apply longThinOriginalGaussian_minor_bound ((k:ℝ) • θ) P H hP hH hPH
  exact traceMajorArcUnion_smul_nat_preimage (P^2*H) (P^finrank ℚ K)
    (by positivity) θ k hk hminor

end WaringSiegel.WSL3Poisson
