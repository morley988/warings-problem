import WaringSiegel.WSL3PoissonUniformFourier

/-!
# Uniform trace Fourier product decay for actual compact smooth families

The Euclidean family estimate is transported through the literal trace
frequency equivalence and its actual volume-preserving source coordinates.
-/

noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory Module Function NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  WaringSiegel.WSL2 WaringSiegel.WSL3
open scoped ContDiff FourierTransform RealInnerProductSpace BigOperators Classical NumberField
namespace WaringSiegel.WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem traceFourier_eq_euclidean (f : mixedSpace K → ℂ) (β : mixedSpace K) :
    traceFourier f β =
      𝓕 (fun x : euclidean.mixedSpace K => f (euclidean.toMixed K x)) (traceFrequency β) := by
  have h := traceFrequency_fourier f (-β)
  simpa only [map_neg, neg_neg, traceFourier] using h.symm

theorem uniform_traceFourier_polynomial_bound
    {F : P × mixedSpace K → ℂ} (hF : ContDiff ℝ ∞ F)
    {T : Set P} {S : Set (mixedSpace K)} (hT : IsCompact T) (hS : IsCompact S)
    (hFs : ∀ p, support (fun x => F (p,x)) ⊆ S) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ p ∈ T, ∀ β : mixedSpace K,
      (1+‖β‖)^n * ‖traceFourier (fun x => F (p,x)) β‖ ≤ C := by
  let E := euclidean.mixedSpace K
  let G : P × E → ℂ := fun q => F (q.1, euclidean.toMixed K q.2)
  have hG : ContDiff ℝ ∞ G :=
    hF.comp (contDiff_fst.prodMk ((euclidean.toMixed K).contDiff.comp contDiff_snd))
  let S' : Set E := (euclidean.toMixed K).symm '' S
  have hS' : IsCompact S' := hS.image (euclidean.toMixed K).symm.continuous
  have hGs (p : P) : support (fun x => G (p,x)) ⊆ S' := by
    intro x hx
    exact ⟨euclidean.toMixed K x, hFs p hx, (euclidean.toMixed K).symm_apply_apply x⟩
  have hdim : 0 < finrank ℝ E := by
    change 0 < finrank ℝ (euclidean.mixedSpace K)
    rw [euclidean.finrank]
    exact Module.finrank_pos
  letI : Nontrivial E := Module.finrank_pos_iff.mp hdim
  obtain ⟨C, hC, hb⟩ := uniform_fourier_polynomial_bound hG hT hS' hGs n
  let a := ‖(traceFrequency (K:=K)).symm.toContinuousLinearMap‖
  have ha : 0 ≤ a := norm_nonneg _
  refine ⟨(1+a)^n*C, by positivity, fun p hp β => ?_⟩
  have hnorm : ‖β‖ ≤ a * ‖traceFrequency β‖ := by
    simpa only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply] using
      (traceFrequency (K:=K)).symm.toContinuousLinearMap.le_opNorm (traceFrequency β)
  have hpow : (1+‖β‖)^n ≤ (1+a)^n * (1+‖traceFrequency β‖)^n := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [norm_nonneg (traceFrequency β)]
  rw [traceFourier_eq_euclidean]
  calc
    _ ≤ ((1+a)^n * (1+‖traceFrequency β‖)^n) *
        ‖𝓕 (fun x : E => F (p,euclidean.toMixed K x)) (traceFrequency β)‖ :=
      mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
    _ = (1+a)^n * ((1+‖traceFrequency β‖)^n *
        ‖𝓕 (fun x : E => F (p,euclidean.toMixed K x)) (traceFrequency β)‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hb p hp (traceFrequency β)) (by positivity)

theorem norm_le_productDecay_of_polynomial_bound (f : mixedSpace K → ℂ) (m : ℕ) (C : ℝ)
    (hf : ∀ β, (1+‖β‖)^(Fintype.card (InfinitePlace K)*m)*‖f β‖ ≤ C)
    (β : mixedSpace K) : ‖f β‖ ≤ C * archimedeanProductDecay m β := by
  have hden : 0 < ∏ w : InfinitePlace K, (1+normAtPlace w β)^m := by
    apply Finset.prod_pos
    intro w hw
    have h := normAtPlace_nonneg w β
    positivity
  have hprod : (∏ w : InfinitePlace K, (1+normAtPlace w β)^m) ≤
      (1+‖β‖)^(Fintype.card (InfinitePlace K)*m) := by
    calc
      _ ≤ ∏ _w : InfinitePlace K, (1+‖β‖)^m := by
        apply Finset.prod_le_prod
        · intro w hw
          have h := normAtPlace_nonneg w β
          positivity
        · intro w hw
          apply pow_le_pow_left₀ (by have h := normAtPlace_nonneg w β; positivity)
          exact add_le_add_left (normAtPlace_le_mixed_norm β w) 1
      _ = _ := by rw [Finset.prod_const, Finset.card_univ, ← pow_mul, Nat.mul_comm]
  unfold archimedeanProductDecay
  rw [Finset.prod_div_distrib, Finset.prod_const_one, mul_one_div]
  apply (le_div_iff₀ hden).mpr
  calc
    _ ≤ ‖f β‖ * (1+‖β‖)^(Fintype.card (InfinitePlace K)*m) :=
      mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ ≤ _ := by simpa only [mul_comm] using hf β

/-- The actual family Fourier integrals have one product-decay constant before
all amplitude parameters and all frequencies. -/
theorem uniform_traceFourier_product_decay
    {F : P × mixedSpace K → ℂ} (hF : ContDiff ℝ ∞ F)
    {T : Set P} {S : Set (mixedSpace K)} (hT : IsCompact T) (hS : IsCompact S)
    (hFs : ∀ p, support (fun x => F (p,x)) ⊆ S) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ p ∈ T, ∀ β : mixedSpace K,
      ‖traceFourier (fun x => F (p,x)) β‖ ≤ C * archimedeanProductDecay m β := by
  obtain ⟨C, hC, hb⟩ := uniform_traceFourier_polynomial_bound hF hT hS hFs
    (Fintype.card (InfinitePlace K)*m)
  exact ⟨C, hC, fun p hp β => norm_le_productDecay_of_polynomial_bound _ m C (hb p hp) β⟩

end WaringSiegel.WSL3Poisson
