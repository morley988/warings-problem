import Waring.FourierCompletion
import Waring.CompletionKernel
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Mul
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Common-modulation completion for finite moment families

Jensen's inequality is applied to the measure having density equal to the
common completion majorant. Only after summing the resulting moment bound
over the whole family do we use its uniform estimate at one common real t.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Waring.FourierCompletion

/-- The elementary finite-measure form of Jensen needed for completion. -/
theorem integral_pow_le_mass_mul {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {f : α → ℝ} {p : ℕ}
    (hp : 1 ≤ p) (hf : ∀ x, 0 ≤ f x)
    (hfi : Integrable f μ) (hpi : Integrable (fun x => f x ^ p) μ) :
    (∫ x, f x ∂μ) ^ p ≤ μ.real Set.univ ^ (p - 1) * (∫ x, f x ^ p ∂μ) := by
  by_cases hμ : μ = 0
  · subst μ
    have hp0 : p ≠ 0 := by omega
    simp [hp0]
  haveI : NeZero μ := ⟨hμ⟩
  have hm : 0 < μ.real Set.univ := measureReal_univ_pos
  have H := (convexOn_pow (𝕜 := ℝ) p).map_average_le
    (continuous_pow p).continuousOn isClosed_Ici
    (Filter.Eventually.of_forall hf) hfi hpi
  simp only [average_eq, smul_eq_mul] at H
  have H' := mul_le_mul_of_nonneg_left H (pow_nonneg hm.le p)
  have hl : μ.real Set.univ ^ p * ((μ.real Set.univ)⁻¹ * (∫ x, f x ∂μ)) ^ p =
      (∫ x, f x ∂μ) ^ p := by
    rw [← mul_pow, mul_inv_cancel_left₀ hm.ne']
  rw [hl] at H'
  convert H' using 1
  rcases p with _ | p
  · omega
  simp only [Nat.add_sub_cancel, pow_succ]
  field_simp

/-- Weighted Jensen on the unit interval. All hypotheses concern a literal
real weight and continuous nonnegative function, with no analytic estimate. -/
theorem integral_weighted_pow_le {K f : ℝ → ℝ} {p : ℕ}
    (hp : 1 ≤ p) (hKm : Measurable K) (hK : ∀ t, 0 ≤ K t)
    (hKi : IntervalIntegrable K volume 0 1)
    (hfc : Continuous f) (hf : ∀ t, 0 ≤ f t) :
    (∫ t in (0 : ℝ)..1, K t * f t) ^ p ≤
      (∫ t in (0 : ℝ)..1, K t) ^ (p-1) *
        (∫ t in (0 : ℝ)..1, K t * f t ^ p) := by
  let μ : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)
  let ν : Measure ℝ := μ.withDensity (fun t => ENNReal.ofReal (K t))
  have hKμ : Integrable K μ := by
    simpa only [μ, intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] using hKi
  haveI : IsFiniteMeasure ν := isFiniteMeasure_withDensity_ofReal hKμ.hasFiniteIntegral
  have hfd (g : ℝ → ℝ) : (∫ t, g t ∂ν) = ∫ t in (0 : ℝ)..1, K t * g t := by
    rw [intervalIntegral.integral_of_le zero_le_one]
    dsimp [ν, μ]
    rw [integral_withDensity_eq_integral_toReal_smul hKm.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
    simp only [ENNReal.toReal_ofReal (hK _), smul_eq_mul]
  have hmass : ν.real Set.univ = ∫ t in (0 : ℝ)..1, K t := by
    have hh := hfd (fun _ => (1 : ℝ))
    simpa using hh
  have hi (g : ℝ → ℝ) (hgc : Continuous g) : Integrable g ν := by
    apply (integrable_withDensity_iff hKm.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).2
    have hh := hKi.continuousOn_mul hgc.continuousOn
    simpa only [ENNReal.toReal_ofReal (hK _), μ,
      intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] using hh
  have H := integral_pow_le_mass_mul hp hf (hi f hfc) (hi (fun t => f t ^ p) (hfc.pow p))
  simpa only [hfd, hmass] using H

/-- Uniform common-modulation moment estimates pass to any family of
restrictions dominated by the same integrable completion kernel. -/
theorem family_completion_moment_bound {ι : Type*} (s : Finset ι)
    (S : Finset ℤ) (T : ι → Finset ℤ) (w : ι → ℤ → ℂ) {p : ℕ} (hp : 1 ≤ p)
    (hTS : ∀ i ∈ s, T i ⊆ S) (K : ℝ → ℝ)
    (hKm : Measurable K) (hK : ∀ t, 0 ≤ K t) (hKi : IntervalIntegrable K volume 0 1)
    (hkernel : ∀ i ∈ s, ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖kernel (T i) t‖ ≤ K t)
    (B : ℝ) (hB : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (∑ i ∈ s, ‖modulatedSum S (w i) t‖ ^ p) ≤ B) :
    (∑ i ∈ s, ‖∑ n ∈ T i, w i n‖ ^ p) ≤ (∫ t in (0 : ℝ)..1, K t) ^ p * B := by
  let A := ∫ t in (0 : ℝ)..1, K t
  have hA : 0 ≤ A := intervalIntegral.integral_nonneg zero_le_one (fun t _ => hK t)
  have hi (i : ι) : IntervalIntegrable
      (fun t => K t * ‖modulatedSum S (w i) t‖ ^ p) volume 0 1 :=
    hKi.mul_continuousOn ((continuous_modulatedSum S (w i)).norm.pow p).continuousOn
  calc
    _ ≤ ∑ i ∈ s, A ^ (p-1) * (∫ t in (0 : ℝ)..1, K t * ‖modulatedSum S (w i) t‖ ^ p) := by
      apply Finset.sum_le_sum
      intro i his
      apply (pow_le_pow_left₀ (norm_nonneg _)
        (completion_common_majorant S (T i) (hTS i his) (w i) K hKi (hkernel i his)) p).trans
      exact integral_weighted_pow_le hp hKm hK hKi (continuous_modulatedSum S (w i)).norm
        (fun _ => norm_nonneg _)
    _ = A ^ (p-1) * (∫ t in (0 : ℝ)..1, K t * (∑ i ∈ s, ‖modulatedSum S (w i) t‖ ^ p)) := by
      rw [← Finset.mul_sum]
      congr 1
      simp_rw [Finset.mul_sum]
      rw [intervalIntegral.integral_finset_sum (fun i _ => hi i)]
    _ ≤ A ^ (p-1) * (∫ t in (0 : ℝ)..1, K t * B) := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hA _)
      apply intervalIntegral.integral_mono_on zero_le_one
        (hKi.mul_continuousOn (continuous_finset_sum s (fun i _ =>
          (continuous_modulatedSum S (w i)).norm.pow p)).continuousOn)
        (hKi.mul_const B)
      intro t ht
      exact mul_le_mul_of_nonneg_left (hB t ht) (hK t)
    _ = _ := by
      rw [intervalIntegral.integral_mul_const]
      change A ^ (p-1) * (A * B) = A ^ p * B
      rw [← mul_assoc, ← pow_succ]
      congr 2
      omega

/-- Full completion for arbitrary positive-step progressions, with a proved
logarithmic loss. In particular d=1 gives intervals and d=2 gives parity
classes. The full-family hypothesis uses a single common t. -/
theorem family_progression_moment_log_bound {ι : Type*} (s : Finset ι)
    (S : Finset ℤ) (M : ι → ℤ) (n : ι → ℕ) (w : ι → ℤ → ℂ)
    (N d p : ℕ) (hN : 0 < N) (hd : 0 < d) (hp : 1 ≤ p)
    (hnN : ∀ i ∈ s, n i ≤ N)
    (hTS : ∀ i ∈ s, progression (M i) (d : ℤ) (n i) ⊆ S)
    (B : ℝ) (hB0 : 0 ≤ B) (hB : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (∑ i ∈ s, ‖modulatedSum S (w i) t‖ ^ p) ≤ B) :
    (∑ i ∈ s, ‖∑ z ∈ progression (M i) (d : ℤ) (n i), w i z‖ ^ p) ≤
      (4*(2+Real.log (N : ℝ)/Real.log 2)) ^ p * B := by
  let K := fun t : ℝ => CompletionKernel.kernel N ((d : ℝ) * t)
  have hKm : Measurable K :=
    (CompletionKernel.measurable_kernel N).comp (measurable_const.mul measurable_id)
  have hK (t : ℝ) : 0 ≤ K t := CompletionKernel.kernel_nonneg hN _
  have hKi : IntervalIntegrable K volume 0 1 :=
    CompletionKernel.kernel_comp_intervalIntegrable hN _ (measurable_const.mul measurable_id) 0 1
  have H := family_completion_moment_bound s S (fun i => progression (M i) d (n i)) w hp
    hTS K hKm hK hKi (fun i his t _ => by
      simpa only [K, Int.cast_natCast] using
        norm_kernel_progression_le (M i) (d : ℤ) (by exact_mod_cast hd.ne') hN (hnN i his) t) B hB
  apply H.trans
  apply mul_le_mul_of_nonneg_right _ hB0
  apply pow_le_pow_left₀
    (intervalIntegral.integral_nonneg zero_le_one (fun t _ => hK t))
  exact CompletionKernel.kernel_integral_mul_nat_le_log N d hN hd

/-- Interval-restriction form of the common-modulation theorem. -/
theorem family_interval_moment_log_bound {ι : Type*} (s : Finset ι)
    (S : Finset ℤ) (a b : ι → ℤ) (w : ι → ℤ → ℂ)
    (N p : ℕ) (hN : 0 < N) (hp : 1 ≤ p)
    (hlen : ∀ i ∈ s, (b i + 1 - a i).toNat ≤ N)
    (hTS : ∀ i ∈ s, Finset.Icc (a i) (b i) ⊆ S)
    (B : ℝ) (hB0 : 0 ≤ B) (hB : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (∑ i ∈ s, ‖modulatedSum S (w i) t‖ ^ p) ≤ B) :
    (∑ i ∈ s, ‖∑ z ∈ Finset.Icc (a i) (b i), w i z‖ ^ p) ≤
      (4*(2+Real.log (N : ℝ)/Real.log 2)) ^ p * B := by
  have hsub : ∀ i ∈ s, progression (a i) (1 : ℤ) (b i + 1 - a i).toNat ⊆ S := by
    intro i his
    simpa only [← interval_eq_progression] using hTS i his
  have H := family_progression_moment_log_bound s S a (fun i => (b i + 1 - a i).toNat)
    w N 1 p hN (by norm_num) hp hlen hsub B hB0 hB
  simpa only [Nat.cast_one, ← interval_eq_progression] using H

/-- Parity-restriction form. The modulus is fixed at two, while the interval
and residue may vary throughout the family. No modulation is chosen per i. -/
theorem family_parity_moment_log_bound {ι : Type*} (s : Finset ι)
    (S : Finset ℤ) (a b r : ι → ℤ) (w : ι → ℤ → ℂ)
    (N p : ℕ) (hN : 0 < N) (hp : 1 ≤ p)
    (hlen : ∀ i ∈ s, (b i + 1 - a i).toNat ≤ N)
    (hTS : ∀ i ∈ s, (Finset.Icc (a i) (b i)).filter (fun z => z%2 = r i%2) ⊆ S)
    (B : ℝ) (hB0 : 0 ≤ B) (hB : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (∑ i ∈ s, ‖modulatedSum S (w i) t‖ ^ p) ≤ B) :
    (∑ i ∈ s, ‖∑ z ∈ (Finset.Icc (a i) (b i)).filter (fun z => z%2 = r i%2), w i z‖ ^ p) ≤
      (4*(2+Real.log (N : ℝ)/Real.log 2)) ^ p * B := by
  let M := fun i => a i + (r i - a i)%2
  let n := fun i => ((b i - M i)/2+1).toNat
  have heq (i : ι) : (Finset.Icc (a i) (b i)).filter (fun z => z%2 = r i%2) =
      progression (M i) 2 (n i) := parity_interval_eq_progression (a i) (b i) (r i)
  have hn : ∀ i ∈ s, n i ≤ N := by
    intro i his
    have hh := hlen i his
    dsimp [n, M]
    omega
  have H := family_progression_moment_log_bound s S M n w N 2 p hN (by norm_num) hp hn
    (fun i his => by simpa only [Nat.cast_ofNat, ← heq] using hTS i his) B hB0 hB
  simpa only [Nat.cast_ofNat, ← heq] using H

#print axioms integral_pow_le_mass_mul
#print axioms integral_weighted_pow_le
#print axioms family_completion_moment_bound
#print axioms family_progression_moment_log_bound
#print axioms family_interval_moment_log_bound
#print axioms family_parity_moment_log_bound

end Waring.FourierCompletion
