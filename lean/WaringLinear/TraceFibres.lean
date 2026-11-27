import WaringSiegel.WSL2MomentHaarAverage
import WaringSiegel.WSL3TraceIdealDuality

/-! # Multiplication fibres and Haar mass

A bound for the number of selected lifts of each point gives a proportional
bound for the Haar integral of every nonnegative weight on the target.
This form retains the amplitudes in a large-values iteration.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Classical NumberField
open WaringSiegel

namespace WaringLinear

variable {K : Type*} [Field K] [NumberField K]

/-- The actual multiplication kernel on the trace torus equals the set of
rational characters with conductor dividing the principal ideal. -/
theorem trace_kernel_as_ideal_centers (a : 𝓞 K) (ha : a ≠ 0) :
    ((traceTorusMul a).ker : Set (ArchimedeanTraceTorus K)) =
      traceIdealCenters (Ideal.span {a}) := by
  ext q
  constructor
  · intro hq
    obtain ⟨γ,hγ,hqγ⟩ := traceTorusMul_kernel_representative a ha hq
    exact ⟨γ, hqγ, (Ideal.span_singleton_le_iff_mem _).mpr
      ((traceKernelFractionalIdeal_mem a ha γ).mp hγ)⟩
  · rintro ⟨γ,rfl,hγ⟩
    apply (traceTorusMul_kernel_mk_iff a ha _).mpr
    exact ⟨γ, (traceKernelFractionalIdeal_mem a ha γ).mpr
      ((Ideal.span_singleton_le_iff_mem _).mp hγ), rfl⟩

/-- The fibre cardinality on the trace torus is the principal ideal norm. -/
theorem trace_kernel_card (a : 𝓞 K) (ha : a ≠ 0) :
    Nat.card (traceTorusMul a).ker = Ideal.absNorm (Ideal.span {a}) := by
  change Nat.card (↑((traceTorusMul a).ker : Set (ArchimedeanTraceTorus K)) : Type _) = _
  rw [trace_kernel_as_ideal_centers a ha]
  exact traceIdealCenters_card _ (by simpa using ha)

/-- The exact normalization for the multiplier in a kth-power sum. -/
theorem trace_pow_kernel_card (a : 𝓞 K) (ha : a ≠ 0) (k : ℕ) :
    Nat.card (traceTorusMul (a ^ k)).ker = Ideal.absNorm (Ideal.span {a}) ^ k := by
  rw [trace_kernel_card _ (pow_ne_zero _ ha), ← Ideal.span_singleton_pow, map_pow]

variable {T : Type*} [AddCommGroup T] [MeasurableSpace T] [MeasurableAdd T]

/-- Weighted finite-cover estimate on any additive group. The selectivity
hypothesis counts the selected points of each kernel coset. -/
theorem integral_selected_lifts_le
    (μ : Measure T) [μ.IsAddRightInvariant] (π : T →+ T)
    (hπ : MeasurePreserving π μ μ) [Fintype π.ker]
    (S : Set T) (hS : MeasurableSet S) (J : ℕ)
    (hJ : ∀ x : T, (Finset.univ.filter (fun η : π.ker => x + η.1 ∈ S)).card ≤ J)
    (g : T → ℝ) (hg : Integrable g μ) (hpos : ∀ x, 0 ≤ g x) :
    (∫ x, S.indicator (fun y => g (π y)) x ∂μ) ≤
      (J : ℝ) / Fintype.card π.ker * ∫ y, g y ∂μ := by
  let f : T → ℝ := S.indicator (fun _ => 1)
  let G : T → ℝ := fun x => g (π x)
  have hG : Integrable G μ := hπ.integrable_comp_of_integrable hg
  have hfg (x : T) : f x * G x = S.indicator G x := by
    by_cases h : x ∈ S <;> simp [f, h, Set.indicator]
  have hinv (η : π.ker) (x : T) : G (x+η.1) = G x := by
    simp [G, AddMonoidHom.mem_ker.mp η.property]
  have hInt : Integrable (fun x => f x * G x) μ := by
    simp_rw [hfg]
    exact hG.indicator hS
  have havg := WSL2.integral_finite_translation_average_mul μ
    (fun η : π.ker => (η : T)) f G hInt hinv
  have hleft := WSL2.integrable_finite_translation_average_mul μ
    (fun η : π.ker => (η : T)) f G hInt hinv
  have hpoint (x : T) : (𝔼 η : π.ker, f (x+η.1)) ≤ (J : ℝ) / Fintype.card π.ker := by
    rw [Fintype.expect_eq_sum_div_card]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    have hcount : (∑ η : π.ker, f (x+η.1)) =
        ((Finset.univ.filter (fun η : π.ker => x+η.1 ∈ S)).card : ℝ) := by
      simp [f, Set.indicator]
    rw [hcount]
    exact_mod_cast hJ x
  have hpush : (∫ x, G x ∂μ) = ∫ y, g y ∂μ := by
    unfold G
    rw [← integral_map hπ.measurable.aemeasurable (by simpa only [hπ.map_eq] using hg.aestronglyMeasurable), hπ.map_eq]
  calc
    _ = ∫ x, f x * G x ∂μ := by simp_rw [hfg]; rfl
    _ = _ := havg.symm
    _ ≤ ∫ x, ((J : ℝ) / Fintype.card π.ker) * G x ∂μ :=
      integral_mono hleft (hG.const_mul _) (fun x => mul_le_mul_of_nonneg_right
        (hpoint x) (hpos (π x)))
    _ = _ := by rw [integral_const_mul, hpush]

/-- Weighted large-value fibre bound over an arbitrary number field, with the
arithmetic normalization written as a power of the ideal norm. -/
theorem trace_integral_selected_lifts_le
    (a : 𝓞 K) (ha : a ≠ 0) (k J : ℕ)
    (S : Set (ArchimedeanTraceTorus K)) (hS : MeasurableSet S)
    (hJ : ∀ x : ArchimedeanTraceTorus K,
      Nat.card {q : (traceTorusMul (a^k)).ker // x + q.1 ∈ S} ≤ J)
    (g : ArchimedeanTraceTorus K → ℝ) (hg : Integrable g traceHaar)
    (hpos : ∀ x, 0 ≤ g x) :
    (∫ x, S.indicator (fun y => g (traceTorusMul (a^k) y)) x ∂traceHaar) ≤
      (J : ℝ) / (Ideal.absNorm (Ideal.span {a}) : ℝ)^k * ∫ y, g y ∂traceHaar := by
  classical
  letI := traceTorusMul_kernel_finite_type (a^k) (pow_ne_zero _ ha)
  letI := Fintype.ofFinite (traceTorusMul (a^k)).ker
  have hcard : (Fintype.card (traceTorusMul (a^k)).ker : ℝ) =
      (Ideal.absNorm (Ideal.span {a}) : ℝ)^k := by
    exact_mod_cast (Nat.card_eq_fintype_card.symm.trans (trace_pow_kernel_card a ha k))
  rw [← hcard]
  apply integral_selected_lifts_le traceHaar _ (traceTorusMul_measurePreserving _ (pow_ne_zero _ ha))
    S hS J _ g hg hpos
  intro x
  simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using hJ x

#print axioms trace_pow_kernel_card
#print axioms integral_selected_lifts_le
#print axioms trace_integral_selected_lifts_le

end WaringLinear
