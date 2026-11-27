import WaringSiegel.WSL3PoissonMixedNonzero

/-! # Exact expansion of the sixth-power square in the mixed J integral

All phases are the literal trace-torus characters. The difference of sixth
powers occurs inside the torus multiplier, before any absolute-value bound.
-/
noncomputable section
set_option maxHeartbeats 600000
open MeasureTheory Function Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding WaringSiegel.WSL2
open scoped NumberField Classical BigOperators ContDiff nonZeroDivisors ComplexConjugate
namespace WaringSiegel.WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

theorem traceWeylSum_mul_conj_expansion {α β : Type*} [Fintype α] [Fintype β]
    (k : ℕ) (x : α → 𝓞 K) (y : β → 𝓞 K) (w : α → ℂ) (v : β → ℂ)
    (q : ArchimedeanTraceTorus K) :
    traceWeylSum k x w q * conj (traceWeylSum k y v q) =
      ∑ p : α × β, (w p.1 * conj (v p.2))*traceTorusCharacter (x p.1^k-y p.2^k) q := by
  simpa only [frequencySum,traceWeylSum,traceTorusCharacter,map_sub] using
    frequencySum_mul_conj_expansion
      (fun a => integerCoordinates K (x a^k)) (fun b => integerCoordinates K (y b^k)) w v
      (archimedeanTraceTorusContinuousAddEquiv q)

/-- Exact exchange of the h-sum with the two sixth-power variables. -/
theorem trace_sixth_square_cubic_exchange {α β : Type*} [Fintype α] [Fintype β]
    (h : α → 𝓞 K) (m : β → 𝓞 K) (u : α → ℂ) (w : β → ℂ)
    (q : ArchimedeanTraceTorus K) :
    (∑ a : α, u a * ((‖traceWeylSum 6 m w (traceTorusMul (h a^3) q)‖^2 : ℝ):ℂ)) =
      ∑ p : β × β, (w p.1*conj (w p.2))*
        traceWeylSum 3 h u (traceTorusMul (m p.1^6-m p.2^6) q) := by
  simp only [Complex.ofReal_pow,← Complex.mul_conj',traceWeylSum_mul_conj_expansion,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  simp only [traceWeylSum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  have hp : traceTorusCharacter (m p.1^6-m p.2^6) (traceTorusMul (h a^3) q) =
      traceTorusCharacter (h a^3) (traceTorusMul (m p.1^6-m p.2^6) q) := by
    rw [← traceTorusCharacter_mul,← traceTorusCharacter_mul,mul_comm]
  rw [hp]
  ring

/-- The literal excluded-zero cubic sum is a Weyl sum on its erased support. -/
theorem compactTraceNonzeroCubicSum_eq_traceWeylSum (u : mixedSpace K → ℂ)
    (huc : HasCompactSupport u) (H : ℝ) (hH : H ≠ 0) (q : ArchimedeanTraceTorus K) :
    compactTraceNonzeroCubicSum u huc H hH q =
      traceWeylSum 3 (fun h : (compactIntegerSupport u huc H hH).erase 0 => (h:𝓞 K))
        (fun h => u (H⁻¹ • mixedEmbedding K ((h:𝓞 K):K))) q := by
  exact (Finset.sum_coe_sort _ _).symm

/-- The original J integrand. No major/minor estimate enters its definition. -/
def compactMixedJIntegrand (u w v : mixedSpace K → ℂ)
    (huc : HasCompactSupport u) (hwc : HasCompactSupport w) (hvc : HasCompactSupport v)
    (H M R : ℝ) (hH : H ≠ 0) (hM : M ≠ 0) (hR : R ≠ 0)
    (q : ArchimedeanTraceTorus K) : ℂ :=
  (∑ h ∈ (compactIntegerSupport u huc H hH).erase 0,
    u (H⁻¹ • mixedEmbedding K (h:K)) *
      ((‖compactTraceWeylSum 6 w hwc M hM (traceTorusMul (h^3) q)‖^2 : ℝ):ℂ)) *
    ((‖compactTraceWeylSum 3 v hvc R hR (traceTorusMul 4 q)‖^4 : ℝ):ℂ)

def compactMixedJIntegral (u w v : mixedSpace K → ℂ)
    (huc : HasCompactSupport u) (hwc : HasCompactSupport w) (hvc : HasCompactSupport v)
    (H M R : ℝ) (hH : H ≠ 0) (hM : M ≠ 0) (hR : R ≠ 0) : ℂ :=
  ∫ q, compactMixedJIntegrand u w v huc hwc hvc H M R hH hM hR q ∂traceHaar

theorem compactMixedJIntegrand_expansion (u w v : mixedSpace K → ℂ)
    (huc : HasCompactSupport u) (hwc : HasCompactSupport w) (hvc : HasCompactSupport v)
    (H M R : ℝ) (hH : H ≠ 0) (hM : M ≠ 0) (hR : R ≠ 0)
    (q : ArchimedeanTraceTorus K) :
    compactMixedJIntegrand u w v huc hwc hvc H M R hH hM hR q =
      ∑ p : compactIntegerSupport w hwc M hM × compactIntegerSupport w hwc M hM,
        (w (M⁻¹ • mixedEmbedding K ((p.1:𝓞 K):K))*
          conj (w (M⁻¹ • mixedEmbedding K ((p.2:𝓞 K):K)))) *
          compactTraceNonzeroCubicSum u huc H hH
            (traceTorusMul ((p.1:𝓞 K)^6-(p.2:𝓞 K)^6) q) *
          ((‖compactTraceWeylSum 3 v hvc R hR (traceTorusMul 4 q)‖^4 : ℝ):ℂ) := by
  unfold compactMixedJIntegrand
  rw [← Finset.sum_coe_sort ((compactIntegerSupport u huc H hH).erase 0)]
  simp only [compactTraceWeylSum]
  rw [trace_sixth_square_cubic_exchange]
  simp_rw [← compactTraceNonzeroCubicSum_eq_traceWeylSum]
  exact Finset.sum_mul _ _ _

end WaringSiegel.WSL3Poisson
