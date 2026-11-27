import WaringSiegel.WSL2TraceHaar
import WaringSiegel.WSL2ArchimedeanTrace
import WaringSiegel.WSL2MomentHuaCubic

/-!
# WSL2: literal trace Weyl sums and Hua moments on V / D⁻¹

The actual quotient, actual real-algebra trace exponential, and probability
Haar measure are linked by proved identities. The newly proved number-field
Hua estimates therefore hold on the manuscript's archimedean trace torus.
-/

noncomputable section
open MeasureTheory
open scoped NumberField BigOperators Classical
open NumberField NumberField.mixedEmbedding

namespace WaringSiegel
variable {K : Type*} [Field K] [NumberField K]

theorem traceTorusCharacter_mk (a : 𝓞 K) (x : mixedSpace K) :
    traceTorusCharacter a (Submodule.Quotient.mk x) =
      Complex.exp (2 * Real.pi * Complex.I *
        (archimedeanTrace (mixedEmbedding K (a : K) * x) : ℂ)) := by
  change latticeCharacter (integerCoordinates K a) (archimedeanTorusHom x) = _
  exact latticeCharacter_archimedeanTorusHom a x

def traceWeylSum {α : Type*} [Fintype α] (k : ℕ) (nodes : α → 𝓞 K)
    (w : α → ℂ) (q : ArchimedeanTraceTorus K) : ℂ :=
  ∑ a, w a * traceTorusCharacter (nodes a ^ k) q

theorem traceWeylSum_coordinates {α : Type*} [Fintype α] (k : ℕ)
    (nodes : α → 𝓞 K) (w : α → ℂ) (q : ArchimedeanTraceTorus K) :
    traceWeylSum k nodes w q = finiteWeylSum (integerCoordinates K) k nodes w
      (archimedeanTraceTorusContinuousAddEquiv q) := rfl

theorem traceWeylSum_mk {α : Type*} [Fintype α] (k : ℕ)
    (nodes : α → 𝓞 K) (w : α → ℂ) (x : mixedSpace K) :
    traceWeylSum k nodes w (Submodule.Quotient.mk x) =
      ∑ a, w a * Complex.exp (2 * Real.pi * Complex.I *
        (archimedeanTrace (mixedEmbedding K ((nodes a ^ k : 𝓞 K) : K) * x) : ℂ)) := by
  simp only [traceWeylSum, traceTorusCharacter_mk]

theorem traceWeylSum_integral_norm_pow {α : Type*} [Fintype α] (k m : ℕ)
    (nodes : α → 𝓞 K) (w : α → ℂ) :
    (∫ q, ‖traceWeylSum k nodes w q‖ ^ m ∂traceHaar) =
      ∫ θ, ‖finiteWeylSum (integerCoordinates K) k nodes w θ‖ ^ m ∂latticeHaar := by
  simp only [traceWeylSum_coordinates]
  exact traceHaar_integral_coordinates (K := K) (E := ℝ)
    (fun θ => ‖finiteWeylSum (integerCoordinates K) k nodes w θ‖ ^ m)

theorem traceWeylSum_integral_product (k s : ℕ)
    {α : Fin s → Type*} [∀ i, Fintype (α i)]
    (nodes : ∀ i, α i → 𝓞 K) (w : ∀ i, α i → ℂ) (ν : 𝓞 K) :
    (∫ q, (∏ i, traceWeylSum k (nodes i) (w i) q) * traceTorusCharacter (-ν) q ∂traceHaar) =
      ∑ x : ∀ i, α i, if (∑ i, nodes i (x i) ^ k) = ν then (∏ i, w i (x i)) else 0 := by
  simp only [traceWeylSum_coordinates, traceTorusCharacter, map_neg]
  exact (traceHaar_integral_coordinates (K := K) (E := ℂ)
    (fun θ => (∏ i, finiteWeylSum (integerCoordinates K) k (nodes i) (w i) θ) *
      latticeCharacter (-integerCoordinates K ν) θ)).trans
    (numberField_integral_Weyl_product K k s nodes w ν)

/-- The first three Hua estimates on the literal archimedean quotient,
uniform in scale, finite node sets, and arbitrary bounded complex weights. -/
theorem traceTorus_low_hua_moments (k j : ℕ) (hj : 1 ≤ j) (hj3 : j ≤ 3)
    (hjk : j ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P → ∀ {α : Type*} [Fintype α],
      ∀ nodes : α → 𝓞 K, Function.Injective nodes →
      (∀ a, ∀ v : InfinitePlace K, v (nodes a : K) ≤ P) →
      ∀ w : α → ℂ, ∀ W : ℝ, 0 ≤ W → (∀ a, ‖w a‖ ≤ W) →
      (∫ q, ‖traceWeylSum k nodes w q‖ ^ (2 ^ j) ∂traceHaar) ≤
        C * (P ^ Module.finrank ℚ K : ℝ) ^ ((2 ^ j - j : ℕ) + ε) * W ^ (2 ^ j) := by
  obtain ⟨C, hC, hbound⟩ := WSL2.numberField_low_hua_moments (K := K) k j hj hj3 hjk hε
  refine ⟨C, hC, ?_⟩
  intro P hP α inst nodes hinj hnodes w W hW hw
  rw [traceWeylSum_integral_norm_pow]
  exact hbound P hP nodes hinj hnodes w W hW hw

end WaringSiegel
