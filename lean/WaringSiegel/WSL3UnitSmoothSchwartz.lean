import WaringSiegel.WSL3UnitSmoothProfile
import Mathlib.Analysis.Distribution.FourierSchwartz

/-!
# Actual Schwartz source phases for Poisson summation

The fixed product weight is smooth and compactly supported, hence Schwartz.
Its polynomial trace modulation is also a genuine Schwartz function, with
all hypotheses derived. This concerns the source variable, and does not
assert uniform root-frequency decay as the polynomial parameter varies.
-/
noncomputable section
open MeasureTheory
open scoped NumberField Classical SchwartzMap ContDiff
open NumberField NumberField.mixedEmbedding WaringSiegel.WSL2
namespace WaringSiegel.WSL3
variable {K : Type*} [Field K] [NumberField K]
set_option maxHeartbeats 800000

def smoothRootWeightSchwartz (ρ R : ℝ) (hρ : 0 < ρ) (hR : 0 < R) : 𝓢(mixedSpace K, ℝ) :=
  (smoothRootWeight_hasCompactSupport ρ R hρ hR).toSchwartzMap (smoothRootWeight_contDiff ρ R)

/-- Every derivative of the one fixed weight has an actual uniform bound. -/
theorem smoothRootWeight_derivative_bound (ρ R : ℝ) (hρ : 0 < ρ) (hR : 0 < R) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : mixedSpace K, ‖iteratedFDeriv ℝ n (smoothRootWeight ρ R) x‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := (smoothRootWeightSchwartz (K := K) ρ R hρ hR).decay 0 n
  exact ⟨C, hC, fun x => by simpa only [pow_zero, one_mul] using hb x⟩

theorem archimedeanTraceCharacter_contDiff (β : mixedSpace K) :
    ContDiff ℝ ∞ (archimedeanTraceCharacter β) := by
  have ht : ContDiff ℝ ∞ (archimedeanTrace (K := K)) :=
    (LinearMap.toContinuousLinearMap (archimedeanTrace (K := K))).contDiff
  unfold archimedeanTraceCharacter
  exact Complex.contDiff_exp.comp (contDiff_const.mul
    (Complex.ofRealCLM.contDiff.comp (ht.comp (contDiff_const.mul contDiff_id))))

def smoothRootPhaseSchwartz (k : ℕ) (ρ R : ℝ) (hρ : 0 < ρ) (hR : 0 < R)
    (β : mixedSpace K) : 𝓢(mixedSpace K, ℂ) :=
  ((smoothRootWeight_hasCompactSupport ρ R hρ hR).smul_right
    (f' := fun x : mixedSpace K => archimedeanTraceCharacter β (x^k))).toSchwartzMap
      ((smoothRootWeight_contDiff ρ R).smul
        ((archimedeanTraceCharacter_contDiff β).comp (contDiff_id.pow k)))

@[simp]
theorem smoothRootPhaseSchwartz_apply (k : ℕ) (ρ R : ℝ) (hρ : 0 < ρ) (hR : 0 < R)
    (β x : mixedSpace K) :
    smoothRootPhaseSchwartz k ρ R hρ hR β x =
      smoothRootWeight ρ R x • archimedeanTraceCharacter β (x^k) := rfl

theorem weightedRootIntegral_eq_integral_schwartz (k : ℕ) (ρ R : ℝ) (hρ : 0 < ρ) (hR : 0 < R)
    (β : mixedSpace K) :
    weightedRootIntegral k (smoothRootWeight ρ R) β =
      ∫ x, smoothRootPhaseSchwartz k ρ R hρ hR β x := rfl

end WaringSiegel.WSL3
