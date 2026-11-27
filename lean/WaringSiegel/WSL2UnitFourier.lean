import WaringSiegel.WSL2UnitDensity
import WaringSiegel.WSL2ArchimedeanTrace
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Literal Fourier factorization for the archimedean Waring density

The phase is the exponential of the actual real-algebra trace pairing on
R^r₁ × C^r₂. The Fourier transform of the genuine sum-of-powers density is
proved to be the (s+1)-st power of the actual one-root oscillatory integral.
This fixes the exact Fourier integrand without assuming an inversion theorem.
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped NumberField BigOperators Classical
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
namespace WaringSiegel.WSL2
variable {K : Type*} [Field K] [NumberField K]
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

/-- The genuine trace Fourier phase, with positive exponential sign. -/
def archimedeanTraceCharacter (β x : mixedSpace K) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (archimedeanTrace (β * x) : ℂ))

theorem archimedeanTraceCharacter_continuous (β : mixedSpace K) :
    Continuous (archimedeanTraceCharacter β) := by
  have htr : Continuous (archimedeanTrace (K := K)) :=
    (archimedeanTrace (K := K)).continuous_of_finiteDimensional
  unfold archimedeanTraceCharacter
  fun_prop

theorem archimedeanTraceCharacter_add (β x y : mixedSpace K) :
    archimedeanTraceCharacter β (x + y) =
      archimedeanTraceCharacter β x * archimedeanTraceCharacter β y := by
  simp only [archimedeanTraceCharacter, mul_add, map_add, Complex.ofReal_add, Complex.exp_add]

theorem archimedeanTraceCharacter_sum {ι : Type*} (β : mixedSpace K)
    (T : Finset ι) (f : ι → mixedSpace K) :
    archimedeanTraceCharacter β (∑ i ∈ T, f i) = ∏ i ∈ T, archimedeanTraceCharacter β (f i) := by
  simp only [archimedeanTraceCharacter, Finset.mul_sum, map_sum, Complex.ofReal_sum,
    Complex.exp_sum]

theorem archimedeanTraceCharacter_norm (β x : mixedSpace K) :
    ‖archimedeanTraceCharacter β x‖ = 1 := by
  simp [archimedeanTraceCharacter, Complex.norm_exp, Complex.mul_re]

theorem archimedeanTraceCharacter_waringMap (k s : ℕ) (β : mixedSpace K)
    (x : ArchimedeanTupleSpace K s) :
    archimedeanTraceCharacter β (archimedeanWaringMap k s x) =
      archimedeanTraceCharacter β (x.1 ^ k) *
        ∏ i, archimedeanTraceCharacter β ((x.2 i) ^ k) := by
  rw [archimedeanWaringMap, archimedeanTraceCharacter_add,
    archimedeanTraceCharacter_sum]

/-- The actual root-box oscillatory integral occurring in the singular integral. -/
def archimedeanRootIntegral (k : ℕ) (ρ R : ℝ) (β : mixedSpace K) : ℂ :=
  ∫ x in rootBox K ρ R, archimedeanTraceCharacter β (x ^ k)

/-- Direct Fourier factorization of the actual finite pushforward measure. -/
theorem archimedeanWaringMeasure_fourier (k s : ℕ) (ρ R : ℝ) (β : mixedSpace K) :
    (∫ b, archimedeanTraceCharacter β b ∂archimedeanWaringMeasure k s ρ R) =
      archimedeanRootIntegral k ρ R β ^ (s + 1) := by
  letI : BorelSpace (ArchimedeanTupleSpace K s) := inferInstance
  letI : SigmaFinite (volume : Measure (Fin s → mixedSpace K)) := by
    change SigmaFinite (Measure.pi fun _ : Fin s => (volume : Measure (mixedSpace K)))
    exact Measure.pi.sigmaFinite _
  have hf : Measurable (archimedeanWaringMap (K := K) k s) := by
    apply Continuous.measurable
    unfold archimedeanWaringMap
    fun_prop
  let D := rootBox K ρ R
  let T : Set (Fin s → mixedSpace K) := {y | ∀ i, y i ∈ D}
  have hT : T = Set.univ.pi (fun _ : Fin s => D) := by ext y; simp [T]
  have hpi : (volume : Measure (Fin s → mixedSpace K)).restrict T =
      Measure.pi (fun _ : Fin s => volume.restrict D) := by
    rw [hT]
    exact Measure.restrict_pi_pi (fun _ : Fin s => (volume : Measure (mixedSpace K))) (fun _ => D)
  unfold archimedeanWaringMeasure
  rw [integral_map hf.aemeasurable
    (archimedeanTraceCharacter_continuous β).aestronglyMeasurable]
  simp_rw [archimedeanTraceCharacter_waringMap]
  change (∫ x : ArchimedeanTupleSpace K s,
    archimedeanTraceCharacter β (x.1 ^ k) *
      ∏ i, archimedeanTraceCharacter β ((x.2 i) ^ k)
      ∂((volume.prod volume).restrict (D ×ˢ T))) = _
  rw [← Measure.prod_restrict]
  rw [integral_prod_mul (fun x : mixedSpace K => archimedeanTraceCharacter β (x ^ k))
    (fun y : Fin s → mixedSpace K => ∏ i, archimedeanTraceCharacter β ((y i) ^ k))]
  rw [hpi, integral_fintype_prod_eq_pow (fun x : mixedSpace K => archimedeanTraceCharacter β (x ^ k))]
  simp only [Fintype.card_fin, archimedeanRootIntegral, D, pow_succ, mul_comm]

/-- The Fourier transform of the genuine Lebesgue density has the literal
product integrand used by the circle method. -/
theorem archimedeanWaringDensity_fourier (k s : ℕ) (hk : 0 < k)
    (ρ R : ℝ) (hρ : 0 < ρ) (β : mixedSpace K) :
    (∫ b, (archimedeanWaringDensity k s ρ R b).toReal • archimedeanTraceCharacter β b) =
      archimedeanRootIntegral k ρ R β ^ (s + 1) := by
  exact (integral_rnDeriv_smul
    (archimedeanWaringMeasure_absolutelyContinuous (K := K) k s hk ρ R hρ)).trans
      (archimedeanWaringMeasure_fourier k s ρ R β)

end WaringSiegel.WSL2

#print axioms WaringSiegel.WSL2.archimedeanWaringMeasure_fourier
#print axioms WaringSiegel.WSL2.archimedeanWaringDensity_fourier
