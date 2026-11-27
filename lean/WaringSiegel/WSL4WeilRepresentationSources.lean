import WaringSiegel.WSL4WeilRepresentationFourier
import WaringSiegel.WSL4ArchRootScaled

/-! # The actual auxiliary sources as two finite root families -/
noncomputable section
set_option maxHeartbeats 1000000
namespace WaringSiegel.WSL4Weil
open MeasureTheory NumberField NumberField.mixedEmbedding Module
  WSL2 WSL3 WSL3Poisson WSL4Local WSL4
open scoped NumberField BigOperators Classical SchwartzMap
variable {K : Type*} [Field K] [NumberField K]

def maskedIntegerSupport (w : mixedSpace K → ℂ) (hc : HasCompactSupport w)
    (P : ℝ) (hP : P ≠ 0) (p : ℕ) : Finset (𝓞 K) :=
  (compactIntegerSupport w hc P hP).filter (fun x => IsUnit
    (Ideal.Quotient.mk (Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K))) x))

theorem compactCoprimeTraceCubicSum_eq_traceWeylSum
    (w : mixedSpace K → ℂ) (hc : HasCompactSupport w)
    (P : ℝ) (hP : P ≠ 0) (p : ℕ) (q : ArchimedeanTraceTorus K) :
    compactCoprimeTraceCubicSum w P p q 0 =
      traceWeylSum 3 (fun x : maskedIntegerSupport w hc P hP p => (x : 𝓞 K))
        (fun x => w (P⁻¹ • mixedEmbedding K ((x : 𝓞 K) : K))) q := by
  rw [compactCoprimeTraceCubicSum_eq_finite w hc P hP p]
  unfold finiteLinearTraceSum traceWeylSum
  simp only [traceTorusCharacter_zero,mul_one]
  exact (Finset.sum_coe_sort (maskedIntegerSupport w hc P hP p)
    (fun x : 𝓞 K => w (P⁻¹ • mixedEmbedding K (x : K))*traceTorusCharacter (x^3) q)).symm

theorem compactCoprimeTraceCubicSum_eq_traceCoprimeWeylSum
    (w : mixedSpace K → ℂ) (hc : HasCompactSupport w)
    (P : ℝ) (hP : P ≠ 0) (p : ℕ) (q : ArchimedeanTraceTorus K) :
    compactCoprimeTraceCubicSum w P p q 0 =
      traceCoprimeWeylSum (p : 𝓞 K) 3
        (fun x : compactIntegerSupport w hc P hP => (x : 𝓞 K))
        (fun x => w (P⁻¹ • mixedEmbedding K ((x : 𝓞 K) : K))) q := by
  rw [compactCoprimeTraceCubicSum_eq_finite w hc P hP p]
  unfold finiteLinearTraceSum traceCoprimeWeylSum
  simp only [traceTorusCharacter_zero,mul_one,Finset.sum_filter]
  exact (Finset.sum_coe_sort (compactIntegerSupport w hc P hP)
    (fun x : 𝓞 K => if IsUnit (Ideal.Quotient.mk (Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K))) x)
      then w (P⁻¹ • mixedEmbedding K (x : K))*traceTorusCharacter (x^3) q else 0)).symm

theorem compactTraceCubicSum_mul_eq_scaled_nodes
    (w : mixedSpace K → ℂ) (hc : HasCompactSupport w)
    (P : ℝ) (hP : P ≠ 0) (p : ℕ) (q : ArchimedeanTraceTorus K) :
    compactTraceWeylSum 3 w hc P hP (traceTorusMul ((p : 𝓞 K)^3) q) =
      traceWeylSum 3 (fun x : compactIntegerSupport w hc P hP => (p : 𝓞 K)*(x : 𝓞 K))
        (fun x => w (P⁻¹ • mixedEmbedding K ((x : 𝓞 K) : K))) q := by
  simp only [compactTraceWeylSum,traceWeylSum,mul_pow,traceTorusCharacter_mul]

theorem inverse_scale_prime_mul_embedding (P : ℝ) (p : ℕ) (x : 𝓞 K) :
    P⁻¹ • mixedEmbedding K (((p : 𝓞 K)*x : 𝓞 K) : K) =
      (P/(p : ℝ))⁻¹ • mixedEmbedding K (x : K) := by
  simp only [RingOfIntegers.coe_eq_algebraMap,map_mul,map_natCast]
  rw [← natCast_smul_mixed,smul_smul,inv_div,div_eq_mul_inv]
  congr 1
  ring
end WaringSiegel.WSL4Weil

#print axioms WaringSiegel.WSL4Weil.compactCoprimeTraceCubicSum_eq_traceWeylSum
#print axioms WaringSiegel.WSL4Weil.inverse_scale_prime_mul_embedding

#print axioms WaringSiegel.WSL4Weil.compactCoprimeTraceCubicSum_eq_traceCoprimeWeylSum
