import WaringLinear.MomentAbsorption
import WaringSiegel.WSL2TraceMoments

/-! # One-variable replacement for power sums over a number field

The frequency is the actual kth power of an algebraic integer. Every
integral is on the normalized trace torus of the field.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators NumberField Classical
open WaringSiegel WaringSiegel.WSL2

namespace WaringLinear

variable {K : Type*} [Field K] [NumberField K] {α : Type*} [Fintype α]

theorem trace_even_moment_le_one_mixed (k : ℕ) (n : α → 𝓞 K) (a b : α → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hab : ∀ i, a i ≤ b i) (s : ℕ) :
    (∫ q, ‖traceWeylSum k n (fun x => (a x : ℂ)) q‖^(2*(s+1)) ∂traceHaar) ≤
      ∫ q, ‖traceWeylSum k n (fun x => (b x : ℂ)) q‖ *
        ‖traceWeylSum k n (fun x => (a x : ℂ)) q‖^(2*s+1) ∂traceHaar := by
  let v (x : α) := integerCoordinates K (n x ^ k)
  let F := frequencySum v (fun x => (a x : ℂ))
  let f := frequencySum v (fun x => (b x : ℂ))
  calc
    _ = ∫ θ, ‖F θ‖^(2*(s+1)) ∂latticeHaar :=
      traceWeylSum_integral_norm_pow k _ n _
    _ ≤ ∫ θ, ‖f θ‖ * ‖F θ‖^(2*s+1) ∂latticeHaar :=
      even_moment_le_one_mixed v a b ha hab s
    _ = _ := (traceHaar_integral_coordinates (K := K) (E := ℝ)
      (fun θ => ‖f θ‖ * ‖F θ‖^(2*s+1))).symm

private theorem trace_sum_continuous (k : ℕ) (n : α → 𝓞 K) (w : α → ℂ) :
    Continuous (traceWeylSum k n w) :=
  (continuous_frequencySum (fun x => integerCoordinates K (n x^k)) w).comp
    (archimedeanTraceTorusContinuousAddEquiv (K := K)).continuous

/-- A loss-free even moment for the actual trace sums. The ordinary major-arc
moment, ordinary minor-arc saving, and old restricted moment are precisely the
three analytic estimates supplied by the caller. -/
theorem trace_loss_free_of_defect
    (k : ℕ) (n : α → 𝓞 K) (a b : α → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hab : ∀ i, a i ≤ b i) (s m d : ℕ) (horder : m+d = 2*s+1)
    (M : Set (ArchimedeanTraceTorus K)) (hM : MeasurableSet M)
    (P C B A D ρ E : ℝ) (hP : 1 ≤ P) (hC : 0 ≤ C) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hE : E ≤ ρ)
    (hBox : ∀ q ∈ Mᶜ, ‖traceWeylSum k n (fun x => (a x : ℂ)) q‖ ≤ C*P)
    (hMinor : ∀ q ∈ Mᶜ, ‖traceWeylSum k n (fun x => (b x : ℂ)) q‖ ≤ B*P^(1-ρ))
    (hMajor : (∫ q in M, ‖traceWeylSum k n (fun x => (b x : ℂ)) q‖^(m+d+1) ∂traceHaar) ≤
      A*P^((m:ℝ)+d+1-k))
    (hRestricted : (∫ q, ‖traceWeylSum k n (fun x => (a x : ℂ)) q‖^m ∂traceHaar) ≤
      D*P^((m:ℝ)-k+E)) :
    (∫ q, ‖traceWeylSum k n (fun x => (a x : ℂ)) q‖^(m+d+1) ∂traceHaar) ≤
      2*((2:ℝ)^(m+d+1)*A + B*C^d*D)*P^((m:ℝ)+d+1-k) := by
  let F := traceWeylSum k n (fun x => (a x : ℂ))
  let f := traceWeylSum k n (fun x => (b x : ℂ))
  have hF := (trace_sum_continuous k n (fun x => (a x : ℂ))).norm
  have hf := (trace_sum_continuous k n (fun x => (b x : ℂ))).norm
  have hSupport := trace_even_moment_le_one_mixed k n a b ha hab s
  rw [show 2*(s+1) = m+d+1 by omega, ← horder] at hSupport
  exact loss_free_of_defect traceHaar M hM (fun q => ‖F q‖) (fun q => ‖f q‖)
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) m d k P C B A D ρ E hP hC hB hD hE
    hBox hMinor
    ((hF.pow _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    ((hf.pow _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    ((hF.pow _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    ((hf.mul (hF.pow _)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    hSupport hMajor hRestricted

#print axioms trace_even_moment_le_one_mixed
#print axioms trace_loss_free_of_defect

end WaringLinear
