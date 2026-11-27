import WaringSiegel.WSL3PoissonTrace
import WaringSiegel.WSL3UnitTraceFrequency

/-!
# Actual trace Fourier transform on Schwartz functions

Riesz trace coordinates identify the literal trace Fourier integral with the
ordinary Fourier transform. This proves its Schwartz decay and lattice
summability, including a product-decay bound uniform in the frequency.
-/

noncomputable section
open MeasureTheory Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  WaringSiegel.WSL2 WaringSiegel.WSL3
open scoped BigOperators Classical NumberField nonZeroDivisors SchwartzMap FourierTransform
namespace WaringSiegel.WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

def traceFourierSchwartz (f : 𝓢(mixedSpace K, ℂ)) : 𝓢(mixedSpace K, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ traceFrequency
    (SchwartzMap.fourierTransformCLM ℂ
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (euclidean.toMixed K) f))

theorem traceFourierSchwartz_apply (f : 𝓢(mixedSpace K, ℂ)) (β : mixedSpace K) :
    traceFourierSchwartz f β = traceFourier f β := by
  have h := traceFrequency_fourier f (-β)
  simpa only [map_neg, neg_neg, traceFourier] using h

theorem schwartz_integerRing_summable (f : 𝓢(mixedSpace K, ℂ)) :
    Summable (fun a : 𝓞 K => f (mixedEmbedding K (a:K))) := by
  have h := (integerCoordinatesEquiv K).toEquiv.summable_iff.mpr
    (schwartz_integer_summable
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (NumberField.mixedEmbedding.latticeBasis K).equivFunL.symm f))
  apply h.congr
  intro a
  change f ((NumberField.mixedEmbedding.latticeBasis K).equivFunL.symm
    (intVector (integerCoordinatesEquiv K a))) = _
  rw [integer_basis_coordinates]

theorem schwartz_inverseDifferent_summable (f : 𝓢(mixedSpace K, ℂ)) :
    Summable (fun a : inverseDifferent K => f (mixedEmbedding K (a:K))) := by
  have h := (inverseDifferentCoordinatesEquiv K).toEquiv.summable_iff.mpr
    (schwartz_integer_summable
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (archimedeanTraceDualBasis (K:=K)).equivFunL.symm f))
  apply h.congr
  intro a
  change f ((archimedeanTraceDualBasis (K:=K)).equivFunL.symm
    (intVector (inverseDifferentCoordinatesEquiv K a))) = _
  rw [inverseDifferent_basis_coordinates]

theorem traceFourier_inverseDifferent_summable (f : 𝓢(mixedSpace K, ℂ)) :
    Summable (fun a : inverseDifferent K => traceFourier f (mixedEmbedding K (a:K))) := by
  simpa only [traceFourierSchwartz_apply] using
    schwartz_inverseDifferent_summable (traceFourierSchwartz f)

def archimedeanProductDecay (m : ℕ) (β : mixedSpace K) : ℝ :=
  ∏ w, 1/(1+normAtPlace w β)^m

theorem archimedeanProductDecay_nonneg (m : ℕ) (β : mixedSpace K) :
    0 ≤ archimedeanProductDecay m β := by
  apply Finset.prod_nonneg
  intro w hw
  have h := normAtPlace_nonneg w β
  positivity

/-- A fixed Schwartz function has arbitrary product decay at all infinite places. -/
theorem schwartz_product_decay (f : 𝓢(mixedSpace K, ℂ)) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ β : mixedSpace K, ‖f β‖ ≤ C * archimedeanProductDecay m β := by
  obtain ⟨C, hC, hb⟩ := schwartz_polynomial_bound f (Fintype.card (InfinitePlace K)*m)
  refine ⟨C+1, by linarith, fun β => ?_⟩
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
  have hbound : ‖f β‖ * (∏ w : InfinitePlace K, (1+normAtPlace w β)^m) ≤ C+1 := by
    calc
      _ ≤ ‖f β‖ * (1+‖β‖)^(Fintype.card (InfinitePlace K)*m) :=
        mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
      _ ≤ C := by simpa only [mul_comm] using hb β
      _ ≤ C+1 := by linarith
  unfold archimedeanProductDecay
  rw [Finset.prod_div_distrib, Finset.prod_const_one, mul_one_div]
  exact (le_div_iff₀ hden).mpr hbound

/-- The actual trace Fourier transform has a constant chosen before all frequencies. -/
theorem traceFourier_product_decay (f : 𝓢(mixedSpace K, ℂ)) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ β : mixedSpace K,
      ‖traceFourier f β‖ ≤ C * archimedeanProductDecay m β := by
  simpa only [traceFourierSchwartz_apply] using schwartz_product_decay (traceFourierSchwartz f) m

end WaringSiegel.WSL3Poisson
