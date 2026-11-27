import WaringSiegel.WSL3IdealPoissonBasis
import WaringSiegel.WSL3PoissonTraceSchwartz

/-!
# Actual fractional-ideal Poisson summation with the trace Fourier transform
-/
noncomputable section
open MeasureTheory Module NumberField NumberField.mixedEmbedding WaringSiegel.WSL2
open scoped BigOperators Classical NumberField nonZeroDivisors SchwartzMap
namespace WaringSiegel.WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

theorem fractional_bases_trace_pairing (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (i j : FractionalIndex I) :
    archimedeanTrace (fractionalIdealLatticeBasis K I i * fractionalArchDualBasis I j) =
      if i = j then 1 else 0 := by
  rw [fractionalIdealLatticeBasis_apply,fractionalArchDualBasis_apply,
    ← map_mul,archimedeanTrace_field]
  change (Algebra.trace ℚ K ((NumberField.basisOfFractionalIdeal K I i)*
    rationalTraceDualBasis K (NumberField.basisOfFractionalIdeal K I) j):ℝ) = _
  rw [← rational_basis_repr_eq_trace,Basis.repr_self,Finsupp.single_apply]
  split_ifs <;> norm_num

theorem fractional_basis_trace_pairing (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (i : FractionalIndex I) (x : mixedSpace K) :
    archimedeanTrace (fractionalIdealLatticeBasis K I i * x) =
      (fractionalArchDualBasis I).repr x i := by
  let b := fractionalArchDualBasis I
  calc
    _ = archimedeanTrace (fractionalIdealLatticeBasis K I i *
        (∑ j, b.repr x j • b j)) := by rw [b.sum_repr]
    _ = ∑ j, b.repr x j * archimedeanTrace (fractionalIdealLatticeBasis K I i*b j) := by
      simp only [Finset.mul_sum,mul_smul_comm,map_sum,map_smul,smul_eq_mul]
    _ = _ := by
      simp only [b,fractional_bases_trace_pairing,mul_ite,mul_one,mul_zero]
      simp

theorem fractional_trace_pairing (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (x y : mixedSpace K) :
    archimedeanTrace (x*y) = ∑ i,
      (fractionalIdealLatticeBasis K I).repr x i * (fractionalArchDualBasis I).repr y i := by
  let b := fractionalIdealLatticeBasis K I
  calc
    _ = archimedeanTrace ((∑ i, b.repr x i • b i)*y) := by rw [b.sum_repr]
    _ = ∑ i, b.repr x i * archimedeanTrace (b i*y) := by
      simp only [Finset.sum_mul,smul_mul_assoc,map_sum,map_smul,smul_eq_mul]
    _ = _ := by simp only [b,fractional_basis_trace_pairing]

theorem fractional_dual_integer_character (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (a : fractionalTraceDual I) (x : mixedSpace K) :
    integerCharacter (-(fractionalDualCoordinatesEquiv I a))
      ((fractionalIdealLatticeBasis K I).equivFunL x) =
        archimedeanTraceCharacter (-(mixedEmbedding K (a:K))) x := by
  rw [integerCharacter_exp,archimedeanTraceCharacter,neg_mul,
    (archimedeanTrace (K:=K)).map_neg,mul_comm (mixedEmbedding K (a:K)) x,
    fractional_trace_pairing I]
  simp_rw [fractionalArchDualBasis_repr_field,← fractionalDualCoordinates_cast]
  simp only [Pi.neg_apply,Int.cast_neg,neg_mul,Finset.sum_neg_distrib,
    Complex.ofReal_neg,Complex.ofReal_sum,Complex.ofReal_mul,Complex.ofReal_intCast,
    Rat.cast_intCast]
  congr 2
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  change ((fractionalDualCoordinatesEquiv I a i : ℤ):ℂ)*
    ((fractionalIdealLatticeBasis K I).repr x i:ℂ) = _
  ring

theorem fractional_basisFourier (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (f : mixedSpace K → ℂ) (a : fractionalTraceDual I) :
    basisFourier (fractionalIdealLatticeBasis K I) f (fractionalDualCoordinatesEquiv I a) =
      traceFourier f (mixedEmbedding K (a:K)) := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    change integerCharacter (-(fractionalDualCoordinatesEquiv I a))
      ((fractionalIdealLatticeBasis K I).equivFunL x)*f x = _
    rw [fractional_dual_integer_character]

/-- Genuine Poisson on any actual nonzero fractional ideal. The dual is
D^-1 I^-1 and the normalizing factor is the actual ideal-lattice covolume. -/
theorem poisson_fractionalIdeal_schwartz (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (f : 𝓢(mixedSpace K,ℂ)) :
    (∑' a : (I : FractionalIdeal (𝓞 K)⁰ K), f (mixedEmbedding K (a:K))) =
      ((FractionalIdeal.absNorm I.1:ℝ)*basisCovolume (NumberField.mixedEmbedding.latticeBasis K))⁻¹ •
        (∑' a : fractionalTraceDual I, traceFourier f (mixedEmbedding K (a:K))) := by
  calc
    _ = ∑' n : FractionalIndex I → ℤ,
        f ((fractionalIdealLatticeBasis K I).equivFunL.symm (intVector n)) := by
      rw [← (fractionalCoordinatesEquiv I).toEquiv.tsum_eq]
      apply tsum_congr
      intro a
      exact congrArg f (fractional_basis_coordinates I a).symm
    _ = _ := by
      rw [poisson_basis_schwartz,fractional_basisCovolume]
      congr 1
      rw [← (fractionalDualCoordinatesEquiv I).toEquiv.tsum_eq]
      apply tsum_congr
      intro a
      exact fractional_basisFourier I f a

/-- Absolute convergence on the actual fractional ideal follows from its
proved arithmetic coordinates and the original Schwartz estimate. -/
theorem schwartz_fractionalIdeal_summable (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (f : 𝓢(mixedSpace K,ℂ)) :
    Summable (fun a : (I : FractionalIdeal (𝓞 K)⁰ K) => f (mixedEmbedding K (a:K))) := by
  have h := (fractionalCoordinatesEquiv I).toEquiv.summable_iff.mpr
    (schwartz_integer_summable
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (fractionalIdealLatticeBasis K I).equivFunL.symm f))
  apply h.congr
  intro a
  change f ((fractionalIdealLatticeBasis K I).equivFunL.symm
    (intVector (fractionalCoordinatesEquiv I a))) = _
  rw [fractional_basis_coordinates]

theorem traceFourier_fractionalIdealDual_summable (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (f : 𝓢(mixedSpace K,ℂ)) :
    Summable (fun a : fractionalTraceDual I => traceFourier f (mixedEmbedding K (a:K))) := by
  simpa only [traceFourierSchwartz_apply] using
    schwartz_fractionalIdeal_summable (Units.mk0 (fractionalTraceDual I) (fractionalTraceDual_ne_zero I))
      (traceFourierSchwartz f)

#print axioms fractional_trace_pairing
#print axioms poisson_fractionalIdeal_schwartz
end WaringSiegel.WSL3Poisson
