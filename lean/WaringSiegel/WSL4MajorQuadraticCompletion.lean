import WaringSiegel.WSL3MomentShiftedCompletion
import WaringSiegel.WSL3MomentExactSliceKernel

/-! # Quadratic common translations with the completion twist retained -/
noncomputable section
set_option maxHeartbeats 1200000
open MeasureTheory NumberField NumberField.mixedEmbedding Module
open scoped BigOperators Classical NumberField SchwartzMap
namespace WaringSiegel.WSL4
open WSL2 WSL3 WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]
variable {α : Type*} [Fintype α]

local instance {ι : Type*} [Fintype ι] : IsProbabilityMeasure (latticeHaar (ι := ι)) := by
  unfold latticeHaar
  infer_instance

theorem quadratic_completed_sum_norm (nodes : α → 𝓞 K) (z : 𝓞 K)
    (P : ℝ) (θ β : mixedSpace K) :
    ‖completedFiniteSum (fun a => mixedEmbedding K (nodes a:K))
      (fun a => latticeCharacter (integerCoordinates K ((nodes a+z)^2))
        (archimedeanTorusHom θ)) P β‖ =
    ‖frequencySum (fun a => integerCoordinates K (nodes a))
      (fun a => latticeCharacter (integerCoordinates K ((nodes a)^2)) (archimedeanTorusHom θ) *
        latticeCharacter (integerCoordinates K (nodes a)) (archimedeanTorusHom (P⁻¹ • β)))
      (archimedeanTorusHom ((2:ℝ) • θ * mixedEmbedding K (z:K)))‖ := by
  have he : completedFiniteSum (fun a => mixedEmbedding K (nodes a:K))
      (fun a => latticeCharacter (integerCoordinates K ((nodes a+z)^2))
        (archimedeanTorusHom θ)) P β =
      latticeCharacter (integerCoordinates K (z^2)) (archimedeanTorusHom θ) *
      frequencySum (fun a => integerCoordinates K (nodes a))
        (fun a => latticeCharacter (integerCoordinates K ((nodes a)^2)) (archimedeanTorusHom θ) *
          latticeCharacter (integerCoordinates K (nodes a)) (archimedeanTorusHom (P⁻¹ • β)))
        (archimedeanTorusHom ((2:ℝ) • θ * mixedEmbedding K (z:K))) := by
    unfold completedFiniteSum frequencySum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    dsimp only
    rw [← latticeCharacter_integer_arch (nodes a) (P⁻¹ • β)]
    have hg := latticeCharacter_shifted_top_coefficient 2 z (nodes a) θ
    norm_num only [Nat.cast_ofNat] at hg
    rw [hg]
    have hpow : (nodes a+z)^2=z^2+((nodes a)^2+(2:𝓞 K)*z*nodes a) := by ring
    rw [hpow]
    simp only [map_add,latticeCharacter_add]
    ring
  rw [he,norm_mul,norm_latticeCharacter_eq_one,one_mul]

theorem sliceMoment_zero_one (nodes : α → 𝓞 K) (w : α → ℂ)
    (β : NumberFieldCoordinateIndex K → AddCircle (1:ℝ)) :
    sliceMoment 1 (vinogradovFrequency (integerCoordinates K) 0 nodes)
      (fun a => integerCoordinates K ((nodes a)^1)) w β =
      ‖frequencySum (fun a => integerCoordinates K (nodes a)) w β‖^2 := by
  have hv : vinogradovFrequency (integerCoordinates K) 0 nodes = fun _ => 0 := by
    funext a j
    exact Fin.elim0 j.1
  simp only [sliceMoment,hv,frequencySum,latticeCharacter_zero,mul_one,pow_one]
  simp

theorem integral_quadratic_linear_twist_sq (nodes : α → 𝓞 K)
    (hinj : Function.Injective nodes) (w : α → ℂ) (hw : ∀ a, ‖w a‖=1) :
    (∫ β, ‖frequencySum (fun a => integerCoordinates K (nodes a)) w β‖^2
      ∂latticeHaar) = Fintype.card α := by
  have hi : Function.Injective (fun a => integerCoordinates K (nodes a)) :=
    (integerCoordinates_injective K).comp hinj
  rw [integral_norm_frequencySum_sq,Fintype.sum_prod_type]
  simp only [hi.eq_iff,Finset.sum_ite_eq,Finset.mem_univ,if_true]
  simp only [Complex.mul_conj',Complex.ofReal_pow,Complex.ofReal_re,hw,one_pow,
    Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
  norm_num

theorem quadratic_completed_average_bound (D : ℝ) (hD : 0≤D) :
    ∃ C : ℝ, 0<C ∧ ∀ B H : ℝ, 1≤B → B^2≤H →
      ∀ θ : mixedSpace K,
      (Submodule.Quotient.mk θ : ArchimedeanTraceTorus K) ∉
        traceMajorArcUnion (B*H) ((2:ℝ)^finrank ℚ K*B^finrank ℚ K) →
      ∀ Y : Finset (𝓞 K), (∀ z∈Y, ∀ v : InfinitePlace K, v (z:K)≤B) →
      ∀ {α : Type*} [Fintype α] (nodes : α → 𝓞 K), Function.Injective nodes →
      (∀ x y : α, ∀ v : InfinitePlace K, v ((nodes x-nodes y:𝓞 K):K)≤D*H) →
      ∀ P : ℝ, ∀ β : mixedSpace K,
      (∑ z : Y, ‖completedFiniteSum (fun a => mixedEmbedding K (nodes a:K))
        (fun a => latticeCharacter (integerCoordinates K ((nodes a+z.val)^2))
          (archimedeanTorusHom θ)) P β‖^2) ≤ C*H^finrank ℚ K*(Fintype.card α) := by
  obtain ⟨C,hC,hb⟩ := monomial_slice_shifted_minor_bound_exact (K := K) D hD
  refine ⟨C,hC,?_⟩
  intro B H hB hBH θ hminor Y hY α inst nodes hinj hnodes P β
  let w : α → ℂ := fun a =>
    latticeCharacter (integerCoordinates K ((nodes a)^2)) (archimedeanTorusHom θ) *
      latticeCharacter (integerCoordinates K (nodes a)) (archimedeanTorusHom (P⁻¹ • β))
  have hw (a : α) : ‖w a‖=1 := by
    simp only [w,norm_mul,norm_latticeCharacter_eq_one,mul_one]
  have h := hb B H hB hBH θ 2 (by norm_num) hminor Y hY nodes w 0 1 (by
    intro x y v
    simpa only [zero_add,pow_one,Fin.sum_univ_one] using hnodes (x 0) (y 0) v)
  simp_rw [sliceMoment_zero_one] at h
  rw [integral_quadratic_linear_twist_sq nodes hinj w hw] at h
  simpa only [quadratic_completed_sum_norm] using h

#print axioms quadratic_completed_sum_norm
#print axioms quadratic_completed_average_bound
end WaringSiegel.WSL4
