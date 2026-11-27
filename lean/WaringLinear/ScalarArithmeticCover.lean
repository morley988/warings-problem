import WaringLinear.ScalarMarkedStates
import WaringSiegel.WSL2TraceMultiplication

/-! # Exact fibres and Haar normalization of scalar Waring dilations -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter
open scoped BigOperators Classical
namespace WaringLinear

def circleCover (n : ℕ) : ScalarTorus →+ ScalarTorus where
  toFun x := n • x
  map_zero' := nsmul_zero n
  map_add' := fun x y => nsmul_add x y n

@[simp] theorem circleCover_apply (n : ℕ) (x : ScalarTorus) : circleCover n x=n • x := rfl

theorem continuous_circleCover (n : ℕ) : Continuous (circleCover n) :=
  continuous_id.nsmul n

theorem measurePreserving_circleCover (n : ℕ) (hn : 0<n) :
    MeasurePreserving (circleCover n) volume volume := by
  have hf := continuous_circleCover n
  have surj : Function.Surjective (circleCover n) := by
    intro y
    obtain ⟨t,rfl⟩ := Quotient.exists_rep y
    refine ⟨((t/(n:ℝ) : ℝ) : ScalarTorus),?_⟩
    rw [circleCover_apply,←AddCircle.coe_nsmul,nsmul_eq_mul,show (n:ℝ)*(t/(n:ℝ))=t by field_simp]
  let μ := (volume : Measure ScalarTorus)
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    simpa using (inferInstance : IsProbabilityMeasure (AddCircle.haarAddCircle (T:=1)))
  have hp : Tendsto (circleCover n) (cocompact ScalarTorus) (cocompact ScalarTorus) := by
    rw [cocompact_eq_bot]
    exact tendsto_bot
  letI : IsAddHaarMeasure (Measure.map (circleCover n) μ) :=
    Measure.isAddHaarMeasure_map μ _ hf surj hp
  letI : IsProbabilityMeasure (Measure.map (circleCover n) μ) :=
    Measure.isProbabilityMeasure_map hf.measurable.aemeasurable
  exact ⟨hf.measurable,isAddHaarMeasure_eq_of_isProbabilityMeasure _ _⟩

/-- Completely explicit list of the additive characters of denominator
dividing n, as a bijection with 0,1,...,n−1. -/
noncomputable def scalarKernelEquiv (n : ℕ) (hn : 0<n) : Fin n ≃ (circleCover n).ker := by
  let f : Fin n → (circleCover n).ker := fun a =>
    ⟨((a.val:ℝ)/(n:ℝ) : ℝ),by
      apply (AddCircle.nsmul_eq_zero_iff hn).mpr
      exact ⟨a.val,a.isLt,by simp⟩⟩
  have hn' : 0<(n:ℝ) := by exact_mod_cast hn
  have mem (a:Fin n) : (a.val:ℝ)/(n:ℝ)∈Set.Ico (0:ℝ) (0+1) := by
    constructor
    · positivity
    · rw [div_lt_iff₀ hn']
      simp
  apply Equiv.ofBijective f
  constructor
  · intro a b h
    have h' := (AddCircle.coe_eq_coe_iff_of_mem_Ico (mem a) (mem b)).mp
      (congrArg Subtype.val h)
    apply Fin.ext
    exact_mod_cast (div_left_inj' hn'.ne').mp h'
  · intro y
    obtain ⟨a,ha,h⟩ := (AddCircle.nsmul_eq_zero_iff hn).mp (AddMonoidHom.mem_ker.mp y.property)
    refine ⟨⟨a,ha⟩,Subtype.ext ?_⟩
    simpa [f] using h

/-- The fibre normalization for multiplication by n, on the genuine
unit circle and its normalized Lebesgue measure. -/
noncomputable def circleKernelFintype (n : ℕ) (hn : 0<n) : Fintype (circleCover n).ker :=
  Fintype.ofEquiv (Fin n) (scalarKernelEquiv n hn)

theorem scalar_kernel_card (n : ℕ) (hn : 0<n) :
    @Fintype.card (circleCover n).ker (circleKernelFintype n hn)=n := by
  letI := circleKernelFintype n hn
  simpa using Fintype.card_congr (scalarKernelEquiv n hn).symm

theorem scalarPowerSum_continuous (s : Finset ℕ) (k : ℕ) :
    Continuous (scalarPowerSum s k) := continuous_finset_sum _ fun _ _ => (fourier _).continuous

#print axioms scalar_kernel_card
#print axioms measurePreserving_circleCover
end WaringLinear
