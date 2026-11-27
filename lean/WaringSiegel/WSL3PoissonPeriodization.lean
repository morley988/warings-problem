import WaringSiegel.LatticeFourier
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.ContinuousMap.Compact

/-!
# Finite-dimensional integer periodization

The fundamental cube, its Haar normalization, and descent of an actual sum of
integer translates are proved explicitly. These are the geometric/measure
steps of multivariate Poisson summation, with no assumed Poisson identity.
-/

noncomputable section
open MeasureTheory Topology TopologicalSpace
open scoped BigOperators Classical

namespace WaringSiegel.WSL3Poisson
variable {ι : Type*} [Fintype ι]
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

/-- Coordinatewise integer inclusion. -/
def intVector (n : ι → ℤ) : ι → ℝ := fun i => n i

@[simp] theorem intVector_add (m n : ι → ℤ) :
    intVector (m+n) = intVector m + intVector n := by ext i; simp [intVector]
@[simp] theorem intVector_zero : intVector (0 : ι → ℤ) = 0 := by ext i; simp [intVector]
@[simp] theorem intVector_neg (m : ι → ℤ) : intVector (-m) = -intVector m := by
  ext i; simp [intVector]

instance intVectorAction : AddAction (ι → ℤ) (ι → ℝ) where
  vadd n x := intVector n + x
  zero_vadd x := by
    change intVector 0 + x = x
    rw [intVector_zero, zero_add]
  add_vadd m n x := by
    change intVector (m+n)+x = intVector m+(intVector n+x)
    rw [intVector_add, add_assoc]

@[simp] theorem intVector_vadd (n : ι → ℤ) (x : ι → ℝ) :
    n +ᵥ x = intVector n + x := rfl

instance intVectorMeasurableVAdd : MeasurableVAdd (ι → ℤ) (ι → ℝ) where
  measurable_const_vadd n := by
    change Measurable (fun x : ι → ℝ => intVector n+x)
    exact measurable_const.add measurable_id
  measurable_vadd_const x := measurable_of_countable _

instance intVectorInvariant : VAddInvariantMeasure (ι → ℤ) (ι → ℝ) volume where
  measure_preimage_vadd n s hs := measure_preimage_add volume (intVector n) s

/-- The half-open unit cube in the literal real coordinate space. -/
def unitCube : Set (ι → ℝ) := Set.univ.pi fun _ => Set.Ico (0:ℝ) 1

theorem unitCube_measurable : MeasurableSet (unitCube (ι := ι)) :=
  MeasurableSet.pi Set.countable_univ fun _ _ => measurableSet_Ico

theorem unitCube_fundamental :
    IsAddFundamentalDomain (ι → ℤ) (unitCube (ι := ι)) volume := by
  apply IsAddFundamentalDomain.mk' unitCube_measurable.nullMeasurableSet
  intro x
  refine ⟨fun i => -⌊x i⌋, ?_, ?_⟩
  · intro i _
    change (((-⌊x i⌋ : ℤ) : ℝ) + x i) ∈ Set.Ico (0:ℝ) 1
    push_cast
    constructor
    · linarith [Int.floor_le (x i)]
    · linarith [Int.lt_floor_add_one (x i)]
  · intro n hn
    ext i
    have h := hn i (Set.mem_univ i)
    change 0 ≤ (n i:ℝ)+x i ∧ (n i:ℝ)+x i < 1 at h
    have he : ⌊x i⌋ = -n i := Int.floor_eq_iff.mpr (by push_cast; constructor <;> linarith)
    omega

/-- Quotient each real coordinate by the actual integer period. -/
def torusMk (x : ι → ℝ) : UnitAddTorus ι := fun i => (x i : UnitAddCircle)

theorem torusMk_isOpenQuotientMap : IsOpenQuotientMap (torusMk (ι := ι)) :=
  IsOpenQuotientMap.piMap fun _ => QuotientAddGroup.isOpenQuotientMap_mk

theorem torusMk_surjective : Function.Surjective (torusMk (ι := ι)) :=
  torusMk_isOpenQuotientMap.surjective

theorem torusMk_add_intVector (x : ι → ℝ) (n : ι → ℤ) :
    torusMk (x+intVector n) = torusMk x := by
  ext i
  change ((x i + (n i:ℝ) : ℝ) : UnitAddCircle) = (x i : UnitAddCircle)
  rw [AddCircle.coe_add]
  have hn : (((n i : ℝ) : UnitAddCircle)) = 0 :=
    (AddCircle.coe_eq_zero_iff (1:ℝ)).mpr ⟨n i, by simp⟩
  simp [hn]

theorem torusMk_eq_iff (x y : ι → ℝ) :
    torusMk x = torusMk y ↔ ∃ n : ι → ℤ, x = y + intVector n := by
  constructor
  · intro h
    have hi (i : ι) : (((x i-y i : ℝ) : UnitAddCircle)) = 0 := by
      have hi := congrFun h i
      change ((x i : ℝ) : UnitAddCircle) = (y i : UnitAddCircle) at hi
      rw [AddCircle.coe_sub, hi, sub_self]
    choose n hn using fun i => (AddCircle.coe_eq_zero_iff (1:ℝ)).mp (hi i)
    refine ⟨n, ?_⟩
    ext i
    have hni := hn i
    simp only [zsmul_eq_mul, mul_one] at hni
    change x i = y i+(n i:ℝ)
    linarith
  · rintro ⟨n,rfl⟩
    exact torusMk_add_intVector y n

/-- The quotient of the unit cube has the existing probability Haar measure. -/
theorem torusMk_measurePreserving :
    MeasurePreserving (torusMk (ι := ι)) (volume.restrict unitCube) latticeHaar := by
  have h (i : ι) : MeasurePreserving (fun x : ℝ => (x : UnitAddCircle))
      (volume.restrict (Set.Ico (0:ℝ) 1)) AddCircle.haarAddCircle := by
    have h := UnitAddCircle.measurePreserving_mk (0:ℝ)
    rw [zero_add] at h
    rw [Measure.restrict_congr_set Ico_ae_eq_Ioc]
    convert h using 1
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    simp
  have hpi := measurePreserving_pi (fun _ : ι => volume.restrict (Set.Ico (0:ℝ) 1))
    (fun _ => AddCircle.haarAddCircle) h
  change MeasurePreserving (fun x : ι → ℝ => fun i => (x i : UnitAddCircle))
    ((Measure.pi fun _ : ι => (volume : Measure ℝ)).restrict (Set.univ.pi fun _ => Set.Ico (0:ℝ) 1))
    (Measure.pi fun _ : ι => AddCircle.haarAddCircle)
  rw [Measure.restrict_pi_pi]
  exact hpi

/-- Actual sum of all integer translates, before descending to the torus. -/
def realPeriodization (f : (ι → ℝ) → ℂ) (x : ι → ℝ) : ℂ :=
  ∑' n : ι → ℤ, f (x+intVector n)

theorem realPeriodization_add_intVector (f : (ι → ℝ) → ℂ)
    (x : ι → ℝ) (m : ι → ℤ) :
    realPeriodization f (x+intVector m) = realPeriodization f x := by
  unfold realPeriodization
  simpa only [Equiv.coe_addLeft, intVector_add, add_assoc] using
    (Equiv.addLeft m).tsum_eq (fun n : ι → ℤ => f (x+intVector n))

def torusPeriodization (f : (ι → ℝ) → ℂ) (q : UnitAddTorus ι) : ℂ :=
  realPeriodization f (Function.surjInv torusMk_surjective q)

theorem torusPeriodization_mk (f : (ι → ℝ) → ℂ) (x : ι → ℝ) :
    torusPeriodization f (torusMk x) = realPeriodization f x := by
  unfold torusPeriodization
  obtain ⟨n, hn⟩ := (torusMk_eq_iff _ x).mp (Function.surjInv_eq torusMk_surjective (torusMk x))
  rw [hn, realPeriodization_add_intVector]

theorem torusPeriodization_continuous (f : (ι → ℝ) → ℂ)
    (hf : Continuous (realPeriodization f)) : Continuous (torusPeriodization f) := by
  apply torusMk_isOpenQuotientMap.isQuotientMap.continuous_iff.mpr
  simpa only [Function.comp_def, torusPeriodization_mk] using hf

/-- Local normal convergence supplies continuity, rather than assuming it
for the periodized function. -/
theorem realPeriodization_continuous_of_normal (f : C((ι → ℝ), ℂ))
    (hf : ∀ K : Compacts (ι → ℝ), Summable fun n : ι → ℤ =>
      ‖(f.comp (ContinuousMap.addRight (intVector n))).restrict K‖) :
    Continuous (realPeriodization f) := by
  have hs := ContinuousMap.summable_of_locally_summable_norm hf
  have he : realPeriodization f =
      (∑' n : ι → ℤ, f.comp (ContinuousMap.addRight (intVector n))) := by
    funext x
    rw [← ContinuousMap.tsum_apply hs]
    rfl
  rw [he]
  exact ContinuousMap.continuous _

end WaringSiegel.WSL3Poisson
