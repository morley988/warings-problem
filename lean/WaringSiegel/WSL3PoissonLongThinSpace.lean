import WaringSiegel.WSL3PoissonCovolume
import WaringSiegel.WSL3PoissonGaussianUnit
import WaringSiegel.WSL3PoissonTrace
import WaringSiegel.WSL3UnitTraceFrequency

/-!
# The actual Euclidean quadratic space for the long-thin lattice

The two mixed archimedean components use their Euclidean norm. The identity
with WSL2's sum of real squares and complex squared moduli is proved below.
The long-thin shear and positive scales are genuine invertible real maps.
-/

noncomputable section
open MeasureTheory MeasureTheory.Measure Module NumberField NumberField.InfinitePlace
  NumberField.mixedEmbedding Topology
open scoped BigOperators Classical NumberField nonZeroDivisors RealInnerProductSpace
namespace WaringSiegel.WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

local instance euclideanMixed_sigmaCompact : SigmaCompactSpace (euclidean.mixedSpace K) :=
  (euclidean.toMixed K).toHomeomorph.isClosedEmbedding.sigmaCompactSpace

/-- WSL2's actual positive quadratic form is precisely the Euclidean squared norm. -/
theorem mixedSquareNorm_eq_euclidean (x : mixedSpace K) :
    mixedSquareNorm x = ‖(euclidean.toMixed K).symm x‖^2 := by
  rw [mixedSquareNorm, InfinitePlace.sum_eq_sum_add_sum,
    WithLp.prod_norm_sq_eq_of_L2, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  congr 1
  · apply Finset.sum_congr rfl
    intro w hw
    rw [normAtPlace_apply_of_isReal w.property]
    rfl
  · apply Finset.sum_congr rfl
    intro w hw
    rw [normAtPlace_apply_of_isComplex w.property]
    rfl

/-- The genuine Euclidean space in dimension twice the field degree. -/
abbrev DoubleMixed (K : Type*) [Field K] :=
  WithLp 2 (euclidean.mixedSpace K × euclidean.mixedSpace K)

instance doubleMixed_measurableSpace : MeasurableSpace (DoubleMixed K) := borel _
instance doubleMixed_borelSpace : BorelSpace (DoubleMixed K) := ⟨rfl⟩

def doubleMixedToProduct : DoubleMixed K ≃L[ℝ]
    (euclidean.mixedSpace K × euclidean.mixedSpace K) :=
  (WithLp.linearEquiv 2 ℝ _).toContinuousLinearEquiv

/-- The L² product and ordinary product volumes agree under the coordinate map. -/
theorem doubleMixedToProduct_measurePreserving :
    MeasurePreserving (doubleMixedToProduct (K:=K)) volume volume := by
  refine ⟨(doubleMixedToProduct (K:=K)).continuous.measurable, ?_⟩
  let b := euclidean.stdOrthonormalBasis K
  rw [← (b.prod b).addHaar_eq_volume, Basis.map_addHaar]
  have h : (b.prod b).toBasis.map (doubleMixedToProduct (K:=K)).toLinearEquiv =
      b.toBasis.prod b.toBasis := by
    ext i : 1
    cases i <;> rfl
  rw [h, Basis.prod_addHaar, b.addHaar_eq_volume]
  rfl

def doubleToMixed : DoubleMixed K ≃L[ℝ] (mixedSpace K × mixedSpace K) :=
  (doubleMixedToProduct (K:=K)).trans ((euclidean.toMixed K).prodCongr (euclidean.toMixed K))

theorem doubleToMixed_measurePreserving :
    MeasurePreserving (doubleToMixed (K:=K)) volume volume :=
  ((euclidean.volumePreserving_toMixed K).prod (euclidean.volumePreserving_toMixed K)).comp
    doubleMixedToProduct_measurePreserving

theorem doubleToMixed_symm_measurePreserving :
    MeasurePreserving (doubleToMixed (K:=K)).symm volume volume := by
  have h : MeasurePreserving (doubleToMixed (K:=K)).toHomeomorph.toMeasurableEquiv :=
    doubleToMixed_measurePreserving
  exact h.symm

theorem doubleMixed_finrank : finrank ℝ (DoubleMixed K) = 2*finrank ℚ K := by
  rw [LinearEquiv.finrank_eq (doubleMixedToProduct (K:=K)).toLinearEquiv,
    Module.finrank_prod, euclidean.finrank]
  ring

theorem doubleToMixed_norm_sq (x y : mixedSpace K) :
    ‖(doubleToMixed (K:=K)).symm (x,y)‖^2 = mixedSquareNorm x + mixedSquareNorm y := by
  rw [WithLp.prod_norm_sq_eq_of_L2, mixedSquareNorm_eq_euclidean, mixedSquareNorm_eq_euclidean]
  rfl

/-- The actual lower triangular shear; it is an involution. -/
def longThinShear (θ : mixedSpace K) : (mixedSpace K × mixedSpace K) ≃L[ℝ]
    (mixedSpace K × mixedSpace K) :=
  ({ toFun := fun p => (p.1, θ*p.1-p.2)
     invFun := fun p => (p.1, θ*p.1-p.2)
     left_inv := by intro p; apply Prod.ext <;> dsimp <;> abel
     right_inv := by intro p; apply Prod.ext <;> dsimp <;> abel
     map_add' := by
       intro p q
       apply Prod.ext
       · rfl
       · simp only [Prod.fst_add, Prod.snd_add, mul_add, sub_add_sub_comm]
     map_smul' := by
       intro r p
       apply Prod.ext
       · rfl
       · change θ * (r • p.1) - r • p.2 = r • (θ*p.1-p.2)
         rw [mul_smul_comm, smul_sub] } :
     (mixedSpace K × mixedSpace K) ≃ₗ[ℝ] (mixedSpace K × mixedSpace K)).toContinuousLinearEquiv

theorem longThinShear_involution (θ : mixedSpace K) :
    (longThinShear θ).toLinearMap.comp (longThinShear θ).toLinearMap = LinearMap.id := by
  apply LinearMap.ext
  intro p
  change (p.1, θ*p.1-(θ*p.1-p.2)) = p
  apply Prod.ext
  · rfl
  · dsimp
    abel

theorem longThinShear_abs_det (θ : mixedSpace K) :
    |LinearMap.det (longThinShear θ).toLinearMap| = 1 := by
  have h := congrArg LinearMap.det (longThinShear_involution θ)
  rw [LinearMap.det_comp, LinearMap.det_id] at h
  have habs : |LinearMap.det (longThinShear θ).toLinearMap|^2 = 1 := by
    rw [sq, ← abs_mul, h, abs_one]
  have hn := abs_nonneg (LinearMap.det (longThinShear θ).toLinearMap)
  nlinarith

/-- Independent positive scales after the actual shear. -/
def longThinScale (P H : ℝ) (hP : P ≠ 0) (hH : H ≠ 0) :
    (mixedSpace K × mixedSpace K) ≃L[ℝ] (mixedSpace K × mixedSpace K) :=
  ((LinearEquiv.smulOfNeZero ℝ (mixedSpace K) P⁻¹ (inv_ne_zero hP)).prodCongr
    (LinearEquiv.smulOfNeZero ℝ (mixedSpace K) (P*H) (mul_ne_zero hP hH))).toContinuousLinearEquiv

def longThinMap (θ : mixedSpace K) (P H : ℝ) (hP : P ≠ 0) (hH : H ≠ 0) :
    (mixedSpace K × mixedSpace K) ≃L[ℝ] (mixedSpace K × mixedSpace K) :=
  (longThinShear θ).trans (longThinScale P H hP hH)

theorem longThinMap_apply (θ : mixedSpace K) (P H : ℝ) (hP : P ≠ 0) (hH : H ≠ 0)
    (p : mixedSpace K × mixedSpace K) :
    longThinMap θ P H hP hH p = (P⁻¹ • p.1, (P*H) • (θ*p.1-p.2)) := rfl

theorem longThinScale_det (P H : ℝ) (hP : P ≠ 0) (hH : H ≠ 0) :
    LinearMap.det (longThinScale (K:=K) P H hP hH).toLinearMap = H^(finrank ℚ K) := by
  change LinearMap.det ((P⁻¹ • (LinearMap.id : mixedSpace K →ₗ[ℝ] mixedSpace K)).prodMap
    ((P*H) • (LinearMap.id : mixedSpace K →ₗ[ℝ] mixedSpace K))) = _
  rw [LinearMap.det_prodMap, LinearMap.det_smul, LinearMap.det_smul,
    LinearMap.det_id, mul_one, mul_one, mixedEmbedding.finrank, inv_pow, mul_pow]
  field_simp

theorem longThinMap_abs_det (θ : mixedSpace K) (P H : ℝ) (hP : P ≠ 0) (hH : 0 < H) :
    |LinearMap.det (longThinMap θ P H hP hH.ne').toLinearMap| = H^(finrank ℚ K) := by
  change |LinearMap.det ((longThinScale P H hP hH.ne').toLinearMap.comp
    (longThinShear θ).toLinearMap)| = _
  rw [LinearMap.det_comp, abs_mul, longThinScale_det, longThinShear_abs_det,
    mul_one, abs_of_nonneg (pow_nonneg hH.le _)]

end WaringSiegel.WSL3Poisson
