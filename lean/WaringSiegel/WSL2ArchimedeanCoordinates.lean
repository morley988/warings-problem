import WaringSiegel.WSL2Conductor

/-!
# WSL2: continuous archimedean trace-dual coordinates

Rational linear maps of K extend canonically to the mixed archimedean
space using its actual integral lattice basis. In particular the algebraic
trace-dual basis extends to a real basis, so its coordinate map is a genuine
continuous linear equivalence, not merely an algebraic map on K.
-/

noncomputable section
open scoped NumberField nonZeroDivisors BigOperators Classical
open NumberField NumberField.mixedEmbedding Module

namespace WaringSiegel
variable {K : Type*} [Field K] [NumberField K]

def extendFieldLinearMap (f : K →ₗ[ℚ] K) : mixedSpace K →ₗ[ℝ] mixedSpace K :=
  (NumberField.mixedEmbedding.latticeBasis K).constr ℝ
    (fun i => mixedEmbedding K (f (NumberField.integralBasis K i)))

theorem extendFieldLinearMap_apply_field (f : K →ₗ[ℚ] K) (x : K) :
    extendFieldLinearMap f (mixedEmbedding K x) = mixedEmbedding K (f x) := by
  rw [extendFieldLinearMap, Basis.constr_apply_fintype]
  simp only [Basis.equivFun_apply, NumberField.mixedEmbedding.latticeBasis_repr_apply]
  calc
    _ = ∑ i, mixedEmbedding K (f ((NumberField.integralBasis K).repr x i •
        NumberField.integralBasis K i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [map_smul, map_rat_smul, Rat.cast_smul_eq_qsmul]
    _ = mixedEmbedding K (f (∑ i, (NumberField.integralBasis K).repr x i •
        NumberField.integralBasis K i)) := by rw [map_sum, map_sum]
    _ = _ := by rw [Basis.sum_repr]

theorem extendFieldLinearMap_id :
    extendFieldLinearMap (LinearMap.id : K →ₗ[ℚ] K) = LinearMap.id := by
  apply (NumberField.mixedEmbedding.latticeBasis K).ext
  intro i
  simp only [NumberField.mixedEmbedding.latticeBasis_apply,
    extendFieldLinearMap_apply_field, LinearMap.id_apply]

theorem extendFieldLinearMap_comp (f g : K →ₗ[ℚ] K) :
    extendFieldLinearMap (f.comp g) = (extendFieldLinearMap f).comp (extendFieldLinearMap g) := by
  apply (NumberField.mixedEmbedding.latticeBasis K).ext
  intro i
  simp only [NumberField.mixedEmbedding.latticeBasis_apply, LinearMap.comp_apply,
    extendFieldLinearMap_apply_field]

def extendFieldLinearEquiv (e : K ≃ₗ[ℚ] K) : mixedSpace K ≃ₗ[ℝ] mixedSpace K where
  toLinearMap := extendFieldLinearMap e.toLinearMap
  invFun := extendFieldLinearMap e.symm.toLinearMap
  left_inv x := by
    have h : (extendFieldLinearMap e.symm.toLinearMap).comp
        (extendFieldLinearMap e.toLinearMap) = LinearMap.id := by
      apply (NumberField.mixedEmbedding.latticeBasis K).ext
      intro i
      simp only [NumberField.mixedEmbedding.latticeBasis_apply, LinearMap.comp_apply,
        extendFieldLinearMap_apply_field, LinearEquiv.coe_coe,
        LinearEquiv.symm_apply_apply, LinearMap.id_apply]
    exact LinearMap.congr_fun h x
  right_inv x := by
    have h : (extendFieldLinearMap e.toLinearMap).comp
        (extendFieldLinearMap e.symm.toLinearMap) = LinearMap.id := by
      apply (NumberField.mixedEmbedding.latticeBasis K).ext
      intro i
      simp only [NumberField.mixedEmbedding.latticeBasis_apply, LinearMap.comp_apply,
        extendFieldLinearMap_apply_field, LinearEquiv.coe_coe,
        LinearEquiv.apply_symm_apply, LinearMap.id_apply]
    exact LinearMap.congr_fun h x

@[simp] theorem extendFieldLinearEquiv_apply_field (e : K ≃ₗ[ℚ] K) (x : K) :
    extendFieldLinearEquiv e (mixedEmbedding K x) = mixedEmbedding K (e x) :=
  extendFieldLinearMap_apply_field e.toLinearMap x

@[simp] theorem extendFieldLinearEquiv_symm_apply_field (e : K ≃ₗ[ℚ] K) (x : K) :
    (extendFieldLinearEquiv e).symm (mixedEmbedding K x) = mixedEmbedding K (e.symm x) :=
  extendFieldLinearMap_apply_field e.symm.toLinearMap x

def archimedeanTraceDualBasis : Basis (NumberFieldCoordinateIndex K) ℝ (mixedSpace K) :=
  (NumberField.mixedEmbedding.latticeBasis K).map
    (extendFieldLinearEquiv ((NumberField.integralBasis K).equiv
      (integralTraceDualBasis K) (Equiv.refl _)))

theorem archimedeanTraceDualBasis_apply (i : NumberFieldCoordinateIndex K) :
    archimedeanTraceDualBasis i = mixedEmbedding K (integralTraceDualBasis K i) := by
  simp only [archimedeanTraceDualBasis, Basis.map_apply,
    NumberField.mixedEmbedding.latticeBasis_apply,
    extendFieldLinearEquiv_apply_field, Basis.equiv_apply, Equiv.refl_apply]

theorem archimedeanTraceDualBasis_repr_field (x : K) (i : NumberFieldCoordinateIndex K) :
    (archimedeanTraceDualBasis (K := K)).repr (mixedEmbedding K x) i =
      ((integralTraceDualBasis K).repr x i : ℝ) := by
  simp only [archimedeanTraceDualBasis, Basis.map_repr, LinearEquiv.trans_apply,
    extendFieldLinearEquiv_symm_apply_field,
    NumberField.mixedEmbedding.latticeBasis_repr_apply]
  congr 1
  simp [Basis.equiv]

/-- The actual real coordinate equivalence underlying the coordinate torus. -/
def archimedeanDualCoordinates : mixedSpace K ≃L[ℝ] (NumberFieldCoordinateIndex K → ℝ) :=
  (archimedeanTraceDualBasis (K := K)).equivFun.toContinuousLinearEquiv

theorem archimedeanDualCoordinates_field (x : K) (i : NumberFieldCoordinateIndex K) :
    archimedeanDualCoordinates (mixedEmbedding K x) i =
      ((integralTraceDualBasis K).repr x i : ℝ) :=
  archimedeanTraceDualBasis_repr_field x i

end WaringSiegel
