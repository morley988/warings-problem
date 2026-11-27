import WaringSiegel.WSL3PoissonNumberFieldCovolume

/-!
# Arithmetic coordinates and trace-dual bases for arbitrary fractional ideals

All lattices below are the actual images of fractional ideals. The trace dual
is identified with the actual product of the inverse different and ideal inverse.
-/
noncomputable section
open MeasureTheory Module NumberField NumberField.mixedEmbedding WaringSiegel.WSL2
open scoped BigOperators Classical NumberField nonZeroDivisors SchwartzMap
namespace WaringSiegel.WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

abbrev FractionalIndex (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) := Free.ChooseBasisIndex ℤ I

def fractionalTraceDual (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K :=
  inverseDifferent K * (I : FractionalIdeal (𝓞 K)⁰ K)⁻¹

theorem fractionalTraceDual_eq_dual (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    fractionalTraceDual I = FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K) := by
  rw [FractionalIdeal.dual_eq_mul_inv, fractionalTraceDual,inverseDifferent_eq_dual]

theorem fractionalTraceDual_ne_zero (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    fractionalTraceDual I ≠ 0 := by
  rw [fractionalTraceDual_eq_dual]
  exact FractionalIdeal.dual_ne_zero ℤ ℚ I.ne_zero

def fractionalRationalDualBasis (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Basis (FractionalIndex I) ℚ K :=
  rationalTraceDualBasis K (NumberField.basisOfFractionalIdeal K I)

theorem span_fractionalRationalDualBasis (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Submodule.span ℤ (Set.range (fractionalRationalDualBasis I)) =
      (fractionalTraceDual I : Submodule (𝓞 K) K).restrictScalars ℤ := by
  have hb : Submodule.span ℤ (Set.range (NumberField.basisOfFractionalIdeal K I)) =
      (I : Submodule (𝓞 K) K).restrictScalars ℤ := by
    ext x
    exact NumberField.mem_span_basisOfFractionalIdeal K
  rw [fractionalTraceDual_eq_dual,FractionalIdeal.coe_dual ℤ ℚ I.ne_zero]
  change Submodule.span ℤ (Set.range (fractionalRationalDualBasis I)) =
    (Algebra.traceForm ℚ K).dualSubmodule ((I : Submodule (𝓞 K) K).restrictScalars ℤ)
  rw [← hb]
  exact ((Algebra.traceForm ℚ K).dualSubmodule_span_of_basis
    (traceForm_nondegenerate ℚ K) (NumberField.basisOfFractionalIdeal K I)).symm

def fractionalCoordinatesEquiv (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    I ≃ₗ[ℤ] (FractionalIndex I → ℤ) := (NumberField.fractionalIdealBasis K I.1).equivFun

def fractionalDualCoordinatesEquiv (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    fractionalTraceDual I ≃ₗ[ℤ] (FractionalIndex I → ℤ) :=
  (LinearEquiv.ofEq _ _ (span_fractionalRationalDualBasis I)).symm.trans
    ((fractionalRationalDualBasis I).restrictScalars ℤ).equivFun

theorem fractionalCoordinates_cast (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (a : (I : FractionalIdeal (𝓞 K)⁰ K)) (i : FractionalIndex I) :
    ((fractionalCoordinatesEquiv I a i : ℤ):ℚ) =
      (NumberField.basisOfFractionalIdeal K I).repr (a:K) i := by
  symm
  exact (NumberField.fractionalIdealBasis K I.1).ofIsLocalizedModule_repr_apply ℚ ℤ⁰
    ((Submodule.subtype (I : Submodule (𝓞 K) K)).restrictScalars ℤ) a i

theorem fractionalDualCoordinates_cast (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (a : fractionalTraceDual I) (i : FractionalIndex I) :
    ((fractionalDualCoordinatesEquiv I a i : ℤ):ℚ) =
      (fractionalRationalDualBasis I).repr (a:K) i := by
  exact Basis.restrictScalars_repr_apply ℤ (fractionalRationalDualBasis I)
    ((LinearEquiv.ofEq _ _ (span_fractionalRationalDualBasis I)).symm a) i

theorem fractionalLatticeBasis_repr_field (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (x : K) (i : FractionalIndex I) :
    (fractionalIdealLatticeBasis K I).repr (mixedEmbedding K x) i =
      ((NumberField.basisOfFractionalIdeal K I).repr x i : ℝ) := by
  let b := NumberField.basisOfFractionalIdeal K I
  have he : mixedEmbedding K x =
      ∑ j, (b.repr x j : ℝ) • fractionalIdealLatticeBasis K I j := by
    conv_lhs => rw [← b.sum_repr x]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_rat_smul, Rat.cast_smul_eq_qsmul, fractionalIdealLatticeBasis_apply]
  rw [he]
  simp only [map_sum, map_smul, Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [Finsupp.finset_sum_apply]
  change (∑ j, (Finsupp.single j (b.repr x j : ℝ)) i) = (b.repr x i : ℝ)
  simp only [Finsupp.single_apply,Finset.sum_ite_eq',Finset.mem_univ,if_true]

def fractionalArchDualBasis (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Basis (FractionalIndex I) ℝ (mixedSpace K) :=
  (fractionalIdealLatticeBasis K I).map
    (extendFieldLinearEquiv ((NumberField.basisOfFractionalIdeal K I).equiv
      (fractionalRationalDualBasis I) (Equiv.refl _)))

theorem fractionalArchDualBasis_apply (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (i : FractionalIndex I) :
    fractionalArchDualBasis I i = mixedEmbedding K (fractionalRationalDualBasis I i) := by
  simp only [fractionalArchDualBasis, Basis.map_apply, fractionalIdealLatticeBasis_apply,
    extendFieldLinearEquiv_apply_field, Basis.equiv_apply, Equiv.refl_apply]

theorem fractionalArchDualBasis_repr_field (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (x : K) (i : FractionalIndex I) :
    (fractionalArchDualBasis I).repr (mixedEmbedding K x) i =
      ((fractionalRationalDualBasis I).repr x i : ℝ) := by
  simp only [fractionalArchDualBasis, Basis.map_repr, LinearEquiv.trans_apply,
    extendFieldLinearEquiv_symm_apply_field, fractionalLatticeBasis_repr_field]
  congr 1
  simp [Basis.equiv]

theorem fractional_basis_coordinates (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (a : (I : FractionalIdeal (𝓞 K)⁰ K)) :
    (fractionalIdealLatticeBasis K I).equivFunL.symm
      (intVector (fractionalCoordinatesEquiv I a)) = mixedEmbedding K (a:K) := by
  apply (fractionalIdealLatticeBasis K I).equivFunL.injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  ext i
  change (fractionalCoordinatesEquiv I a i : ℝ) =
    (fractionalIdealLatticeBasis K I).repr (mixedEmbedding K (a:K)) i
  rw [fractionalLatticeBasis_repr_field, ← fractionalCoordinates_cast]
  norm_cast

theorem fractional_dual_basis_coordinates (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (a : fractionalTraceDual I) :
    (fractionalArchDualBasis I).equivFunL.symm
      (intVector (fractionalDualCoordinatesEquiv I a)) = mixedEmbedding K (a:K) := by
  apply (fractionalArchDualBasis I).equivFunL.injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  ext i
  change (fractionalDualCoordinatesEquiv I a i : ℝ) =
    (fractionalArchDualBasis I).repr (mixedEmbedding K (a:K)) i
  rw [fractionalArchDualBasis_repr_field, ← fractionalDualCoordinates_cast]
  norm_cast

/-- Geometric covolume of the actual ideal lattice, including the field factor. -/
theorem fractional_basisCovolume (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    basisCovolume (fractionalIdealLatticeBasis K I) =
      (FractionalIdeal.absNorm I.1:ℝ)*basisCovolume (NumberField.mixedEmbedding.latticeBasis K) := by
  rw [basisCovolume,basisCovolume,measureReal_def,measureReal_def,
    volume_fundamentalDomain_fractionalIdealLatticeBasis,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by exact_mod_cast FractionalIdeal.absNorm_nonneg I.1)]

#print axioms fractionalTraceDual_eq_dual
#print axioms fractional_basis_coordinates
#print axioms fractional_dual_basis_coordinates
#print axioms fractional_basisCovolume
end WaringSiegel.WSL3Poisson
