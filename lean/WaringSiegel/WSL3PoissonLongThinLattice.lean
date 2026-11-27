import WaringSiegel.WSL3PoissonLongThinSpace
import WaringSiegel.WSL3PoissonNumberFieldCovolume

/-!
# Actual long-thin lattice, its integral coordinates and covolume

The basis below is the image of `O_K × different⁻¹` under precisely the shear
and scales occurring in WSL2. Its norm is the literal WSL2 quadratic form.
-/

noncomputable section
open MeasureTheory Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open scoped BigOperators Classical NumberField nonZeroDivisors RealInnerProductSpace
namespace WaringSiegel.WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

abbrev DoubleIndex K [Field K] [NumberField K] :=
  NumberFieldCoordinateIndex K ⊕ NumberFieldCoordinateIndex K

def longThinBaseBasis : Basis (DoubleIndex K) ℝ (mixedSpace K × mixedSpace K) :=
  (NumberField.mixedEmbedding.latticeBasis K).prod (archimedeanTraceDualBasis (K:=K))

def longThinBasis (θ : mixedSpace K) (P H : ℝ) (hP : P ≠ 0) (hH : H ≠ 0) :
    Basis (DoubleIndex K) ℝ (DoubleMixed K) :=
  ((longThinBaseBasis (K:=K)).map (longThinMap θ P H hP hH).toLinearEquiv).map
    (doubleToMixed (K:=K)).symm.toLinearEquiv

def longThinPoint (θ : mixedSpace K) (P H : ℝ) (y a : mixedSpace K) : DoubleMixed K :=
  (doubleToMixed (K:=K)).symm (P⁻¹ • y, (P*H) • (θ*y-a))

theorem mixedSquareNorm_smul (r : ℝ) (x : mixedSpace K) :
    mixedSquareNorm (r • x) = r^2 * mixedSquareNorm x := by
  rw [mixedSquareNorm_eq_euclidean, map_smul, _root_.norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs, mixedSquareNorm_eq_euclidean]

theorem longThinPoint_norm_sq (θ : mixedSpace K) (P H : ℝ) (y a : mixedSpace K) :
    ‖longThinPoint θ P H y a‖^2 =
      mixedSquareNorm y/P^2 + (P*H)^2*mixedSquareNorm (θ*y-a) := by
  rw [longThinPoint, doubleToMixed_norm_sq, mixedSquareNorm_smul, mixedSquareNorm_smul]
  simp only [inv_pow, div_eq_mul_inv]
  ring

theorem longThinBasis_coordinates (θ : mixedSpace K) (P H : ℝ)
    (hP : P ≠ 0) (hH : H ≠ 0) (r : DoubleIndex K → ℝ) :
    (longThinBasis θ P H hP hH).equivFunL.symm r =
      longThinPoint θ P H
        ((NumberField.mixedEmbedding.latticeBasis K).equivFunL.symm (r ∘ Sum.inl))
        ((archimedeanTraceDualBasis (K:=K)).equivFunL.symm (r ∘ Sum.inr)) := by
  apply (longThinBasis θ P H hP hH).equivFunL.injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  have hmap (y a : mixedSpace K) :
      (longThinBasis θ P H hP hH).equivFunL (longThinPoint θ P H y a) =
        (longThinBaseBasis (K:=K)).equivFunL (y,a) := by
    change (longThinBaseBasis (K:=K)).equivFunL
      ((longThinMap θ P H hP hH).symm
        (doubleToMixed ((doubleToMixed (K:=K)).symm (longThinMap θ P H hP hH (y,a))))) = _
    rw [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.symm_apply_apply]
  rw [hmap]
  ext i
  cases i with
  | inl i => exact (congrFun ((NumberField.mixedEmbedding.latticeBasis K).equivFunL.apply_symm_apply
      (r ∘ Sum.inl)) i).symm
  | inr i => exact (congrFun ((archimedeanTraceDualBasis (K:=K)).equivFunL.apply_symm_apply
      (r ∘ Sum.inr)) i).symm

/-- A genuine bijection from actual algebraic lattice points to all integer coordinates. -/
def longThinPairCoordinates : (𝓞 K × inverseDifferent K) ≃ (DoubleIndex K → ℤ) :=
  ((integerCoordinatesEquiv K).toEquiv.prodCongr
    (inverseDifferentCoordinatesEquiv K).toEquiv).trans
      (Equiv.sumArrowEquivProdArrow _ _ _).symm

theorem longThinPair_coordinates (θ : mixedSpace K) (P H : ℝ)
    (hP : P ≠ 0) (hH : H ≠ 0) (p : 𝓞 K × inverseDifferent K) :
    (longThinBasis θ P H hP hH).equivFunL.symm (intVector (longThinPairCoordinates p)) =
      longThinPoint θ P H (mixedEmbedding K (p.1:K)) (mixedEmbedding K (p.2:K)) := by
  rw [longThinBasis_coordinates]
  change longThinPoint θ P H
    ((NumberField.mixedEmbedding.latticeBasis K).equivFunL.symm
      (intVector (integerCoordinatesEquiv K p.1)))
    ((archimedeanTraceDualBasis (K:=K)).equivFunL.symm
      (intVector (inverseDifferentCoordinatesEquiv K p.2))) = _
  rw [integer_basis_coordinates, inverseDifferent_basis_coordinates]

/-- WSL2's actual subtype of allowed pairs is precisely the product lattice. -/
def longThinDomainEquiv : longThinDualDomain (inverseDifferent K) ≃ (𝓞 K × inverseDifferent K) where
  toFun p := (p.1.1, ⟨p.1.2, p.2⟩)
  invFun p := ⟨(p.1, p.2), p.2.2⟩
  left_inv p := by cases p; rfl
  right_inv p := by cases p; rfl

theorem longThinBasis_covolume (θ : mixedSpace K) (P H : ℝ)
    (hP : P ≠ 0) (hH : 0 < H) :
    basisCovolume (longThinBasis θ P H hP hH.ne') =
      H^(finrank ℚ K) / (4:ℝ)^nrComplexPlaces K := by
  letI : SecondCountableTopology (mixedSpace K) := inferInstance
  letI : SigmaCompactSpace (mixedSpace K) := inferInstance
  letI : BorelSpace (mixedSpace K × mixedSpace K) := inferInstance
  letI : MeasureTheory.Measure.IsAddHaarMeasure
      (volume : Measure (mixedSpace K × mixedSpace K)) := by
    change MeasureTheory.Measure.IsAddHaarMeasure ((volume : Measure (mixedSpace K)).prod volume)
    exact MeasureTheory.Measure.prod.instIsAddHaarMeasure volume volume
  unfold longThinBasis
  rw [basisCovolume_map_measurePreserving _ _ doubleToMixed_symm_measurePreserving,
    basisCovolume_map, longThinMap_abs_det θ P H hP hH, longThinBaseBasis, basisCovolume_prod,
    trace_lattice_covolume_product, div_eq_mul_inv]

end WaringSiegel.WSL3Poisson
