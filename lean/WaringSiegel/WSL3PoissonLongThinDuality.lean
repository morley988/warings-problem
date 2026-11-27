import WaringSiegel.WSL3PoissonLongThinLattice

/-!
# The original lattice as the true Euclidean dual of the long-thin lattice

The trace-frequency map is literal Riesz duality for the algebra trace.
Consequently its complex factors are present in the resulting quadratic form.
-/

noncomputable section
open MeasureTheory Module NumberField NumberField.mixedEmbedding WaringSiegel.WSL3
open scoped BigOperators Classical NumberField nonZeroDivisors RealInnerProductSpace
namespace WaringSiegel.WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

/-- Actual original-side vector, dual to the sheared and scaled trace lattice. -/
def longThinOriginalPoint (θ : mixedSpace K) (P H : ℝ) (u v : mixedSpace K) : DoubleMixed K :=
  (doubleMixedToProduct (K:=K)).symm
    (P • traceFrequency (u+θ*v), -(P*H)⁻¹ • traceFrequency v)

theorem longThinOriginalPoint_norm_sq (θ : mixedSpace K) (P H : ℝ) (u v : mixedSpace K) :
    ‖longThinOriginalPoint θ P H u v‖^2 =
      P^2 * ‖traceFrequency (u+θ*v)‖^2 + (P*H)⁻¹^2 * ‖traceFrequency v‖^2 := by
  rw [longThinOriginalPoint, WithLp.prod_norm_sq_eq_of_L2]
  change ‖P • traceFrequency (u+θ*v)‖^2 + ‖(-(P*H)⁻¹:ℝ) • traceFrequency v‖^2 = _
  rw [_root_.norm_smul, _root_.norm_smul, mul_pow, mul_pow,
    Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs, neg_sq]

/-- The two displayed vectors pair by the literal algebraic trace, exactly. -/
theorem longThin_original_pairing (θ : mixedSpace K) (P H : ℝ)
    (hP : P ≠ 0) (hH : H ≠ 0) (u v y a : mixedSpace K) :
    inner ℝ (longThinOriginalPoint θ P H u v) (longThinPoint θ P H y a) =
      archimedeanTrace (u*y) + archimedeanTrace (v*a) := by
  change inner ℝ (P • traceFrequency (u+θ*v)) ((euclidean.toMixed K).symm (P⁻¹ • y)) +
    inner ℝ (-(P*H)⁻¹ • traceFrequency v) ((euclidean.toMixed K).symm ((P*H) • (θ*y-a))) = _
  rw [map_smul, map_smul, real_inner_smul_left, real_inner_smul_right,
    real_inner_smul_left, real_inner_smul_right,
    traceFrequency_inner, traceFrequency_inner,
    ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply]
  have hcancel :
      P * (P⁻¹ * archimedeanTrace ((u+θ*v)*y)) +
        -(P*H)⁻¹ * ((P*H)*archimedeanTrace (v*(θ*y-a))) =
      archimedeanTrace ((u+θ*v)*y) - archimedeanTrace (v*(θ*y-a)) := by
    field_simp
    ring
  rw [hcancel]
  rw [← map_sub]
  have h : (u+θ*v)*y - v*(θ*y-a) = u*y+v*a := by ring
  rw [h, map_add]

/-- True original lattice indices, in the coordinate order of the dual basis. -/
def longThinOriginalCoordinates : (inverseDifferent K × 𝓞 K) ≃ (DoubleIndex K → ℤ) :=
  ((inverseDifferentCoordinatesEquiv K).toEquiv.prodCongr
    (integerCoordinatesEquiv K).toEquiv).trans
      (Equiv.sumArrowEquivProdArrow _ _ _).symm

theorem longThinBaseBasis_equivFun_inl (x y : mixedSpace K) (i : NumberFieldCoordinateIndex K) :
    (longThinBaseBasis (K:=K)).equivFunL (x,y) (Sum.inl i) =
      (NumberField.mixedEmbedding.latticeBasis K).equivFunL x i := rfl

theorem longThinBaseBasis_equivFun_inr (x y : mixedSpace K) (i : NumberFieldCoordinateIndex K) :
    (longThinBaseBasis (K:=K)).equivFunL (x,y) (Sum.inr i) = archimedeanDualCoordinates y i := rfl

theorem longThinBasis_point_coordinates (θ : mixedSpace K) (P H : ℝ)
    (hP : P ≠ 0) (hH : H ≠ 0) (y a : mixedSpace K) :
    (longThinBasis θ P H hP hH).equivFunL (longThinPoint θ P H y a) =
      (longThinBaseBasis (K:=K)).equivFunL (y,a) := by
  change (longThinBaseBasis (K:=K)).equivFunL
    ((longThinMap θ P H hP hH).symm
      (doubleToMixed ((doubleToMixed (K:=K)).symm (longThinMap θ P H hP hH (y,a))))) = _
  rw [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.symm_apply_apply]

/-- The explicit original vector is the actual Euclidean dual-basis vector. -/
theorem longThinOriginal_basisDualCoordinates (θ : mixedSpace K) (P H : ℝ)
    (hP : P ≠ 0) (hH : H ≠ 0) (p : inverseDifferent K × 𝓞 K) :
    basisDualCoordinates (longThinBasis θ P H hP hH)
      (intVector (longThinOriginalCoordinates p)) =
        longThinOriginalPoint θ P H (mixedEmbedding K (p.1:K)) (mixedEmbedding K (p.2:K)) := by
  apply ext_inner_right ℝ
  intro x
  obtain ⟨q, rfl⟩ := ((longThinMap θ P H hP hH).trans (doubleToMixed (K:=K)).symm).surjective x
  change inner ℝ (basisDualCoordinates (longThinBasis θ P H hP hH)
    (intVector (longThinOriginalCoordinates p))) (longThinPoint θ P H q.1 q.2) =
    inner ℝ (longThinOriginalPoint θ P H (mixedEmbedding K (p.1:K))
      (mixedEmbedding K (p.2:K))) (longThinPoint θ P H q.1 q.2)
  rw [basisDualCoordinates_inner, longThinBasis_point_coordinates, Fintype.sum_sum_type,
    longThin_original_pairing θ P H hP hH]
  simp only [longThinBaseBasis_equivFun_inl, longThinBaseBasis_equivFun_inr]
  change (∑ i, (inverseDifferentCoordinatesEquiv K p.1 i:ℝ) *
      (NumberField.mixedEmbedding.latticeBasis K).equivFunL q.1 i) +
    (∑ i, (integerCoordinatesEquiv K p.2 i:ℝ) * archimedeanDualCoordinates q.2 i) = _
  rw [mul_comm (mixedEmbedding K (p.1:K)) q.1, trace_pairing_bases,
    archimedeanDualCoordinates_inverseDifferent, archimedeanTrace_pairing_eq_coordinates]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    change _ = _ * (inverseDifferentCoordinatesEquiv K p.1 i:ℝ)
    ring
end WaringSiegel.WSL3Poisson
