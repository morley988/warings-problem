import WaringSiegel.WSL3MomentExactMinorAverage
import WaringSiegel.WSL3PoissonMixedTorus

/-! # A positive full-system majorant for the actual minor-arc Weyl moment -/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory NumberField NumberField.mixedEmbedding Module GafniTao
open scoped BigOperators Classical NumberField SchwartzMap
namespace WaringSiegel.WSL3
open WSL2 WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

def vinogradovMinorArcs (k : ℕ) (P : ℝ) : Set (ArchimedeanTraceTorus K) :=
  (traceMajorArcUnion (P^k) ((k:ℝ)^finrank ℚ K * P^finrank ℚ K))ᶜ

theorem vinogradovMinorArcs_measurable (k : ℕ) (P : ℝ) (hP : 0 < P) :
    MeasurableSet (vinogradovMinorArcs (K := K) k P) :=
  (traceMajorArcUnion_measurableSet _ _ (by positivity)).compl

/-- One enlarged finite domain is chosen before the top coefficient. Its
positive majorant retains the last power-sum equation upon integration. -/
theorem compactTraceWeylSum_minor_majorant
    (f : 𝓢(mixedSpace K, ℂ)) (hc : HasCompactSupport (f : mixedSpace K → ℂ))
    (R s : ℕ) (hR : 1 ≤ R) (hs : 1 ≤ s) :
    ∃ C A : ℝ, 0 < C ∧ 1 ≤ A ∧ ∀ (P : ℝ) (hP : 1 ≤ P),
      ∃ T : Finset (𝓞 K),
        (∀ x∈T, ∀ v : InfinitePlace K, v (x:K) ≤ A*P) ∧
        ∀ q ∈ vinogradovMinorArcs (K := K) (R+2) P,
          ‖compactTraceWeylSum (R+2) f hc P (by linarith) q‖^(2*s) ≤
            C * (P^finrank ℚ K)^(wooleyTriangular R+R) *
              monomialSliceIntegral (integerCoordinates K) R s (fun a : T => a.val)
                (archimedeanTraceTorusContinuousAddEquiv q) := by
  obtain ⟨A, hA, hsupport⟩ := compact_support_place_bound (f : mixedSpace K → ℂ) hc
  obtain ⟨c, hcpos, htranslations⟩ := exists_integer_translation_set (K := K)
  obtain ⟨B, hB, havg⟩ := smoothLowerMoment_minor_average_exact f R s hR hs A (by linarith)
  obtain ⟨I, hI, hinsert⟩ := numberField_pointwise_insertion_bound (K := K) R s hs
  let D : ℝ := (A^finrank ℚ K)^wooleyTriangular R
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨I*D*B/c, A+1, by positivity, by linarith, ?_⟩
  intro P hP
  have hP0 : 0 < P := lt_of_lt_of_le zero_lt_one hP
  let X : ℝ := P^finrank ℚ K
  have hX : 0 < X := pow_pos hP0 _
  let S := compactIntegerSupport f hc P hP0.ne'
  obtain ⟨Y, hY, hcard⟩ := htranslations P hP
  have hS : ∀ x∈S, ∀ v : InfinitePlace K, v (x:K) ≤ A*P := by
    intro x hx v
    exact hsupport P hP0 x ((mem_compactIntegerSupport _ _ _ _ _).mp hx) v
  let T := translatedUnion S Y
  refine ⟨T, translatedUnion_place_bound S Y A P hS hY, ?_⟩
  intro q hq
  obtain ⟨θ, rfl⟩ := Quotient.exists_rep q
  change ‖compactTraceWeylSum (R+2) f hc P _ (Submodule.Quotient.mk θ)‖^(2*s) ≤ _
  let w : S → ℂ := fun x => f (P⁻¹ • mixedEmbedding K (x.val:K)) *
    latticeCharacter (integerCoordinates K (x.val^(R+2))) (archimedeanTorusHom θ)
  let M := smoothLowerMoment f R s S P θ
  let G := monomialSliceIntegral (integerCoordinates K) R s (fun a : T => a.val)
    (archimedeanTorusHom θ)
  have hM : 0 ≤ M := smoothLowerMoment_nonneg f R s S P θ
  have hG : 0 ≤ G := monomialSliceIntegral_nonneg _ _ _ _ _
  have hi := hinsert (A*P) (one_le_mul_of_one_le_of_one_le hA hP)
    (fun x : S => x.val) (fun x v => hS x.val x.property v) w
  have ha := havg P hP S Y
    (fun x hx => (mem_compactIntegerSupport _ _ _ _ _).mpr hx) hS hY θ hq
  have hiscale : ((A*P)^finrank ℚ K)^wooleyTriangular R = D * X^wooleyTriangular R := by
    simp only [mul_pow, D, X]
  change ‖∑ x : S, w x‖^(2*s) ≤ I*((A*P)^finrank ℚ K)^wooleyTriangular R*M at hi
  rw [hiscale] at hi
  have hsum : compactTraceWeylSum (R+2) f hc P hP0.ne' (Submodule.Quotient.mk θ) =
      ∑ x : S, w x := rfl
  rw [hsum]
  change ‖∑ x : S, w x‖^(2*s) ≤ (I*D*B/c)*X^(wooleyTriangular R+R)*G
  apply (mul_le_mul_left (mul_pos hcpos hX)).mp
  calc
    c*X*‖∑ x : S, w x‖^(2*s) ≤ c*X*(I*(D*X^wooleyTriangular R)*M) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ = I*(D*X^wooleyTriangular R)*(c*X*M) := by ring
    _ ≤ I*(D*X^wooleyTriangular R)*((Y.card:ℝ)*M) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcard hM) (by positivity)
    _ ≤ I*(D*X^wooleyTriangular R)*(B*X^(R+1)*G) :=
      mul_le_mul_of_nonneg_left ha (by positivity)
    _ = c*X*((I*D*B/c)*X^(wooleyTriangular R+R)*G) := by
      rw [pow_add X (wooleyTriangular R) R, pow_succ X R]
      field_simp [hcpos.ne']
      <;> ring

#print axioms compactTraceWeylSum_minor_majorant
end WaringSiegel.WSL3
