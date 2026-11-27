import WaringSiegel.WSL4MajorFlexibleAverage
import WaringSiegel.WSL3MomentLocalized

/-! # Localized Vinogradov moments for a flexible conductor cutoff -/
noncomputable section
set_option maxHeartbeats 1200000
open MeasureTheory NumberField NumberField.mixedEmbedding Module GafniTao
open scoped BigOperators Classical NumberField SchwartzMap
namespace WaringSiegel.WSL4
open WSL2 WSL3 WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

def flexibleMinorArcs (k : ℕ) (B H : ℝ) : Set (ArchimedeanTraceTorus K) :=
  (traceMajorArcUnion (B*H) ((k:ℝ)^finrank ℚ K * B^finrank ℚ K))ᶜ

theorem flexibleMinorArcs_measurable (k : ℕ) (B H : ℝ) (hB : 0<B) (hH : 0<H) :
    MeasurableSet (flexibleMinorArcs (K := K) k B H) :=
  (traceMajorArcUnion_measurableSet _ _ (mul_pos hB hH)).compl

theorem compactTraceWeylSum_flexible_minor_majorant
    (f : 𝓢(mixedSpace K, ℂ)) (hc : HasCompactSupport (f : mixedSpace K → ℂ))
    (R s : ℕ) (hR : 1≤R) (hs : 1≤s) :
    ∃ C A : ℝ, 0<C ∧ 1≤A ∧ ∀ P B H : ℝ,
      (hP : 1≤P) → 1≤B → B≤P → B^2≤H → P^(R+1)≤H →
      ∃ T : Finset (𝓞 K),
        (∀ x∈T, ∀ v : InfinitePlace K, v (x:K)≤A*P) ∧
        ∀ q∈flexibleMinorArcs (K := K) (R+2) B H,
          ‖compactTraceWeylSum (R+2) f hc P (by linarith) q‖^(2*s) ≤
            C*(P^finrank ℚ K)^wooleyTriangular R * H^finrank ℚ K / B^finrank ℚ K *
              monomialSliceIntegral (integerCoordinates K) R s (fun a : T => a.val)
                (archimedeanTraceTorusContinuousAddEquiv q) := by
  obtain ⟨A,hA,hsupport⟩ := compact_support_place_bound (f : mixedSpace K → ℂ) hc
  obtain ⟨c,hcpos,htranslations⟩ := exists_integer_translation_set (K := K)
  obtain ⟨Q,hQ,havg⟩ := smoothLowerMoment_flexible_minor_average f R s hR hs A (by linarith)
  obtain ⟨I,hI,hinsert⟩ := numberField_pointwise_insertion_bound (K := K) R s hs
  let D : ℝ := (A^finrank ℚ K)^wooleyTriangular R
  have hD : 0<D := by dsimp [D]; positivity
  refine ⟨I*D*Q/c,A+1,by positivity,by linarith,?_⟩
  intro P B H hP hB hBP hBH hPH
  have hP0 : 0<P := lt_of_lt_of_le zero_lt_one hP
  have hB0 : 0<B := lt_of_lt_of_le zero_lt_one hB
  have hH0 : 0<H := (pow_pos hB0 2).trans_le hBH
  let X : ℝ := P^finrank ℚ K
  let YB : ℝ := B^finrank ℚ K
  have hYB : 0<YB := pow_pos hB0 _
  let S := compactIntegerSupport f hc P hP0.ne'
  obtain ⟨Y,hY,hcard⟩ := htranslations B hB
  have hS : ∀ x∈S, ∀ v : InfinitePlace K, v (x:K)≤A*P := by
    intro x hx v
    exact hsupport P hP0 x ((mem_compactIntegerSupport _ _ _ _ _).mp hx) v
  let T := translatedUnion S Y
  refine ⟨T,translatedUnion_place_bound S Y A P hS (fun y hy v => (hY y hy v).trans hBP),?_⟩
  intro q hq
  obtain ⟨θ,rfl⟩ := Quotient.exists_rep q
  let w : S → ℂ := fun x => f (P⁻¹ • mixedEmbedding K (x.val:K)) *
    latticeCharacter (integerCoordinates K (x.val^(R+2))) (archimedeanTorusHom θ)
  let M := smoothLowerMoment f R s S P θ
  let G := monomialSliceIntegral (integerCoordinates K) R s (fun a : T => a.val)
    (archimedeanTorusHom θ)
  have hM : 0≤M := smoothLowerMoment_nonneg f R s S P θ
  have hi := hinsert (A*P) (one_le_mul_of_one_le_of_one_le hA hP)
    (fun x : S => x.val) (fun x v => hS x.val x.property v) w
  have ha := havg P B H hP hB hBP hBH hPH S Y
    (fun x hx => (mem_compactIntegerSupport _ _ _ _ _).mpr hx) hS hY θ hq
  have hiscale : ((A*P)^finrank ℚ K)^wooleyTriangular R = D*X^wooleyTriangular R := by
    simp only [mul_pow,D,X]
  change ‖∑ x : S,w x‖^(2*s)≤I*((A*P)^finrank ℚ K)^wooleyTriangular R*M at hi
  rw [hiscale] at hi
  change ‖∑ x : S,w x‖^(2*s)≤(I*D*Q/c)*X^wooleyTriangular R*H^finrank ℚ K/YB*G
  apply (mul_le_mul_left (mul_pos hcpos hYB)).mp
  calc
    c*YB*‖∑ x : S,w x‖^(2*s)≤c*YB*(I*(D*X^wooleyTriangular R)*M) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ = I*(D*X^wooleyTriangular R)*(c*YB*M) := by ring
    _ ≤ I*(D*X^wooleyTriangular R)*((Y.card:ℝ)*M) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcard hM) (by positivity)
    _ ≤ I*(D*X^wooleyTriangular R)*(Q*H^finrank ℚ K*G) :=
      mul_le_mul_of_nonneg_left ha (by positivity)
    _ = _ := by field_simp [hcpos.ne',hYB.ne'] <;> ring

theorem compactTraceWeylSum_flexible_localized_moment
    (f : 𝓢(mixedSpace K, ℂ)) (hc : HasCompactSupport (f : mixedSpace K → ℂ))
    (R s : ℕ) (hR : 1≤R) (hs : 1≤s) :
    ∃ C A : ℝ, 0<C ∧ 1≤A ∧ ∀ P B H : ℝ,
      (hP : 1≤P) → 1≤B → B≤P → B^2≤H → P^(R+1)≤H →
      ∃ T : Finset (𝓞 K),
        (∀ x∈T, ∀ v : InfinitePlace K, v (x:K)≤A*P) ∧
        (∫ q in flexibleMinorArcs (K := K) (R+2) B H,
          ‖compactTraceWeylSum (R+2) f hc P (by linarith) q‖^(2*s) ∂traceHaar) ≤
            C*(P^finrank ℚ K)^wooleyTriangular R * H^finrank ℚ K / B^finrank ℚ K *
              (vinogradovCount (R+2) s (fun a : T => a.val):ℝ) := by
  obtain ⟨C,A,hC,hA,hb⟩ := compactTraceWeylSum_flexible_minor_majorant f hc R s hR hs
  refine ⟨C,A,hC,hA,?_⟩
  intro P B H hP hB hBP hBH hPH
  obtain ⟨T,hT,hbound⟩ := hb P B H hP hB hBP hBH hPH
  refine ⟨T,hT,?_⟩
  have hP0 : 0<P := lt_of_lt_of_le zero_lt_one hP
  have hB0 : 0<B := lt_of_lt_of_le zero_lt_one hB
  have hH0 : 0<H := (pow_pos hB0 2).trans_le hBH
  let F : ArchimedeanTraceTorus K → ℝ :=
    fun q => ‖compactTraceWeylSum (R+2) f hc P hP0.ne' q‖^(2*s)
  let G : ArchimedeanTraceTorus K → ℝ :=
    fun q => monomialSliceIntegral (integerCoordinates K) R s (fun a : T => a.val)
      (archimedeanTraceTorusContinuousAddEquiv q)
  let D : ℝ := C*(P^finrank ℚ K)^wooleyTriangular R*H^finrank ℚ K/B^finrank ℚ K
  have hD : 0≤D := by dsimp [D]; positivity
  have hFcont : Continuous F := (compactTraceWeylSum_continuous _ _ _ _ _).norm.pow _
  have hGcont : Continuous G :=
    (monomialSliceIntegral_continuous (integerCoordinates K) (integerCoordinates_injective K)
      R s (fun a : T => a.val)).comp archimedeanTraceTorusContinuousAddEquiv.continuous
  have hiF : Integrable F traceHaar := hFcont.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hiG : Integrable G traceHaar := hGcont.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hG0 : ∀ q,0≤G q := fun q => monomialSliceIntegral_nonneg _ _ _ _ _
  have hfull : (∫ q,G q ∂traceHaar)=(vinogradovCount (R+2) s (fun a : T => a.val):ℝ) := by
    rw [show G=fun q => monomialSliceIntegral (integerCoordinates K) R s
        (fun a : T => a.val) (archimedeanTraceTorusContinuousAddEquiv q) from rfl,
      traceHaar_integral_coordinates]
    exact integral_monomialSliceIntegral (integerCoordinates K) (integerCoordinates_injective K) R s _
  calc
    _ ≤ ∫ q in flexibleMinorArcs (K := K) (R+2) B H,D*G q ∂traceHaar :=
      setIntegral_mono_on hiF.integrableOn (hiG.const_mul D).integrableOn
        (flexibleMinorArcs_measurable _ _ _ hB0 hH0) hbound
    _ = D*∫ q in flexibleMinorArcs (K := K) (R+2) B H,G q ∂traceHaar := integral_const_mul _ _
    _ ≤ D*∫ q,G q ∂traceHaar := mul_le_mul_of_nonneg_left
      (setIntegral_le_integral hiG (Filter.Eventually.of_forall hG0)) hD
    _ = _ := by rw [hfull]

#print axioms compactTraceWeylSum_flexible_localized_moment
end WaringSiegel.WSL4
