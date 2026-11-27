import WaringSiegel.WSL4MajorQuadraticCompletion
import WaringSiegel.WSL3MomentTranslationSupport
import WaringSiegel.WSL3PoissonMixedTorus
import WaringSiegel.WSL3IntegerBoxLower

/-! # Actual smooth quadratic pointwise estimates with a flexible cutoff -/
noncomputable section
set_option maxHeartbeats 1800000
open MeasureTheory NumberField NumberField.mixedEmbedding Module
open scoped BigOperators Classical NumberField SchwartzMap
namespace WaringSiegel.WSL4
open WSL2 WSL3 WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

theorem compactTraceQuadraticSum_flexible_bound
    (f : 𝓢(mixedSpace K, ℂ)) (hc : HasCompactSupport (f : mixedSpace K → ℂ)) :
    ∃ C : ℝ, 0<C ∧ ∀ P B H : ℝ, (hP : 1≤P) → 1≤B → B≤P → B^2≤H → P≤H →
      ∀ q : ArchimedeanTraceTorus K,
      q∉traceMajorArcUnion (B*H) ((2:ℝ)^finrank ℚ K*B^finrank ℚ K) →
      ‖compactTraceWeylSum 2 f hc P (by linarith) q‖^2 ≤
        C*P^finrank ℚ K*H^finrank ℚ K/B^finrank ℚ K := by
  obtain ⟨A,hA,hsupport⟩ := compact_support_place_bound (f : mixedSpace K → ℂ) hc
  obtain ⟨c,hcpos,htranslations⟩ := exists_integer_translation_set (K := K)
  obtain ⟨Q,hQ,hkernel⟩ := quadratic_completed_average_bound (K := K) (2*(A+1)) (by linarith)
  let L : ℝ := ∫ β, ‖weightCompletionAmplitude f β‖
  have hL : 0≤L := integral_nonneg (fun _ => norm_nonneg _)
  let D : ℝ := 2*(3:ℝ)^finrank ℚ K*(A+1)^finrank ℚ K
  have hD : 0<D := by dsimp [D]; positivity
  refine ⟨(1+L^2)*Q*D/c,by positivity,?_⟩
  intro P B H hP hB hBP hBH hPH q hminor
  obtain ⟨θ,rfl⟩ := Quotient.exists_rep q
  have hP0 : 0<P := lt_of_lt_of_le zero_lt_one hP
  have hB0 : 0<B := lt_of_lt_of_le zero_lt_one hB
  have hH : 0<H := hP0.trans_le hPH
  let S := compactIntegerSupport f hc P hP0.ne'
  obtain ⟨Y,hY,hcard⟩ := htranslations B hB
  let T := translatedUnion S Y
  have hS : ∀ x∈S, ∀ v : InfinitePlace K, v (x:K)≤A*P := by
    intro x hx v
    exact hsupport P hP0 x ((mem_compactIntegerSupport _ _ _ _ _).mp hx) v
  have hT := translatedUnion_place_bound S Y A P hS (fun y hy v => (hY y hy v).trans hBP)
  have hTcard : (T.card:ℝ)≤D*P^finrank ℚ K := by
    have hh := integer_box_card_bound T ((A+1)*P)
      (one_le_mul_of_one_le_of_one_le (by linarith) hP) hT
    exact hh.trans_eq (by dsimp [D]; rw [mul_pow]; ring)
  let points : T → mixedSpace K := fun a => mixedEmbedding K (a.val:K)
  let a : Y → T → ℂ := fun z x =>
    latticeCharacter (integerCoordinates K ((x.val+z.val)^2)) (archimedeanTorusHom θ)
  let g : Y → mixedSpace K → ℂ := fun z => completedFiniteSum points (a z) P
  let F : ℝ := ‖compactTraceWeylSum 2 f hc P hP0.ne' (Submodule.Quotient.mk θ)‖^2
  have hfinite (z : Y) :
      (∑ x : T, a z x*f (P⁻¹ • (points x-(-mixedEmbedding K (z.val:K))))) =
        compactTraceWeylSum 2 f hc P hP0.ne' (Submodule.Quotient.mk θ) := by
    symm
    change (∑ x : S, f (P⁻¹ • mixedEmbedding K (x.val:K)) *
      latticeCharacter (integerCoordinates K (x.val^2)) (archimedeanTorusHom θ)) = _
    have he := finite_sum_common_translate
      (fun x : 𝓞 K => f (P⁻¹ • mixedEmbedding K (x:K)))
      (fun x => latticeCharacter (integerCoordinates K (x^2)) (archimedeanTorusHom θ))
      S T z.val (fun x hx => (mem_compactIntegerSupport _ _ _ _ _).mpr hx)
      (fun x hx => mem_translatedUnion S Y hx z.property)
    apply he.trans
    apply Finset.sum_congr rfl
    intro x hx
    simp only [a,points,sub_neg_eq_add,map_add]
    ring
  have hcompletion (z : Y) : F≤L*∫ β, ‖weightCompletionAmplitude f β‖*‖g z β‖^2 := by
    have hh := finite_sum_shifted_weight_moment_completion f points (a z) P
      (-mixedEmbedding K (z.val:K)) 1
    simpa only [hfinite,pow_one] using hh
  have hi (z : Y) : Integrable (fun β => ‖weightCompletionAmplitude f β‖*‖g z β‖^2) := by
    apply completionAmplitude_mul_bounded_pow_integrable f (g z)
      (completedFiniteSum_continuous points (a z) P) _
      (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
      (completedFiniteSum_norm_le points (a z) P) 2
  have hg (β : mixedSpace K) : (∑ z : Y, ‖g z β‖^2)≤Q*H^finrank ℚ K*(T.card:ℝ) := by
    have hh := hkernel B H hB hBH θ hminor Y hY (fun x : T => x.val) Subtype.val_injective
      (by
        intro x y v
        have hh := v.val.sub_le_add (x.val:K) (y.val:K)
        change v ((x.val:K)-(y.val:K))≤2*(A+1)*H
        calc
          _ ≤ v (x.val:K)+v (y.val:K) := hh
          _ ≤ (A+1)*P+(A+1)*P := add_le_add (hT x.val x.property v) (hT y.val y.property v)
          _ = 2*(A+1)*P := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hPH (by linarith)) P β
    simpa only [Fintype.card_coe] using hh
  have havg : (Y.card:ℝ)*F≤L^2*(Q*H^finrank ℚ K*(T.card:ℝ)) := by
    calc
      _ = ∑ z : Y, F := by simp
      _ ≤ ∑ z : Y, L*∫ β, ‖weightCompletionAmplitude f β‖*‖g z β‖^2 :=
        Finset.sum_le_sum (fun z _ => hcompletion z)
      _ = L*∫ β, ‖weightCompletionAmplitude f β‖*(∑ z : Y, ‖g z β‖^2) := by
        rw [← Finset.mul_sum,← integral_finset_sum _ (fun z _ => hi z)]
        congr 1
        apply integral_congr_ae
        filter_upwards with β
        rw [Finset.mul_sum]
      _ ≤ L*∫ β, ‖weightCompletionAmplitude f β‖*(Q*H^finrank ℚ K*(T.card:ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ hL
        apply integral_mono
        · simpa only [Finset.mul_sum] using integrable_finset_sum _ (fun z _ => hi z)
        · exact (weightCompletionAmplitude_integrable f).norm.mul_const _
        · intro β
          exact mul_le_mul_of_nonneg_left (hg β) (norm_nonneg _)
      _ = _ := by rw [integral_mul_const]; dsimp only [L]; ring
  have hmain : c*B^finrank ℚ K*F≤(1+L^2)*Q*D*P^finrank ℚ K*H^finrank ℚ K := by
    calc
      _ ≤ (Y.card:ℝ)*F := mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
      _ ≤ L^2*(Q*H^finrank ℚ K*(T.card:ℝ)) := havg
      _ ≤ L^2*(Q*H^finrank ℚ K*(D*P^finrank ℚ K)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hTcard (by positivity)) (sq_nonneg _)
      _ ≤ (1+L^2)*(Q*H^finrank ℚ K*(D*P^finrank ℚ K)) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by ring
  apply (mul_le_mul_left (mul_pos hcpos (pow_pos hB0 (finrank ℚ K)))).mp
  exact hmain.trans_eq (by field_simp [hcpos.ne',(pow_pos hB0 (finrank ℚ K)).ne'])

#print axioms compactTraceQuadraticSum_flexible_bound
end WaringSiegel.WSL4
