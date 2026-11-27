import Waring.PolicyCompletionMajorBox
import Waring.PolicyCompletionRestrictedMean
import Waring.MajorTerminalExponent

/-!
# Actual auxiliary major-arc mixed integral from genuine admissibility

This composes the proved auxiliary estimate and the actual restricted smooth
mean. The maximum in the major-terminal exponent comes from the proved
dyadic integration, and the approximation error is retained throughout.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal Classical
namespace Waring.PolicyCompletionMajorIntegral
open PolicyCompletionMajorBox PolicyCompletionMajorBoxRanges
open PolicyCompletionMajorFamily PolicyCompletionSourceMajor
open PolicyCompletionRestrictedMean SmoothMoments RationalHeight AuxiliaryMajorArcs


def boxSmoothLength {j : ℕ} (L : ℝ) (M : Fin j → ℝ) : ℝ := L/(∏ i,M i)

def boxMajorSet {j : ℕ} (k : ℕ) (L R : ℝ) (M : Fin j → ℝ) : Set ℝ :=
  Set.Ioc 0 1 ∩ {α | MajorAtCutoff L ((boxConductor k L M/L)*R^(k*(k-j))) α}

def boxMajorIntegral {j : ℕ} (k s : ℕ) (L Q R : ℝ) (M : Fin j → ℝ) : ℝ :=
  ∫ α in boxMajorSet k L R M,
    ‖boxSourceFamily k L Q R M α‖*‖smoothWeyl k (boxSmoothLength L M) R α‖^(2*s)

theorem continuous_boxSourceFamily {j : ℕ} (k : ℕ) (L Q R : ℝ) (M : Fin j → ℝ) :
    Continuous (boxSourceFamily k L Q R M) := by
  unfold boxSourceFamily sourceFamily integerPolynomialWeyl
  apply continuous_finset_sum
  intro h hh
  apply continuous_finset_sum
  intro m hm
  apply continuous_finset_sum
  intro n hn
  unfold QuadraticModulation.e
  fun_prop

theorem boxMajorSet_measurable {j : ℕ} (k : ℕ) (L R : ℝ) (M : Fin j → ℝ) :
    MeasurableSet (boxMajorSet k L R M) :=
  measurableSet_Ioc.inter (measurableSet_major _ _)

theorem boxConductor_eq_smoothLength {j : ℕ} (k : ℕ) (L : ℝ) (M : Fin j → ℝ) :
    boxConductor k L M=(boxSmoothLength L M)^k := by
  simp only [boxConductor,boxSmoothLength,div_pow]

theorem boxMajorIntegral_lintegral {j : ℕ} (k s : ℕ) (L Q R : ℝ) (M : Fin j → ℝ) :
    ENNReal.ofReal (boxMajorIntegral k s L Q R M)=
      ∫⁻ α,ENNReal.ofReal ‖boxSourceFamily k L Q R M α‖*
        ENNReal.ofReal (‖smoothWeyl k (boxSmoothLength L M) R α‖^(2*s))
          ∂(volume.restrict (boxMajorSet k L R M)) := by
  have hi : IntegrableOn (fun α => ‖boxSourceFamily k L Q R M α‖*
      ‖smoothWeyl k (boxSmoothLength L M) R α‖^(2*s)) (Set.Ioc (0:ℝ) 1) :=
    ((continuous_boxSourceFamily k L Q R M).norm.mul
      ((continuous_smoothWeyl k (boxSmoothLength L M) R).norm.pow (2*s))).integrableOn_Ioc
  have hb := ofReal_integral_eq_lintegral_ofReal
    (hi.mono_set (show boxMajorSet k L R M ⊆ Set.Ioc (0:ℝ) 1 from Set.inter_subset_left))
    (Filter.Eventually.of_forall (fun α => mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) (2*s))))
  simpa only [boxMajorIntegral,ENNReal.ofReal_mul (norm_nonneg _)] using hb

/-- Uniform actual major integral on the source boxes. The only analytic
input is the genuine even smooth-moment admissibility used by the policy. -/
theorem source_box_major_integral {k j s : ℕ} (hk : 1≤k) (hj : j+2≤k) (hs : 1≤s)
    {Δ ε : ℝ} (hadm : AdmissibleExcess k (2*s) Δ) (hε : 0<ε) :
    ∃ η : ℝ,0<η ∧ ∃ C₀ : ℝ,0<C₀ ∧ ∀ (L Q R : ℝ) (M : Fin j → ℝ),
      1≤L → 1≤R → (∀ i,1≤M i) → (∀ i,2≤boxHeights k L M i) →
      1≤boxSmoothLength L M → R≤(boxSmoothLength L M)^η →
      majorSmoothnessThreshold k j≤R^k →
      boxMajorIntegral k s L Q R M ≤
        C₀*L^(ε+max 0 (2*Δ/(k:ℝ)-1/((k-j:ℕ):ℝ)))*L*
          (∏ i,boxHeights k L M i)*(∏ i,M i)*R^j*
          (boxSmoothLength L M)^(((2*s:ℕ):ℝ)-(k:ℝ)) := by
  let δ : ℝ := ε/3
  have hδ : 0<δ := by dsimp [δ]; positivity
  let θ : ℝ := 1/((k-j:ℕ):ℝ)
  have hθ : 0≤θ := by dsimp [θ]; positivity
  let lam : ℝ := 2*Δ/(k:ℝ)
  obtain ⟨CF,hCF,hpoint⟩ := source_box_major_pointwise k j hj hδ
  obtain ⟨η,hη,CG,hCG,hmean⟩ := even_excess_height_lintegral hk hs hadm hδ
  obtain ⟨CT,hCT,hterminal⟩ := MajorTerminalExponent.restricted_major_with_error_epsilon
    (lam := lam) hθ hδ
  refine ⟨η,hη,CF*CG*CT,by positivity,?_⟩
  intro L Q R M hL hR hM hH hY hRY hRlarge
  let Y := boxSmoothLength L M
  let V := boxConductor k L M
  let H := height V
  let A : ℝ := CF*L^δ*L*(∏ i,boxHeights k L M i)*(∏ i,M i)*R^j
  let K : ℝ := CG*Y^(((2*s:ℕ):ℝ)-(k:ℝ)+δ)
  let μ := volume.restrict (boxMajorSet k L R M)
  let g : ℝ → ℝ≥0∞ := fun α => ENNReal.ofReal (‖smoothWeyl k Y R α‖^(2*s))
  let F : ℝ → ℝ≥0∞ := fun α => ENNReal.ofReal ‖boxSourceFamily k L Q R M α‖
  have hLpos : 0<L := zero_lt_one.trans_le hL
  have hYpos : 0<Y := zero_lt_one.trans_le hY
  have hMprod : 1≤∏ i,M i := by
    have hh := Finset.prod_le_prod (s := (Finset.univ : Finset (Fin j)))
      (f := fun _ => (1:ℝ)) (fun _ _ => zero_le_one) (fun i _ => hM i)
    simpa only [Finset.prod_const_one] using hh
  have hHprod : 0<∏ i,boxHeights k L M i :=
    Finset.prod_pos (fun i _ => by linarith [hH i])
  have hA : 0<A := by dsimp [A]; positivity
  have hK : 0<K := by dsimp [K]; positivity
  have hV : V=Y^k := boxConductor_eq_smoothLength k L M
  have hVpos : 0<V := by rw [hV]; positivity
  have hYup : Y≤L := div_le_self hLpos.le hMprod
  have hHmeas : Measurable H := measurable_height hVpos
  have hg : Measurable g := ((continuous_smoothWeyl k Y R).norm.pow (2*s)).measurable.ennreal_ofReal
  have hAmeas := boxMajorSet_measurable k L R M
  have hlo : ∀ᵐ α ∂μ,1≤H α := Filter.Eventually.of_forall (one_le_height V)
  have hhi : ∀ᵐ α ∂μ,H α≤L := by
    filter_upwards [ae_restrict_mem hAmeas] with α hα
    apply source_major_height_upper hLpos hVpos hR
      (show (0:ℝ)≤((k*(k-j):ℕ):ℝ) by positivity)
    simpa only [Real.rpow_natCast] using hα.2
  have hp : ∀ᵐ α ∂μ,F α≤ENNReal.ofReal A*
      (ENNReal.ofReal ((H α)^(-θ))+ENNReal.ofReal (L^(-θ))) := by
    filter_upwards [ae_restrict_mem hAmeas] with α hα
    have hh := hpoint L Q R M hL hR hM hH hRlarge α hα.2
    have hc := ENNReal.ofReal_le_ofReal hh
    simp only [neg_div] at hc
    change F α≤ENNReal.ofReal (A*((H α)^(-θ)+L^(-θ))) at hc
    rw [ENNReal.ofReal_mul hA.le,ENNReal.ofReal_add
      (Real.rpow_nonneg (height_pos _ _).le _) (Real.rpow_nonneg hLpos.le _)] at hc
    exact hc
  have hm (Z : ℝ) (hZ : 1≤Z) (_ : Z≤4*L) :
      (∫⁻ α in {α | H α≤Z},g α ∂μ)≤ENNReal.ofReal K*ENNReal.ofReal (Z^lam) := by
    have hsub : μ≤volume.restrict (Set.Ioc 0 1) := Measure.restrict_mono_set volume Set.inter_subset_left
    have hh := hmean Y hY Z R hZ hR hRY
    rw [← hV] at hh
    exact (lintegral_mono' (Measure.restrict_mono_measure hsub _) le_rfl).trans hh
  have hi := hterminal L hL ℝ μ H F g hHmeas hg hlo hhi
    (ENNReal.ofReal A) (ENNReal.ofReal K) hp hm
  rw [← boxMajorIntegral_lintegral] at hi
  have hcast : ENNReal.ofReal A*ENNReal.ofReal K*
      ENNReal.ofReal (CT*L^(max 0 (lam-θ)+δ))=
      ENNReal.ofReal (A*K*(CT*L^(max 0 (lam-θ)+δ))) := by
    rw [← ENNReal.ofReal_mul hA.le,← ENNReal.ofReal_mul (mul_nonneg hA.le hK.le)]
  rw [hcast] at hi
  have hreal : boxMajorIntegral k s L Q R M≤A*K*(CT*L^(max 0 (lam-θ)+δ)) :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hi
  apply hreal.trans
  have hYδ : Y^δ≤L^δ := Real.rpow_le_rpow hYpos.le hYup hδ.le
  have hsplit : Y^(((2*s:ℕ):ℝ)-(k:ℝ)+δ)=Y^(((2*s:ℕ):ℝ)-(k:ℝ))*Y^δ := Real.rpow_add hYpos _ _
  have hmul := mul_le_mul_of_nonneg_left hYδ (by positivity :
    0≤CF*CG*CT*L^δ*L*(∏ i,boxHeights k L M i)*(∏ i,M i)*R^j*
      Y^(((2*s:ℕ):ℝ)-(k:ℝ))*L^(max 0 (lam-θ)+δ))
  have hpow : L^δ*L^δ*L^(max 0 (lam-θ)+δ)=L^(ε+max 0 (lam-θ)) := by
    rw [← Real.rpow_add hLpos,← Real.rpow_add hLpos]
    congr 1
    dsimp [δ]
    ring
  calc
    _ = (CF*CG*CT*L^δ*L*(∏ i,boxHeights k L M i)*(∏ i,M i)*R^j*
      Y^(((2*s:ℕ):ℝ)-(k:ℝ))*L^(max 0 (lam-θ)+δ))*Y^δ := by
      dsimp [A,K]
      rw [hsplit]
      ring
    _ ≤ (CF*CG*CT*L^δ*L*(∏ i,boxHeights k L M i)*(∏ i,M i)*R^j*
      Y^(((2*s:ℕ):ℝ)-(k:ℝ))*L^(max 0 (lam-θ)+δ))*L^δ := hmul
    _ = _ := by
      calc
        _ = (CF*CG*CT)*(L^δ*L^δ*L^(max 0 (lam-θ)+δ))*L*
            (∏ i,boxHeights k L M i)*(∏ i,M i)*R^j*Y^(((2*s:ℕ):ℝ)-(k:ℝ)) := by ring
        _ = _ := by rw [hpow]

#print axioms continuous_boxSourceFamily
#print axioms boxMajorIntegral_lintegral
#print axioms source_box_major_integral
end Waring.PolicyCompletionMajorIntegral
