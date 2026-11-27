import Waring.ProductBoxMainScale
import Waring.EndgameCompletionBroadArcs

/-! # Integrated narrow-arc error with the explicit fifth cutoff power -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Waring.ProductBox
open EndgameCompletion RestrictedSmoothArcs

def narrowArcIntegral (F : ℝ → ℂ) (δ : ℝ) (p : ArcLabel) : ℂ :=
  ∫ β in -δ..δ,F ((arcLabelRat p : ℝ)+β)

def modelArcIntegrand (k u v L M n : ℕ) (p : ArcLabel) (β : ℝ) : ℂ :=
  mixedMajorModel k u v L M ((p.2 : ZMod (p.1 : ℕ)).val : ℤ) p.1 β*
    fourier (-(n : ℤ)) (((arcLabelRat p : ℝ)+β : ℝ) : AddCircle (1 : ℝ))

def modelArcIntegral (k u v L M n : ℕ) (δ : ℝ) (p : ArcLabel) : ℂ :=
  ∫ β in -δ..δ,modelArcIntegrand k u v L M n p β

theorem continuous_mixedMajorModel (k u v L M q : ℕ) (a : ℤ) :
    Continuous (mixedMajorModel k u v L M a q) := by
  unfold mixedMajorModel
  exact ((continuous_const.mul (continuous_monomialIntegral k ((M : ℝ)^L))).pow u).mul
    ((continuous_const.mul (continuous_productIntegral k L M)).pow v)

theorem continuous_modelArcIntegrand (k u v L M n : ℕ) (p : ArcLabel) :
    Continuous (modelArcIntegrand k u v L M n p) := by
  unfold modelArcIntegrand
  exact (continuous_mixedMajorModel k u v L M p.1 _).mul
    ((fourier (-(n : ℤ))).continuous.comp
      ((AddCircle.continuous_mk' 1).comp (continuous_const.add continuous_id)))

theorem denominatorArcLabels_card_le (S : Finset ℕ+) {N : ℝ} (hN : 0≤N)
    (hQ : ∀ q∈S,(q : ℝ)≤N) : ((denominatorArcLabels S).card : ℝ)≤N^2 := by
  classical
  have hc (q : ℕ+) : Fintype.card (ZMod (q : ℕ))ˣ≤(q : ℕ) := by
    simpa only [ZMod.card] using Fintype.card_le_of_injective
      (fun a : (ZMod (q : ℕ))ˣ => (a : ZMod (q : ℕ))) Units.val_injective
  rw [denominatorArcLabels,Finset.card_sigma,Nat.cast_sum]
  calc
    _ ≤ ∑ _q∈S,N := Finset.sum_le_sum (fun q hq => by
      simpa only [Finset.card_univ] using (Nat.cast_le.mpr (hc q)).trans (hQ q hq))
    _ = (S.card : ℝ)*N := by simp
    _ ≤ N*N := mul_le_mul_of_nonneg_right (denominator_card_le S hN hQ) hN
    _ = _ := (pow_two N).symm

theorem narrowArc_model_error (k u v L M n : ℕ) (hk : 1≤k) (hu : 1≤u)
    (hv : 1≤v) (hL : 1≤L) (hM : 1≤M) (p : ArcLabel) {N : ℝ}
    (hN : 1≤N) (hq : (p.1 : ℝ)≤N) :
    ‖narrowArcIntegral (productIntegrand k u v L M n) (N/((M : ℝ)^L)^k) p-
      modelArcIntegral k u v L M n (N/((M : ℝ)^L)^k) p‖≤
      (mixedMajorConstant k u v L*N^2*((M : ℝ)^L)^(u+v)/(M : ℝ))*
        (2*(N/((M : ℝ)^L)^k)) := by
  let δ := N/((M : ℝ)^L)^k
  have hMr : (0 : ℝ)<M := by exact_mod_cast (show 0<M by omega)
  have hP : 0<((M : ℝ)^L)^k := by positivity
  have hδ : 0≤δ := div_nonneg (by linarith) hP.le
  have hf : Continuous (fun β : ℝ => productIntegrand k u v L M n ((arcLabelRat p : ℝ)+β)) :=
    (continuous_productIntegrand k u v L M n).comp (continuous_const.add continuous_id)
  have hg := continuous_modelArcIntegrand k u v L M n p
  unfold narrowArcIntegral modelArcIntegral
  rw [← intervalIntegral.integral_sub (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _)]
  have hb : ∀ β∈Set.uIoc (-δ) δ,
      ‖productIntegrand k u v L M n ((arcLabelRat p : ℝ)+β)-
        modelArcIntegrand k u v L M n p β‖≤
        mixedMajorConstant k u v L*N^2*((M : ℝ)^L)^(u+v)/(M : ℝ) := by
    intro β hβ
    rw [Set.uIoc_of_le (by linarith : -δ≤δ)] at hβ
    have hab : |β|≤δ := abs_le.mpr ⟨hβ.1.le,hβ.2⟩
    have hscale : |β| *((M : ℝ)^L)^k≤N := (le_div_iff₀ hP).mp hab
    have hh := productIntegrand_narrow_error k u v L M p.1 n hk hu hv hL hM p.1.pos
      ((p.2 : ZMod (p.1 : ℕ)).val : ℤ) hN hq hscale
    simpa only [modelArcIntegrand,arcLabelRat_real,Int.cast_natCast] using hh
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const hb
  simpa only [sub_neg_eq_add,← two_mul,abs_of_nonneg (mul_nonneg (by norm_num : (0 : ℝ)≤2) hδ)] using hh

theorem sum_narrowArc_model_error (k u v L M n : ℕ) (hk : 1≤k) (hu : 1≤u)
    (hv : 1≤v) (hL : 1≤L) (hM : 1≤M) (hkuv : k≤u+v)
    (S : Finset ℕ+) {N : ℝ} (hN : 1≤N) (hQ : ∀ q∈S,(q : ℝ)≤N) :
    ‖(∑ p∈denominatorArcLabels S,narrowArcIntegral (productIntegrand k u v L M n)
        (N/((M : ℝ)^L)^k) p)-
      ∑ p∈denominatorArcLabels S,modelArcIntegral k u v L M n (N/((M : ℝ)^L)^k) p‖≤
      (2*mixedMajorConstant k u v L)*N^5/(M : ℝ)*((M : ℝ)^L)^(u+v-k) := by
  classical
  let P : ℝ := (M : ℝ)^L
  let E := (mixedMajorConstant k u v L*N^2*P^(u+v)/(M : ℝ))*(2*(N/P^k))
  have hMr : (0 : ℝ)<M := by exact_mod_cast (show 0<M by omega)
  have hP : 0<P := by dsimp [P]; positivity
  have hE : 0≤E := by
    dsimp [E]
    have := (mixedMajorConstant_pos k u v L hu).le
    positivity
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ p∈denominatorArcLabels S,‖narrowArcIntegral (productIntegrand k u v L M n)
        (N/P^k) p-modelArcIntegral k u v L M n (N/P^k) p‖ := norm_sum_le _ _
    _ ≤ ∑ _p∈denominatorArcLabels S,E := by
      apply Finset.sum_le_sum
      intro p hp
      exact narrowArc_model_error k u v L M n hk hu hv hL hM p hN
        (hQ p.1 (Finset.mem_sigma.mp hp).1)
    _ = ((denominatorArcLabels S).card : ℝ)*E := by simp
    _ ≤ N^2*E := mul_le_mul_of_nonneg_right
      (denominatorArcLabels_card_le S (by linarith) hQ) hE
    _ = _ := by
      change N^2*E=(2*mixedMajorConstant k u v L)*N^5/(M : ℝ)*P^(u+v-k)
      dsimp [E]
      rw [show P^(u+v)=P^(u+v-k)*P^k by rw [← pow_add,Nat.sub_add_cancel hkuv]]
      field_simp

#print axioms sum_narrowArc_model_error
end Waring.ProductBox
