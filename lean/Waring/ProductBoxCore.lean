import Waring.ProductBoxFinitePositive
import Waring.EndgameCompletionNarrowOrdinary
import Waring.EndgameCompletionProductCutoff

/-! # Positive actual narrow-major contributions on the integer product scale -/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace Waring.ProductBox
open EndgameCompletion RestrictedSmoothArcs

theorem periodic_productIntegrand (k u v L M n : ℕ) :
    Function.Periodic (productIntegrand k u v L M n) 1 := by
  intro α
  unfold productIntegrand
  rw [periodic_ordinaryWeyl,productWeyl_periodic,AddCircle.coe_add_period]

theorem product_core_model_error (k u v L M N n : ℕ) (hk : 1≤k) (hu : 1≤u)
    (hv : 1≤v) (hL : 1≤L) (hM : 1≤M) (hN : 1≤N) (hkuv : k≤u+v)
    (hsize : 2*(k : ℝ)*(N : ℝ)^2≤(M : ℝ)^L)
    (hpack : 4*(N : ℝ)^3≤((M : ℝ)^L)^k) :
    ‖(∫ α in ordinaryCore k ((M : ℝ)^L) N,productIntegrand k u v L M n α)-
        ((((M : ℝ)^L)^(u+v-k) : ℝ) : ℂ)*
          finiteMain k u v L N (n : ℤ) ((n : ℝ)/((M : ℝ)^L)^k)‖≤
      (2*mixedMajorConstant k u v L)*(N : ℝ)^5/(M : ℝ)*((M : ℝ)^L)^(u+v-k) := by
  have hMr : (0 : ℝ)<M := by exact_mod_cast (show 0<M by omega)
  have hP : 0<(M : ℝ)^L := by positivity
  let S := broadDenominators ((N-1 : ℕ) : ℝ)
  have hQ (q : ℕ+) (hq : q∈S) : (q : ℝ)≤(N : ℝ) :=
    ((mem_broadDenominators _ q).mp hq).trans (by exact_mod_cast Nat.sub_le N 1)
  have hcore : (∫ α in ordinaryCore k ((M : ℝ)^L) N,productIntegrand k u v L M n α)=
      ∑ p∈denominatorArcLabels S,narrowArcIntegral (productIntegrand k u v L M n)
        ((N : ℝ)/((M : ℝ)^L)^k) p := by
    simpa only [narrowArcIntegral,denominatorArcLabels,Finset.sum_sigma,arcLabelRat_real] using
      ordinaryCore_integral_eq_arc_sum hk hN hP hsize hpack
        (continuous_productIntegrand k u v L M n) (periodic_productIntegrand k u v L M n)
  have hmodel := modelArcIntegral_sum k u v L M n hkuv (by omega) S (N : ℝ)
  have hmodel' : (∑ p∈denominatorArcLabels S,
      modelArcIntegral k u v L M n ((N : ℝ)/((M : ℝ)^L)^k) p)=
      ((((M : ℝ)^L)^(u+v-k) : ℝ) : ℂ)*
        finiteMain k u v L N (n : ℤ) ((n : ℝ)/((M : ℝ)^L)^k) := by
    rw [hmodel]
    unfold finiteMain
    push_cast
    ring
  rw [hcore,← hmodel']
  exact sum_narrowArc_model_error k u v L M n hk hu hv hL hM hkuv S
    (by exact_mod_cast hN) hQ

theorem product_core_lower (k u v L : ℕ) (hk : 1≤k) (hu : 1≤u) (hv : 1≤v)
    (hL : 1≤L) (hkuv : k≤u+v)
    (hfinite : ∃ η C : ℝ,0<η ∧ 0<C ∧ ∀ᶠ N : ℕ in atTop,∀ n : ℤ,∀ θ∈Set.Icc 1 (1+η),
      C≤(finiteMain k u v L N n θ).re) :
    ∃ c : ℝ,0<c ∧ ∀ᶠ n : ℕ in atTop,
      c*(productScaleP k L n)^(u+v-k)≤
        productArcContribution k u v L (productScaleM k L n) n
          (ordinaryCore k (productScaleP k L n) (productScaleCutoff k L n)) := by
  obtain ⟨η,C,hη,hC,hfinite⟩ := hfinite
  have hk0 : 0<k := by omega
  have hL0 : 0<L := by omega
  have hN := productScaleCutoff_tendsto k L hk0 hL0
  have hfin := hN.eventually hfinite
  have hθ := productScaleTheta_eventually_interval k L hk0 hL0 hη
  have hgeom := productScaleCutoff_geometry k L hk0 hL0
  have he : Tendsto (fun n => (2*mixedMajorConstant k u v L)*
      ((productScaleCutoff k L n : ℝ)^5/(productScaleM k L n : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => 2*mixedMajorConstant k u v L) atTop
        (𝓝 (2*mixedMajorConstant k u v L))).mul (productScaleCutoff_error_tendsto k L hk0 hL0)
  have hevent := he.eventually_lt_const (half_pos hC)
  refine ⟨C/2,half_pos hC,?_⟩
  filter_upwards [hfin,hθ,hgeom,hevent] with n hfin hθ hgeom hevent
  let M := productScaleM k L n
  let P := productScaleP k L n
  let N := productScaleCutoff k L n
  have hMr : (0 : ℝ)<M := by exact_mod_cast (show 0<M by dsimp [M]; omega)
  have hP : 0<P := by dsimp [P,productScaleP]; positivity
  have hpow : 0≤P^(u+v-k) := (pow_pos hP _).le
  have hbound := product_core_model_error k u v L M N n hk hu hv hL hgeom.1 hgeom.2.1
    hkuv hgeom.2.2.1 hgeom.2.2.2
  have herr := (Complex.abs_re_le_norm _).trans hbound
  simp only [Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero] at herr
  have hmain := mul_le_mul_of_nonneg_left (hfin (n : ℤ) (productScaleTheta k L n) hθ.2) hpow
  have herror : (2*mixedMajorConstant k u v L)*(N : ℝ)^5/(M : ℝ)*P^(u+v-k)≤
      (C/2)*P^(u+v-k) := by
    apply mul_le_mul_of_nonneg_right _ hpow
    simpa only [mul_div_assoc] using hevent.le
  have hlow := (abs_le.mp herr).1
  change (C/2)*P^(u+v-k)≤_
  change -(2*mixedMajorConstant k u v L*(N : ℝ)^5/(M : ℝ)*P^(u+v-k))≤
    productArcContribution k u v L M n (ordinaryCore k P N)-
      P^(u+v-k)*(finiteMain k u v L N (n : ℤ) (productScaleTheta k L n)).re at hlow
  linarith

theorem degree8_product_core_lower (L : ℕ) (hL : 1≤L) :
    ∃ c : ℝ,0<c ∧ ∀ᶠ n : ℕ in atTop,
      c*(productScaleP 8 L n)^30≤productArcContribution 8 8 30 L (productScaleM 8 L n) n
        (ordinaryCore 8 (productScaleP 8 L n) (productScaleCutoff 8 L n)) := by
  obtain ⟨l,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : L≠0)
  exact product_core_lower 8 8 30 (l+1) (by omega) (by omega) (by omega) (by omega) (by omega)
    (degree8_finiteMain_uniform_positive l)

theorem degree9_product_core_lower (L : ℕ) (hL : 1≤L) :
    ∃ c : ℝ,0<c ∧ ∀ᶠ n : ℕ in atTop,
      c*(productScaleP 9 L n)^37≤productArcContribution 9 11 35 L (productScaleM 9 L n) n
        (ordinaryCore 9 (productScaleP 9 L n) (productScaleCutoff 9 L n)) := by
  obtain ⟨l,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : L≠0)
  exact product_core_lower 9 11 35 (l+1) (by omega) (by omega) (by omega) (by omega) (by omega)
    (degree9_finiteMain_uniform_positive l)

#print axioms degree8_product_core_lower
#print axioms degree9_product_core_lower
end Waring.ProductBox
