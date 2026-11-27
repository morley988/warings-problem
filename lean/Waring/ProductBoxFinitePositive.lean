import Waring.ProductBoxSeriesTail
import Waring.ProductBoxTail
import Waring.EndgameCompletionSingularPositive

/-! # A uniformly positive finite major model -/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace Waring.ProductBox
open EndgameCompletion RestrictedSmoothArcs

def finiteMain (k u v L : ℕ) (N : ℕ) (n : ℤ) (θ : ℝ) : ℂ :=
  (∑ q∈broadDenominators ((N-1 : ℕ) : ℝ),productSingularCoefficient k u v L n q)*
    ∫ β in -(N : ℝ)..(N : ℝ),singularIntegrand k u v L θ β

theorem singularIntegral_partial_norm_le (k u v L : ℕ) (hk : 1≤k)
    (hgap : (k : ℝ)<(u : ℝ)+(v : ℝ)/2) (N : ℕ) (θ : ℝ) :
    ‖∫ β in -(N : ℝ)..(N : ℝ),singularIntegrand k u v (L+1) θ β‖≤
      ∫ β : ℝ,‖mixedKernel k u v (L+1) β‖ := by
  rw [intervalIntegral.integral_of_le (by have := Nat.cast_nonneg (α := ℝ) N; linarith)]
  apply (norm_integral_le_integral_norm _).trans
  simp_rw [norm_singularIntegrand]
  exact integral_mono_measure Measure.restrict_le_self
    (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
    (integrable_mixedKernel k u v L hk hgap).norm

theorem positive_product_perturbation {S J s j : ℂ} {c d B D ε : ℝ}
    (hc : 0≤c) (hd : 0≤d) (hS : c≤S.re) (hJ : d≤J.re) (hSreal : S.im=0)
    (hB : ‖S‖≤B) (hD : ‖j‖≤D) (he0 : 0≤ε)
    (hs : ‖s-S‖≤ε) (hj : ‖j-J‖≤ε) :
    c*d-ε*(B+D)≤(s*j).re := by
  have herr : ‖s*j-S*J‖≤ε*(B+D) := by
    rw [show s*j-S*J=(s-S)*j+S*(j-J) by ring]
    apply (norm_add_le _ _).trans
    rw [norm_mul,norm_mul]
    calc
      _ ≤ ε*D+B*ε := add_le_add
        (mul_le_mul hs hD (norm_nonneg _) he0)
        (mul_le_mul hB hj (norm_nonneg _) ((norm_nonneg _).trans hB))
      _ = _ := by ring
  have hmain : c*d≤(S*J).re := by
    rw [Complex.mul_re,hSreal,zero_mul,sub_zero]
    exact mul_le_mul hS hJ hd (hc.trans hS)
  have hab := (Complex.abs_re_le_norm (s*j-S*J)).trans herr
  rw [Complex.sub_re] at hab
  have hlow := (abs_le.mp hab).1
  linarith

theorem finiteMain_uniform_positive (k u v L : ℕ) (hk : 1≤k)
    (hgap : (k : ℝ)<(u : ℝ)+(v : ℝ)/2) {b : ℕ → ℝ} (hb : Summable b)
    (hcoef : ∀ n : ℤ,∀ q : ℕ,‖productSingularCoefficient k u v (L+1) n q‖≤b q)
    (hseries : ∃ c : ℝ,0<c ∧ ∀ n : ℤ,c≤(productSingularSeries k u v (L+1) n).re)
    (hintegral : ∃ η d : ℝ,0<η ∧ 0<d ∧ ∀ θ∈Set.Icc 1 (1+η),
      d≤(∫ β : ℝ,singularIntegrand k u v (L+1) θ β).re) :
    ∃ η C : ℝ,0<η ∧ 0<C ∧ ∀ᶠ N : ℕ in atTop,∀ n : ℤ,∀ θ∈Set.Icc 1 (1+η),
      C≤(finiteMain k u v (L+1) N n θ).re := by
  obtain ⟨c,hc,hseries⟩ := hseries
  obtain ⟨η,d,hη,hd,hintegral⟩ := hintegral
  let B : ℝ := |∑' q : ℕ,b q|+1
  let D : ℝ := (∫ β : ℝ,‖mixedKernel k u v (L+1) β‖)+1
  have hB : 0<B := by dsimp [B]; positivity
  have hD : 0<D := by
    have hi : 0≤∫ β : ℝ,‖mixedKernel k u v (L+1) β‖ := integral_nonneg (fun _ => norm_nonneg _)
    dsimp [D]
    linarith
  let ε := c*d/(2*(B+D))
  have hε : 0<ε := by dsimp [ε]; positivity
  have harith := uniform_singular_series_truncation hb hcoef hε
  have hreal := singularIntegral_uniform_truncation k u v L hk hgap hε
  refine ⟨η,c*d/2,hη,by positivity,?_⟩
  filter_upwards [harith,hreal] with N harN hreN n θ hθ
  have hsumm : Summable (fun q => ‖productSingularCoefficient k u v (L+1) n q‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (hcoef n) hb
  have hnormS : ‖productSingularSeries k u v (L+1) n‖≤B := by
    apply ((norm_tsum_le_tsum_norm hsumm).trans (tsum_le_tsum (hcoef n) hsumm hb)).trans
    dsimp [B]
    linarith [le_abs_self (∑' q : ℕ,b q)]
  have hnormJ : ‖∫ β in -(N : ℝ)..(N : ℝ),singularIntegrand k u v (L+1) θ β‖≤D :=
    (singularIntegral_partial_norm_le k u v L hk hgap N θ).trans (by dsimp [D]; linarith)
  have hsclose : ‖(∑ q∈broadDenominators ((N-1 : ℕ) : ℝ),
      productSingularCoefficient k u v (L+1) n q)-productSingularSeries k u v (L+1) n‖≤ε := by
    rw [norm_sub_rev]
    exact (harN n).le
  have hjclose : ‖(∫ β in -(N : ℝ)..(N : ℝ),singularIntegrand k u v (L+1) θ β)-
      (∫ β : ℝ,singularIntegrand k u v (L+1) θ β)‖≤ε := by
    rw [norm_sub_rev]
    exact (hreN θ).le
  have hp := positive_product_perturbation hc.le hd.le (hseries n) (hintegral θ hθ)
    (productSingularSeries_im_eq_zero k u v L n hsumm) hnormS hnormJ hε.le hsclose hjclose
  have he : c*d-ε*(B+D)=c*d/2 := by
    dsimp [ε]
    field_simp
    ring
  rw [he] at hp
  exact hp

theorem degree8_finiteMain_uniform_positive (L : ℕ) :
    ∃ η C : ℝ,0<η ∧ 0<C ∧ ∀ᶠ N : ℕ in atTop,∀ n : ℤ,∀ θ∈Set.Icc 1 (1+η),
      C≤(finiteMain 8 8 30 (L+1) N n θ).re := by
  obtain ⟨B,_,hb⟩ := degree8_productSingularCoefficient_bound L
  exact finiteMain_uniform_positive 8 8 30 L (by norm_num) (by norm_num)
    ((Real.summable_nat_rpow.mpr (by norm_num : (-2 : ℝ)< -1)).mul_left B) hb
    (degree8_productSingularSeries_uniform_positive L) (degree8_singular_integral_positive L)

theorem degree9_finiteMain_uniform_positive (L : ℕ) :
    ∃ η C : ℝ,0<η ∧ 0<C ∧ ∀ᶠ N : ℕ in atTop,∀ n : ℤ,∀ θ∈Set.Icc 1 (1+η),
      C≤(finiteMain 9 11 35 (L+1) N n θ).re := by
  obtain ⟨B,_,hb⟩ := degree9_productSingularCoefficient_bound L
  exact finiteMain_uniform_positive 9 11 35 L (by norm_num) (by norm_num)
    ((Real.summable_nat_rpow.mpr (by norm_num : (-2 : ℝ)< -1)).mul_left B) hb
    (degree9_productSingularSeries_uniform_positive L) (degree9_singular_integral_positive L)

#print axioms degree8_finiteMain_uniform_positive
#print axioms degree9_finiteMain_uniform_positive
end Waring.ProductBox
