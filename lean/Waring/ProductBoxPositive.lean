import Waring.ProductBoxRectangle

/-! # Uniform positivity of the actual mixed singular integral near one -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Waring.ProductBox
open EndgameCompletion QuadraticModulation

theorem power_le_self_unit {k : ℕ} (hk : 1≤k) {b : ℝ} (hb0 : 0≤b) (hb1 : b≤1) :
    b^k≤b := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k≠0)
  rw [pow_succ]
  simpa using mul_le_mul_of_nonneg_right (pow_le_one₀ hb0 hb1) hb0

theorem mixed_singular_integral_positive (k u v L : ℕ) (hk : 1≤k) (hu : 1≤u)
    (hgap : (k : ℝ)<(u+1 : ℕ)+(v : ℝ)/2) :
    ∃ η C : ℝ,0<η ∧ 0<C ∧ ∀ θ∈Set.Icc 1 (1+η),
      C≤(∫ β : ℝ,mixedKernel k (u+1) v (L+1) β*e (-β*θ)).re := by
  let b : ℝ := 1/(2*((u : ℝ)+v+1))
  let a : ℝ := b/2
  have hn : 0≤(u : ℝ)+(v : ℝ) := by positivity
  have hd : 0<2*((u : ℝ)+v+1) := by linarith
  have hb0 : 0<b := one_div_pos.mpr hd
  have hb1 : b≤1 := by
    dsimp [b]
    apply (div_le_iff₀ hd).mpr
    linarith
  have ha0 : 0<a := by dsimp [a]; positivity
  have hab : a<b := by dsimp [a]; linarith
  have ha1 : a≤1 := hab.le.trans hb1
  have hak0 : 0<a^k := pow_pos ha0 _
  have hak1 : a^k≤1 := pow_le_one₀ ha0.le ha1
  have hsum : ((u : ℝ)+v)*b^k≤1/2 := by
    calc
      _ ≤ ((u : ℝ)+v)*b := mul_le_mul_of_nonneg_left (power_le_self_unit hk hb0.le hb1) hn
      _ ≤ 1/2 := by
        dsimp [b]
        rw [mul_one_div]
        apply (div_le_iff₀ hd).mpr
        linarith
  let B := mixedRectangle u v (L+1) a b
  let C := monomialGaussianConstant k*(mixedMeasure u v (L+1)).real B
  have hC : 0<C := mul_pos (monomialGaussianConstant_pos (by omega))
    (mixedRectangle_measure_pos u v (L+1) ha0.le hab hb1)
  refine ⟨a^k/2,C,by positivity,hC,?_⟩
  intro θ hθ
  have hwindow (z : MixedSpace u v (L+1)) (hz : z∈B) :
      θ-mixedValue k u v (L+1) z∈Set.Icc 0 (1-a^k/2) := by
    have hv := mixedValue_rectangle_bounds k u v L hu ha0.le hb1 hz
    constructor <;> linarith [hθ.1,hθ.2]
  have hl := centeredAverage_integral_lower (mixedMeasure u v (L+1))
    (mixedValue k u v (L+1)) (continuous_mixedValue k u v (L+1))
    (by omega : 0<k) (by linarith : 0≤1-a^k/2) (by linarith : 1-a^k/2<1)
    B (measurableSet_mixedRectangle u v (L+1) a b) hwindow
    (integrable_centered_extended hk hgap θ)
  simpa only [centered_extended_characteristic] using hl

theorem degree8_singular_integral_positive (L : ℕ) :
    ∃ η C : ℝ,0<η ∧ 0<C ∧ ∀ θ∈Set.Icc 1 (1+η),
      C≤(∫ β : ℝ,mixedKernel 8 8 30 (L+1) β*e (-β*θ)).re :=
  mixed_singular_integral_positive 8 7 30 L (by omega) (by omega) (by norm_num)

theorem degree9_singular_integral_positive (L : ℕ) :
    ∃ η C : ℝ,0<η ∧ 0<C ∧ ∀ θ∈Set.Icc 1 (1+η),
      C≤(∫ β : ℝ,mixedKernel 9 11 35 (L+1) β*e (-β*θ)).re :=
  mixed_singular_integral_positive 9 10 35 L (by omega) (by omega) (by norm_num)

#print axioms degree8_singular_integral_positive
#print axioms degree9_singular_integral_positive
end Waring.ProductBox
