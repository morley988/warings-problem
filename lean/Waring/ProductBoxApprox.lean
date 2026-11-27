import Waring.ProductBoxPhase
import Waring.EndgameCompletionProductWeights

/-! # The actual product-weight narrow-major approximation -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Waring.ProductBox
open EndgameCompletion SmoothMoments ProductMultiplicity QuadraticModulation

def productIntegral (k L : ℕ) (M β : ℝ) : ℂ := boxIntegral L M (productPhase k L β)

def rationalProductMean (k L : ℕ) (a : ℤ) (q : ℕ) : ℂ :=
  gridMean L q (fun x : Fin L → ℕ => productPhase k L ((a : ℝ)/q) (fun i => x i))

theorem norm_productIntegral_le (k L : ℕ) {M : ℝ} (hM : 0≤M) (β : ℝ) :
    ‖productIntegral k L M β‖≤M^L := by
  simpa only [one_mul] using boxIntegral_norm_le L hM zero_le_one
    (fun x _ => (norm_e _).le : ∀ x,(∀ i,x i ∈ Set.Icc 0 M) → ‖productPhase k L β x‖≤1)

theorem norm_rationalProductMean_le (k L : ℕ) (a : ℤ) {q : ℕ} (hq : 0<q) :
    ‖rationalProductMean k L a q‖≤1 :=
  gridMean_norm_le_one L q hq (fun _ => (norm_e _).le)

theorem continuous_productIntegral (k L : ℕ) (M : ℝ) : Continuous (productIntegral k L M) := by
  apply continuous_boxIntegral
  unfold productPhase e
  fun_prop

theorem productWeyl_rational_grid (k L M : ℕ) (a : ℤ) (q : ℕ) (β : ℝ) :
    productWeyl k L M ((a : ℝ)/q+β)=
      gridSum L M (fun x => productPhase k L β (fun i => (x i : ℝ))*
        productPhase k L ((a : ℝ)/q) (fun i => (x i : ℝ))) := by
  rw [gridSum_eq_finiteTuples]
  unfold productWeyl productBox
  apply Finset.sum_congr rfl
  intro x _
  rw [phase_eq_e]
  unfold productPhase tupleProduct
  push_cast
  rw [add_mul,e_add,mul_comm]

theorem product_rational_approximation (k L M q : ℕ) (hk : 1≤k)
    (hM : 0<M) (hq : 0<q) (a : ℤ) (β : ℝ) :
    ‖productWeyl k L M ((a : ℝ)/q+β)-rationalProductMean k L a q*productIntegral k L M β‖≤
      3*(L : ℝ)*q*(1+2*Real.pi*(k : ℝ)*|β| *(M : ℝ)^(k*L))*(M : ℝ)^L/(M : ℝ) := by
  have hMr : (0 : ℝ)<M := by exact_mod_cast hM
  have hh := product_box_quadrature L M q hM hq zero_le_one
    (show 0≤2*Real.pi*(k : ℝ)*(|β| *(M : ℝ)^(k*L))/(M : ℝ) by positivity)
    (fun x : Fin L → ℕ => productPhase k L ((a : ℝ)/q) (fun i => x i))
    (fun _ => (norm_e _).le) (rational_product_periodic k L a hq)
    (productPhase k L β) (continuous_productPhase k L β)
    (productPhase_regular k L hk hMr le_rfl)
  rw [← productWeyl_rational_grid] at hh
  convert hh using 1
  congr 3
  field_simp

#print axioms product_rational_approximation
end Waring.ProductBox
