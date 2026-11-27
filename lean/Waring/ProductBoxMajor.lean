import Waring.ProductBoxPositive
import Waring.EndgameCompletionProductGrid
import Waring.EndgameCompletionProductRepresentation

/-! # Uniform replacement of the actual mixed product on narrow arcs -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Waring.ProductBox
open EndgameCompletion QuadraticModulation

def mixedMajorModel (k u v L M : ℕ) (a : ℤ) (q : ℕ) (β : ℝ) : ℂ :=
  ((completeMonomialSum k a q/(q : ℂ))*monomialIntegral k ((M : ℝ)^L) β)^u*
    (rationalProductMean k L a q*productIntegral k L M β)^v

def mixedMajorConstant (k u v L : ℕ) : ℝ :=
  3*((u : ℝ)+(v : ℝ)*L)*(1+2*Real.pi*(k : ℝ))

theorem mixedMajorConstant_pos (k u v L : ℕ) (hu : 1≤u) : 0<mixedMajorConstant k u v L := by
  have hu' : (0 : ℝ)<u := by exact_mod_cast (show 0<u by omega)
  unfold mixedMajorConstant
  positivity

theorem norm_productMajorModel_le (k L : ℕ) (a : ℤ) {q M : ℕ} (hq : 0<q) (β : ℝ) :
    ‖rationalProductMean k L a q*productIntegral k L M β‖≤(M : ℝ)^L := by
  rw [norm_mul]
  exact (mul_le_mul (norm_rationalProductMean_le k L a hq)
    (norm_productIntegral_le k L (Nat.cast_nonneg M) β) (norm_nonneg _)
    zero_le_one).trans_eq (one_mul _)

theorem norm_mixed_product_sub_le {f g F G : ℂ} {P : ℝ} (hP : 0≤P)
    (hf : ‖f‖≤P) (hg : ‖g‖≤P) (hF : ‖F‖≤P) (hG : ‖G‖≤P)
    {u v : ℕ} (hu : 1≤u) (hv : 1≤v) :
    ‖f^u*g^v-F^u*G^v‖≤(u : ℝ)*P^(u+v-1)*‖f-F‖+
      (v : ℝ)*P^(u+v-1)*‖g-G‖ := by
  have he : f^u*g^v-F^u*G^v=(f^u-F^u)*g^v+F^u*(g^v-G^v) := by ring
  rw [he]
  apply (norm_add_le _ _).trans
  rw [norm_mul,norm_mul,norm_pow,norm_pow]
  apply add_le_add
  · calc
      _ ≤ ((u : ℝ)*P^(u-1)*‖f-F‖)*P^v :=
        mul_le_mul (norm_pow_sub_pow_le hP hf hF u)
          (pow_le_pow_left₀ (norm_nonneg _) hg v) (by positivity) (by positivity)
      _ = _ := by rw [show u+v-1=(u-1)+v by omega,pow_add]; ring
  · calc
      _ ≤ P^u*((v : ℝ)*P^(v-1)*‖g-G‖) :=
        mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hF u)
          (norm_pow_sub_pow_le hP hg hG v) (by positivity) (by positivity)
      _ = _ := by rw [show u+v-1=u+(v-1) by omega,pow_add]; ring

theorem product_narrow_major_approximation (k L M q : ℕ) (hk : 1≤k)
    (hM : 0<M) (hq : 0<q) (a : ℤ) {W β : ℝ} (hW : 1≤W)
    (hqW : (q : ℝ)≤W) (hβ : |β| *((M : ℝ)^L)^k≤W) :
    ‖productWeyl k L M ((a : ℝ)/(q : ℝ)+β)-rationalProductMean k L a q*productIntegral k L M β‖≤
      3*(L : ℝ)*(1+2*Real.pi*(k : ℝ))*W^2*(M : ℝ)^L/(M : ℝ) := by
  have hMr : (0 : ℝ)<M := by exact_mod_cast hM
  have hβ' : |β| *(M : ℝ)^(k*L)≤W := by
    simpa only [← pow_mul,Nat.mul_comm L k] using hβ
  have hfac : 0≤2*Real.pi*(k : ℝ) := by positivity
  have hh : 1+2*Real.pi*(k : ℝ)*|β| *(M : ℝ)^(k*L)≤
      (1+2*Real.pi*(k : ℝ))*W := by
    nlinarith [mul_le_mul_of_nonneg_left hβ' hfac]
  calc
    _ ≤ 3*(L : ℝ)*q*(1+2*Real.pi*(k : ℝ)*|β| *(M : ℝ)^(k*L))*(M : ℝ)^L/(M : ℝ) :=
      product_rational_approximation k L M q hk hM hq a β
    _ ≤ 3*(L : ℝ)*W*((1+2*Real.pi*(k : ℝ))*W)*(M : ℝ)^L/(M : ℝ) := by
      apply div_le_div_of_nonneg_right _ hMr.le
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul (mul_le_mul_of_nonneg_left hqW (by positivity)) hh
        (by positivity) (by positivity)
    _ = _ := by ring

theorem mixed_narrow_major_approximation (k u v L M q : ℕ) (hk : 1≤k)
    (hu : 1≤u) (hv : 1≤v) (hL : 1≤L) (hM : 1≤M) (hq : 0<q) (a : ℤ)
    {W β : ℝ} (hW : 1≤W) (hqW : (q : ℝ)≤W)
    (hβ : |β| *((M : ℝ)^L)^k≤W) :
    ‖ordinaryWeyl k ((M : ℝ)^L) ((a : ℝ)/(q : ℝ)+β)^u*
        productWeyl k L M ((a : ℝ)/(q : ℝ)+β)^v-mixedMajorModel k u v L M a q β‖≤
      mixedMajorConstant k u v L*W^2*((M : ℝ)^L)^(u+v)/(M : ℝ) := by
  let P : ℝ := (M : ℝ)^L
  have hMr : (0 : ℝ)<M := by exact_mod_cast (show 0<M by omega)
  have hM1 : (1 : ℝ)≤M := by exact_mod_cast hM
  have hP : 0≤P := by dsimp [P]; positivity
  have hMP : (M : ℝ)≤P := by
    simpa only [pow_one] using (pow_le_pow_right₀ hM1 hL)
  have hordinary := ordinary_narrow_major_approximation k hk a hq hP hW hqW hβ
  have hordinary' : ‖ordinaryWeyl k P ((a : ℝ)/(q : ℝ)+β)-
      (completeMonomialSum k a q/(q : ℂ))*monomialIntegral k P β‖≤
      (3*(1+2*Real.pi*(k : ℝ))*W^2)*P/(M : ℝ) := by
    apply hordinary.trans
    apply (le_div_iff₀ hMr).mpr
    exact mul_le_mul_of_nonneg_left hMP (by positivity)
  have hproduct := product_narrow_major_approximation k L M q hk (by omega) hq a hW hqW hβ
  have hh := norm_mixed_product_sub_le hP
    (norm_ordinaryWeyl_le k ((a : ℝ)/(q : ℝ)+β) hP) (norm_productWeyl_le k L M ((a : ℝ)/(q : ℝ)+β))
    (norm_ordinaryMajorModel_le k a hq hP β) (norm_productMajorModel_le k L a hq β) hu hv
  apply hh.trans
  calc
    _ ≤ (u : ℝ)*P^(u+v-1)*((3*(1+2*Real.pi*(k : ℝ))*W^2)*P/(M : ℝ))+
        (v : ℝ)*P^(u+v-1)*(3*(L : ℝ)*(1+2*Real.pi*(k : ℝ))*W^2*P/(M : ℝ)) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hordinary' (by positivity))
        (mul_le_mul_of_nonneg_left hproduct (by positivity))
    _ = _ := by
      change _=mixedMajorConstant k u v L*W^2*P^(u+v)/(M : ℝ)
      rw [show P^(u+v)=P^(u+v-1)*P by
        rw [← pow_succ]; congr 1; omega]
      unfold mixedMajorConstant
      ring

theorem productIntegrand_narrow_error (k u v L M q n : ℕ) (hk : 1≤k)
    (hu : 1≤u) (hv : 1≤v) (hL : 1≤L) (hM : 1≤M) (hq : 0<q) (a : ℤ)
    {W β : ℝ} (hW : 1≤W) (hqW : (q : ℝ)≤W)
    (hβ : |β| *((M : ℝ)^L)^k≤W) :
    ‖productIntegrand k u v L M n ((a : ℝ)/(q : ℝ)+β)-
      mixedMajorModel k u v L M a q β*fourier (-(n : ℤ))
        (((a : ℝ)/(q : ℝ)+β : ℝ) : AddCircle (1 : ℝ))‖≤
      mixedMajorConstant k u v L*W^2*((M : ℝ)^L)^(u+v)/(M : ℝ) := by
  rw [productIntegrand,← sub_mul,norm_mul,
    show ‖fourier (-(n : ℤ)) (((a : ℝ)/(q : ℝ)+β : ℝ) : AddCircle (1 : ℝ))‖=1 from Circle.norm_coe _,mul_one]
  exact mixed_narrow_major_approximation k u v L M q hk hu hv hL hM hq a hW hqW hβ

#print axioms mixed_narrow_major_approximation
#print axioms productIntegrand_narrow_error
end Waring.ProductBox
