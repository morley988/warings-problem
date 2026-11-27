import Waring.ProductBoxMajor
import Waring.EndgameCompletionSingularCoefficients

/-! # Exact scaling and residue coefficients of the mixed major model -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Waring.ProductBox
open EndgameCompletion QuadraticModulation

def singularIntegrand (k u v L : ℕ) (θ β : ℝ) : ℂ :=
  mixedKernel k u v L β*e (-β*θ)

def mixedOscillatory (k u v L : ℕ) (M n β : ℝ) : ℂ :=
  monomialIntegral k (M^L) β^u*productIntegral k L M β^v*e (-β*n)

theorem continuous_singularIntegrand (k u v L : ℕ) (θ : ℝ) :
    Continuous (singularIntegrand k u v L θ) := by
  unfold singularIntegrand
  exact (continuous_mixedKernel k u v L).mul (by unfold e; fun_prop)

theorem norm_singularIntegrand (k u v L : ℕ) (θ β : ℝ) :
    ‖singularIntegrand k u v L θ β‖=‖mixedKernel k u v L β‖ := by
  rw [singularIntegrand,norm_mul,norm_e,mul_one]

theorem integrable_singularIntegrand (k u v L : ℕ) (hk : 1≤k)
    (hgap : (k : ℝ)<(u : ℝ)+(v : ℝ)/2) (θ : ℝ) :
    Integrable (singularIntegrand k u v (L+1) θ) := by
  exact (integrable_mixedKernel k u v L hk hgap).norm.mono'
    (continuous_singularIntegrand k u v (L+1) θ).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun β => (norm_singularIntegrand k u v (L+1) θ β).le))

theorem mixedOscillatory_scale (k u v L : ℕ) {M : ℝ} (hM : 0<M) (n β : ℝ) :
    mixedOscillatory k u v L M n β=((M^L : ℝ) : ℂ)^(u+v)*
      singularIntegrand k u v L (n/(M^L)^k) (β*(M^L)^k) := by
  have he : M^(k*L)=(M^L)^k := by rw [← pow_mul,Nat.mul_comm L k]
  have hn : -(β*(M^L)^k)*(n/(M^L)^k)=-β*n := by field_simp <;> ring
  unfold mixedOscillatory singularIntegrand mixedKernel
  rw [monomialIntegral_scale,productIntegral_scale k L hM.le,he,hn,
    ← Complex.ofReal_pow,mul_pow,mul_pow,pow_add]
  ring

theorem mixedOscillatory_integral_scale (k u v L : ℕ) (hkuv : k≤u+v)
    {M : ℝ} (hM : 0<M) (n N : ℝ) :
    (∫ β in -(N/(M^L)^k)..N/(M^L)^k,mixedOscillatory k u v L M n β)=
      ((M^L : ℝ) : ℂ)^(u+v-k)*
        ∫ γ in -N..N,singularIntegrand k u v L (n/(M^L)^k) γ := by
  simp_rw [mixedOscillatory_scale k u v L hM n]
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_comp_mul_right
    (singularIntegrand k u v L (n/(M^L)^k)) (pow_ne_zero _ (pow_ne_zero _ hM.ne'))]
  have hend : -(N/(M^L)^k)*(M^L)^k=-N := by field_simp
  rw [hend,div_mul_cancel₀ _ (pow_ne_zero _ (pow_ne_zero _ hM.ne')),Complex.real_smul,
    Complex.ofReal_inv,Complex.ofReal_pow]
  have hp : (M : ℂ)≠0 := by exact_mod_cast hM.ne'
  push_cast
  have he : ((M : ℂ)^L)^(u+v)=
      ((M : ℂ)^L)^(u+v-k)*((M : ℂ)^L)^k := by
    rw [← pow_add,Nat.sub_add_cancel hkuv]
  rw [he]
  field_simp

theorem fourier_rational_split (q : ℕ) [NeZero q] (a : ℤ) (n : ℕ) (β : ℝ) :
    fourier (-(n : ℤ)) (((a : ℝ)/(q : ℝ)+β : ℝ) : AddCircle (1 : ℝ))=
      ZMod.stdAddChar (-(a : ZMod q)*(n : ZMod q))*e (-β*n) := by
  have hc := stdAddChar_monomial_nat q 1 (-a) n
  simp only [Int.cast_neg,pow_one] at hc
  rw [fourier_eq_e,hc,← e_add]
  congr 1
  push_cast
  ring

theorem mixedMajorModel_factor (k u v L M q n : ℕ) [NeZero q] (a : ℤ) (β : ℝ) :
    mixedMajorModel k u v L M a q β*fourier (-(n : ℤ))
      (((a : ℝ)/(q : ℝ)+β : ℝ) : AddCircle (1 : ℝ))=
      (ordinaryCompleteMean q k (a : ZMod q)^u*productCompleteMean q k L (a : ZMod q)^v*
        ZMod.stdAddChar (-(a : ZMod q)*(n : ZMod q)))*mixedOscillatory k u v L M n β := by
  rw [mixedMajorModel,rationalProductMean_eq_complete,completeMonomialSum_eq_mod,
    fourier_rational_split]
  simp only [ordinaryCompleteMean,productCompleteMean,mixedOscillatory,mul_pow]
  ring

theorem sum_mixedMajorModel_factor (k u v L M q n : ℕ) [NeZero q] (β : ℝ) :
    (∑ a : (ZMod q)ˣ,mixedMajorModel k u v L M ((a : ZMod q).val : ℤ) q β*
      fourier (-(n : ℤ)) ((((a : ZMod q).val : ℝ)/(q : ℝ)+β : ℝ) : AddCircle (1 : ℝ)))=
        productSingularCoefficient k u v L (n : ℤ) q*mixedOscillatory k u v L M n β := by
  have he (a : (ZMod q)ˣ) := mixedMajorModel_factor k u v L M q n ((a : ZMod q).val : ℤ) β
  simp only [Int.cast_natCast,ZMod.natCast_zmod_val] at he
  simp_rw [he]
  rw [← Finset.sum_mul,productSingularCoefficient_nezero]
  simp only [Int.cast_natCast]

#print axioms mixedOscillatory_integral_scale
#print axioms sum_mixedMajorModel_factor
end Waring.ProductBox
