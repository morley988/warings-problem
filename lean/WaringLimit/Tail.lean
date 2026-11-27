import WaringLimit.Stability
import WaringLimit.Final

/-! Conductor coverage on the continuous, unbounded-modulus portion
of the limiting envelope. This uses the actual finite-degree radical
range M/k and the exact cap sqrt(k)/8. -/
noncomputable section
namespace WaringLimit

/-- Uniform strict margin 29/200 > 1/7 on the tail. -/
theorem tail_weyl {k : Nat} {M u θ : ℝ} (hk : 10000≤k) (hu : 300≤u)
    (hm : u≤M) (hcap : M≤Real.sqrt k/8) (ht₀ : 0≤θ) (ht : θ≤M/k) :
    2*(1/(14*M^2)) < 29/(200*M^2) ∧
    WaringEnvelope.WeylBranch k θ u (29/(200*M^2)) := by
  have hk' : (10000:ℝ)≤k := by exact_mod_cast hk
  have hk₀ : (0:ℝ)<k := by linarith
  have hm₀ : 0<M := by linarith
  have hs : 0≤Real.sqrt k := Real.sqrt_nonneg _
  have hs' : (Real.sqrt k)^2=k := Real.sq_sqrt hk₀.le
  have h1 : 8*M≤Real.sqrt k := by linarith
  have hsq : 64*M^2≤k := by
    nlinarith only [hs',sq_le_sq₀ (show 0≤8*M by positivity) hs |>.2 h1]
  have hMθ : M*θ≤1/64 := by
    have h := mul_le_mul_of_nonneg_left ht hm₀.le
    calc
      _ ≤ M*(M/k) := h
      _ ≤ 1/64 := by field_simp; linarith only [hsq]
  have hθ : θ≤1/800 := by
    have h := mul_le_mul_of_nonneg_right (hu.trans hm) ht₀
    linarith only [h,hMθ]
  have hdegree : (3/2:ℝ)*M+1≤k := by nlinarith only [hsq,(hu.trans hm)]
  have hdiv : 2*(1/(14*M^2)) < 29/(200*M^2) := by field_simp; norm_num
  refine ⟨hdiv,?_⟩
  apply WaringEnvelope.continuous_weyl_tail k θ u (29/(200*M^2)) 300 (3/2) M
    (by norm_num) (by norm_num) ht₀ (by positivity) hu hm hdegree
  · have h := mul_le_mul_of_nonneg_left hMθ (by norm_num : (0:ℝ)≤3/2+1/300)
    field_simp
    nlinarith only [h]
  · field_simp
    nlinarith only [hθ]
  · have h := mul_le_mul_of_nonneg_left hMθ (by norm_num : (0:ℝ)≤3/2+1/300)
    field_simp
    nlinarith only [h]

#print axioms tail_weyl
end WaringLimit
