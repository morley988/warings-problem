import WaringLimit.Envelope

/-! The larger conductor cap allowed by the tagged pointwise estimate,
and the sign of its secondary contribution to the same certified envelope. -/
noncomputable section
namespace WaringLimit

theorem larger_cap_weyl {k : Nat} {M u θ : ℝ} (hk : 10000≤k)
    (hu : 300≤u) (hm : u≤M) (hcap : M≤(9/20)*Real.sqrt k)
    (ht₀ : 0≤θ) (ht : θ≤(9/20)/Real.sqrt k) :
    2*(1/(14*M^2)) < 29/(200*M^2) ∧
    WaringEnvelope.WeylBranch k θ u (29/(200*M^2)) := by
  have hk' : (10000:ℝ)≤k := by exact_mod_cast hk
  have hk₀ : (0:ℝ)<k := by linarith
  have hm₀ : 0<M := by linarith
  have hs : 0<Real.sqrt k := Real.sqrt_pos.mpr hk₀
  have hs' : (Real.sqrt k)^2=k := Real.sq_sqrt hk₀.le
  have hMθ : M*θ≤81/400 := by
    calc
      _ ≤ ((9/20)*Real.sqrt k)*((9/20)/Real.sqrt k) :=
        mul_le_mul hcap ht ht₀ (by positivity)
      _ = 81/400 := by field_simp; ring
  have hθ : θ≤1/800 := by
    have h := mul_le_mul_of_nonneg_right (hu.trans hm) ht₀
    linarith only [h,hMθ]
  have hs100 : 100≤Real.sqrt k := by
    nlinarith only [hs',hs.le,hk']
  have hdegree : (3/2:ℝ)*M+1≤k := by
    nlinarith only [hs',hs100,hcap,
      mul_nonneg (show 0≤Real.sqrt k-1 by linarith) hs.le]
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

theorem log_cap_ratio : Real.log (1000/189) < 167/100 := by
  apply (Real.log_lt_iff_lt_exp (by norm_num : (0:ℝ)<1000/189)).mpr
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ)≤167/100) 10
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  linarith only [h]

/-- The comparison uses the *same* finite-menu price on both sides.
The terminal variable cost has canceled the terminal plateau. -/
theorem negative_cap_charge (k : ℝ) (hk : 0<k)
    (H : ℝ) (hH : H=(9/20)*Real.sqrt k) :
    (2*k/((99999/100000)*H))*(Real.log (15*k/(14*H^2))-2)
      ≤ -(73/50)*Real.sqrt k := by
  have hs := Real.sqrt_pos.mpr hk
  have hsq := Real.sq_sqrt hk.le
  have hratio : 15*k/(14*H^2)=(1000/189:ℝ) := by
    rw [hH]
    field_simp
    nlinarith only [hsq]
  have hcoef : 2*k/((99999/100000)*H)=(4000000/899991)*Real.sqrt k := by
    rw [hH]
    field_simp
    nlinarith only [hsq]
  rw [hratio,hcoef]
  have step := mul_le_mul_of_nonneg_left (le_of_lt log_cap_ratio)
      (show 0≤(4000000/899991)*Real.sqrt k by positivity)
  nlinarith only [step,hs.le]

#print axioms larger_cap_weyl
#print axioms log_cap_ratio
#print axioms negative_cap_charge
end WaringLimit
