import WaringLimit.RealBudget
import WaringLimit.Tail
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! A uniform conductor-cover theorem joins the certified finite path
to its continuous tail at modulus F. The integrations below use
Lebesgue measure and the real logarithm. -/
noncomputable section
namespace WaringLimit
open WaringDualEnvelope
open MeasureTheory Set Real
set_option maxRecDepth 8192

private theorem Tpos : 0<T := by decide
private theorem Bpos : 0<B := by decide
private theorem Fval : F=300 := rfl
attribute [local irreducible] F B T words

def Branch (k : Nat) (θ u s : ℝ) : Prop :=
  (∃ w : List Bool, SafeAt k (0,1) (1,0) w.reverse ∧
    s≤1-lambda (pairOfWord w)-kappa (pairOfWord w)*(u-1)
       -(1+radical (pairOfWord w))*θ) ∨
  WaringEnvelope.WeylBranch k θ u s

private theorem step_endpoint {s t : State} {c : Nat} (h : step s c=some t) :
    endpoint s.z c=some t.m := by
  cases he : endpoint s.z c with
  | none => simp [step,he] at h
  | some m =>
    simp only [step,he,bind,Option.bind,pure] at h
    split at h
    · contradiction
    · injection h with ht
      subst t
      rfl

/-- Each edge of this path carries a saving at all real conductors,
and its real price is the actual logarithmic price for that edge. -/
inductive EffectivePath (k : Nat) (θ : ℝ) : State → State → ℝ → Prop
  | refl : EffectivePath k θ s s 0
  | snoc : EffectivePath k θ s t x → step t c=some v →
      (∀ u : ℝ, 1≤u → u≤(v.m:ℝ)/B →
        ∃ saving, 2*(t.z:ℝ)/T<saving ∧ Branch k θ u saving) →
      EffectivePath k θ s v (x+charge t v)

private theorem effective {k : Nat} (hk : 2*F+1≤k) {θ : ℝ}
    (h₀ : 0≤θ) (hθ : θ≤1/(2000*T))
    {s t : State} {x : ℝ} (p : RealPath s t x) : EffectivePath k θ s t x := by
  induction p with
  | refl => exact .refl
  | snoc _ h ih =>
    exact .snoc ih h (fun u hu hm => endpoint_stable (step_endpoint h) hk h₀ hθ hu hm)

/-- A single path, with its actual real logarithmic charge, covers the
entire finite menu at every sufficiently large finite degree. -/
theorem effective_budget {k : Nat} (hk : 2*F+1≤k) {θ : ℝ}
    (h₀ : 0≤θ) (hθ : θ≤1/(2000*T)) :
    ∃ s x, EffectivePath k θ start s x ∧
      totalCharge s x ≤ (34360293397827451:ℝ)/5000000000000000 := by
  obtain ⟨s,x,p,h⟩ := limiting_real_budget
  exact ⟨s,x,effective hk h₀ hθ p,h⟩

/-- Beyond the terminal modulus the finite menu covers small real
conductors while the continuous Weyl tail covers the remaining ones.
The radical parameter is the same in both branches. -/
theorem joined_tail {k : Nat} {M u θ : ℝ} (hk : 10000≤k)
    (hθ₀ : 0≤θ) (hθ : θ≤1/(2000*T)) (hθM : θ≤M/k)
    (hF : F≤M) (hcap : M≤Real.sqrt k/8) (hu : 1≤u) (hm : u≤M) :
    ∃ s : ℝ, 2*(1/(14*M^2))<s ∧ Branch k θ u s := by
  by_cases h : u≤F
  · obtain ⟨_,v,_,c,hc⟩ := limiting_certificate
    simp only [certifiedEnd,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at hc
    have he := hc.1.1.1.1.1.1.1
    have hz : T≤v.z*14*F^2 := hc.1.1.1.1.1.2
    have hB : (0:ℝ)<B := by exact_mod_cast Bpos
    have hT : (0:ℝ)<T := by exact_mod_cast Tpos
    have hfp : (0:ℝ)<F := by rw [Fval]; norm_num
    have hmp := hfp.trans_le hF
    have hp : u≤(↑(F*B:Nat):ℝ)/B := by
      rw [Nat.cast_mul,mul_div_cancel_right₀ _ hB.ne']; exact h
    have hk' : 2*F+1≤k := le_trans (by decide +kernel) hk
    obtain ⟨s,hs,hbr⟩ := endpoint_stable he hk' hθ₀ hθ hu hp
    have hv : (T:ℝ)≤(v.z:ℝ)*14*(F:ℝ)^2 := by exact_mod_cast hz
    have hfs : (F:ℝ)^2≤M^2 := (sq_le_sq₀ hfp.le hmp.le).mpr hF
    have hval : 1/(14*M^2)≤(v.z:ℝ)/T := by
      apply (div_le_div_iff₀ (by positivity) hT).mpr
      calc
        _ ≤ (v.z:ℝ)*14*(F:ℝ)^2 := by linarith only [hv]
        _ ≤ (v.z:ℝ)*14*M^2 := mul_le_mul_of_nonneg_left hfs (by positivity)
        _ = _ := by ring
    refine ⟨s,?_,hbr⟩
    calc
      _ ≤ 2*((v.z:ℝ)/T) := mul_le_mul_of_nonneg_left hval (by norm_num)
      _ = 2*v.z/T := by ring
      _ < _ := hs
  · obtain ⟨hs,hw⟩ := tail_weyl hk (by simp only [Fval,Nat.cast_ofNat] at h; exact (lt_of_not_ge h).le) hm hcap hθ₀ hθM
    exact ⟨_,hs,Or.inr hw⟩

/-- The tail term in the real budget is the integral of the density
4/(λ M²) over all larger conductors, for λ=retentionNum/retentionDen. -/
theorem tail_integral :
    (∫ x in Ioi (F:ℝ), (4*(retentionDen:ℝ)/retentionNum)*(x^2)⁻¹) =
      (4*(retentionDen:ℝ))/(F*retentionNum:Nat) := by
  have hF : (0:ℝ)<F := by rw [Fval]; norm_num
  have hp := integral_Ioi_rpow_of_lt (by norm_num : (-2:ℝ)< -1) hF
  have he (x : ℝ) : x∈Ioi (F:ℝ) → x^(-2:ℝ)=(x^2)⁻¹ := by
    intro hx
    rw [Real.rpow_neg (le_of_lt (hF.trans hx))]
    norm_num
  rw [integral_const_mul]
  have he' : (∫ x in Ioi (F:ℝ), (x^2)⁻¹)=(∫ x in Ioi (F:ℝ), x^(-2:ℝ)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    exact fun x h => (he x h).symm
  rw [he',hp]
  rw [show (-2:ℝ)+1 = -1 by norm_num]
  rw [Real.rpow_neg_one]
  push_cast
  ring

#print axioms effective_budget
#print axioms joined_tail
#print axioms tail_integral
end WaringLimit
