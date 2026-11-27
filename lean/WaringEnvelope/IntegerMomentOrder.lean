import WaringEnvelope.DiscreteDescent
import Mathlib.Algebra.Order.Floor.Semiring

/-! # Even integer moment orders and the variable-count allowance -/
noncomputable section
namespace WaringEnvelope
open MeasureTheory Set

def evenOrder (x : ℝ) : ℕ := 2*⌈x/2⌉₊

theorem evenOrder_bounds (x : ℝ) (hx : 0≤x) : x≤(evenOrder x:ℝ) ∧ (evenOrder x:ℝ)<x+2 := by
  have hl := Nat.le_ceil (x/2)
  have hu := Nat.ceil_lt_add_one (show 0≤x/2 by positivity)
  unfold evenOrder
  push_cast
  constructor <;> linarith

def defectSequence (V : ℝ → ℝ) (D rate : ℝ) : ℕ → ℝ
  | 0 => D
  | n+1 => max 0 (defectSequence V D rate n-rate*V (defectSequence V D rate n))

/-- The price includes at most two variables for each of the initial rounding,
the last defect step, and the rounding of the number of ordinary factors.
P is the degree-specific statement asserting the normalized moment defect. -/
theorem even_moment_order_of_integral (P : ℕ → ℝ → Prop) (k : ℕ) (hk : 0<k) (V : ℝ → ℝ)
    (D target seed fee : ℝ) (ht : 0≤target) (hD : target≤D) (hseed : 0≤seed) (hfee : 0≤fee)
    (hV : ContinuousOn V (Icc target D)) (hpos : ∀ x∈Icc target D, 0<V x)
    (hmono : MonotoneOn V (Icc target D)) (hinit : P (evenOrder (k*seed)) D)
    (hstep : ∀ r x, P r x → 0≤x → P (r+2) (max 0 (x-(2/k)*V x))) :
    ∃ r a : ℕ, ∃ x : ℝ, Even r ∧ Even a ∧ P r x ∧ 0≤x ∧ x≤target ∧ k*fee≤(a:ℝ) ∧
      ((r+a:ℕ):ℝ)/k < seed+fee+(∫ t in target..D, 1/V t)+6/k := by
  let e := defectSequence V D (2/k)
  let init := evenOrder (k*seed)
  let a := evenOrder (k*fee)
  have hk' : (0:ℝ)<k := by exact_mod_cast hk
  have he (n : ℕ) : 0≤e n := by
    cases n with
    | zero => exact ht.trans hD
    | succ n => exact le_max_left _ _
  have admiss (n : ℕ) : P (init+2*n) (e n) := by
    induction n with
    | zero => simpa [init,e,defectSequence] using hinit
    | succ n ih =>
      have h := hstep (init+2*n) (e n) ih (he n)
      exact (show init+2*n+2=init+2*(n+1) by omega) ▸ h
  obtain ⟨n,hn,hprice⟩ := finite_defect_descent V e D target (2/k) (by positivity)
    ht hD le_rfl hV hpos hmono (fun _ _ => le_rfl)
  have ha := evenOrder_bounds ((k:ℝ)*fee) (mul_nonneg hk'.le hfee)
  have hi := evenOrder_bounds ((k:ℝ)*seed) (mul_nonneg hk'.le hseed)
  refine ⟨init+2*n,a,e n,⟨⌈(k:ℝ)*seed/2⌉₊+n,by dsimp [init,evenOrder];omega⟩,
    ⟨⌈(k:ℝ)*fee/2⌉₊,by dsimp [a,evenOrder];omega⟩,admiss n,he n,hn,ha.1,?_⟩
  apply (div_lt_iff₀ hk').2
  have h₂ : (2:ℝ)*(n:ℝ)≤2+k*(∫ t in target..D, 1/V t) := by
    rw [div_div_eq_mul_div] at hprice
    linarith
  dsimp only [a,init]
  push_cast
  rw [add_mul,div_mul_cancel₀ _ hk'.ne']
  linarith [hi.2,ha.2]

/-- The slightly larger safety constant in the target makes the final
comparison strict even when the integer fee has no rounding slack. -/
theorem ordinary_minor_gap (k a : ℕ) (hk : 1≤k) (x fee : ℝ) (hfee : 0<fee)
    (hcap : x≤fee/((k:ℝ)*(Real.log k+81/10)))
    (hord : k*fee≤(a:ℝ)) :
    (k:ℝ)*x<(a:ℝ)/((k:ℝ)*(Real.log k+802113/100000)) := by
  have hk' : 1≤(k:ℝ) := by exact_mod_cast hk
  have hlog := Real.log_nonneg hk'
  have h₁ : 0<Real.log k+81/10 := by linarith
  have h₂ : 0<Real.log k+802113/100000 := by linarith
  have hkpos : 0<(k:ℝ) := by linarith
  have hA : (k:ℝ)*x≤fee/(Real.log k+81/10) := by
    calc
      _ ≤ k*(fee/((k:ℝ)*(Real.log k+81/10))) := mul_le_mul_of_nonneg_left hcap hkpos.le
      _ = _ := by field_simp
  apply hA.trans_lt
  apply (div_lt_div_iff₀ h₁ (mul_pos hkpos h₂)).2
  calc
    _ < ((k:ℝ)*fee)*(Real.log k+81/10) := by nlinarith [mul_pos hkpos hfee]
    _ ≤ _ := mul_le_mul_of_nonneg_right hord h₁.le

#print axioms even_moment_order_of_integral
#print axioms ordinary_minor_gap
end WaringEnvelope
