import WaringEnvelope.Check
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

/-! # Continuous meaning of Weyl cells in the conductor menu

A degree-j reduction exchanges a defect σ for three simultaneous
lower bounds. In the long-conductor tail the degree is chosen separately
at each conductor by rounding a fixed positive slope times its height.
-/

noncomputable section

namespace WaringEnvelope

/-- The better of repeated Weyl differencing and the Vinogradov exponent. -/
def weylWeight (j : ℕ) : ℕ := min (2^(j-1)) (j*(j-1))

/-- The three inequalities required by the degree-reduction estimate. -/
def WeylAt (j : ℕ) (θ u σ : ℝ) : Prop :=
  (weylWeight j : ℝ) * σ ≤ u/(j+1) - j*θ ∧
  (weylWeight j : ℝ) * σ ≤ 1-u/(j+1)-θ ∧
  (weylWeight j : ℝ) * σ ≤ j-u-j*θ

def WeylBranch (k : ℕ) (θ u σ : ℝ) : Prop :=
  ∃ j : ℕ, 2 ≤ j ∧ j ≤ k ∧ WeylAt j θ u σ

def weylLower (j : ℕ) (θ σ : ℝ) : ℝ :=
  (j+1) * ((weylWeight j : ℝ)*σ + j*θ)

def weylUpper (j : ℕ) (θ σ : ℝ) : ℝ :=
  min ((j+1)*(1-θ-(weylWeight j : ℝ)*σ))
    (j-j*θ-(weylWeight j : ℝ)*σ)

/-- Exact interval of a given integral Weyl degree. -/
theorem weylAt_iff_endpoints (j : ℕ) (θ u σ : ℝ) :
    WeylAt j θ u σ ↔ weylLower j θ σ ≤ u ∧ u ≤ weylUpper j θ σ := by
  have hj : 0 < (j : ℝ)+1 := by positivity
  unfold WeylAt weylLower weylUpper
  rw [le_min_iff]
  constructor
  · rintro ⟨h₁,h₂,h₃⟩
    have ha : (weylWeight j : ℝ)*σ + j*θ ≤ u/(j+1) := by linarith
    have hb : u/(j+1) ≤ 1-θ-(weylWeight j : ℝ)*σ := by linarith
    exact ⟨by simpa [mul_comm] using (le_div_iff₀ hj).mp ha,
      by simpa [mul_comm] using (div_le_iff₀ hj).mp hb, by linarith⟩
  · rintro ⟨h₁,h₂,h₃⟩
    have ha : (weylWeight j : ℝ)*σ + j*θ ≤ u/(j+1) :=
      (le_div_iff₀ hj).mpr (by simpa [mul_comm] using h₁)
    have hb : u/(j+1) ≤ 1-θ-(weylWeight j : ℝ)*σ :=
      (div_le_iff₀ hj).mpr (by simpa [mul_comm] using h₂)
    exact ⟨by linarith, by linarith, by linarith⟩

theorem interval_has_weyl_branch (j k : ℕ) (θ u σ : ℝ) (hj : 2 ≤ j) (hjk : j ≤ k)
    (hl : weylLower j θ σ ≤ u) (hu : u ≤ weylUpper j θ σ) :
    WeylBranch k θ u σ :=
  ⟨j,hj,hjk,(weylAt_iff_endpoints j θ u σ).2 ⟨hl,hu⟩⟩

/-- The numerical Weyl inequalities also have their quotient form. -/
theorem weylAt_iff_saving (j : ℕ) (θ u σ : ℝ) (hj : 2 ≤ j) :
    WeylAt j θ u σ ↔
    σ ≤ min (u/(j+1)-j*θ) (min (1-u/(j+1)-θ) (j-u-j*θ)) / weylWeight j := by
  have hcast : 0 < (weylWeight j : ℝ) := by
    exact_mod_cast (show 0 < weylWeight j by
      unfold weylWeight
      exact lt_min (by positivity) (Nat.mul_pos (by omega) (by omega)))
  rw [le_div_iff₀ hcast, le_min_iff, le_min_iff]
  simp only [WeylAt, mul_comm σ]

/-- For a continuous conductor in [cut,M], use j=ceil(slope*u). The three
tests are precisely the conservative lower bounds used by the tail menu.
This theorem has no conductor-grid hypothesis. -/
theorem continuous_weyl_tail (k : ℕ) (θ u σ cut slope M : ℝ)
    (hcut : 2 ≤ cut) (hslope : 1 ≤ slope) (hθ : 0 ≤ θ) (hσ : 0 ≤ σ)
    (hlo : cut ≤ u) (hhi : u ≤ M) (hk : slope*M+1 ≤ k)
    (h₁ : σ*slope*(slope+1/cut)*M^2 ≤
      1/(slope+2/cut) - (slope+1/cut)*M*θ)
    (h₂ : σ*slope*(slope+1/cut)*M^2 ≤ 1-1/slope-θ)
    (h₃ : σ*slope*(slope+1/cut)*M^2 ≤
      (slope-1)*cut - (slope+1/cut)*M*θ) : WeylBranch k θ u σ := by
  let j := ⌈slope*u⌉₊
  have hc : 0 < cut := by linarith
  have hs : 0 < slope := by linarith
  have hu : 0 < u := by linarith
  have hM : 0 < M := lt_of_lt_of_le hu hhi
  have hjlower : slope*u ≤ (j : ℝ) := Nat.le_ceil _
  have hjupper : (j : ℝ) ≤ slope*u+1 :=
    (Nat.ceil_lt_add_one (mul_nonneg hs.le hu.le)).le
  have hjtwo : 2 ≤ j := by
    have h : (2 : ℝ) ≤ j := calc
      2 ≤ u := hcut.trans hlo
      _ ≤ slope*u := le_mul_of_one_le_left hu.le hslope
      _ ≤ _ := hjlower
    exact_mod_cast h
  have hjk : j ≤ k := by
    have h : (j : ℝ) ≤ k := hjupper.trans ((add_le_add_right
      (mul_le_mul_of_nonneg_left hhi hs.le) 1).trans hk)
    exact_mod_cast h
  have hratio : 1 ≤ u/cut := (one_le_div hc).2 hlo
  have hb0 : 0 ≤ slope+1/cut := by positivity
  have hju : (j : ℝ) ≤ (slope+1/cut)*u := by
    rw [add_mul, one_div_mul_eq_div]
    linarith
  have hjM : (j : ℝ) ≤ (slope+1/cut)*M :=
    hju.trans (mul_le_mul_of_nonneg_left hhi hb0)
  have hjm : (j : ℝ)-1 ≤ slope*M :=
    (show (j : ℝ)-1 ≤ slope*u by linarith).trans (mul_le_mul_of_nonneg_left hhi hs.le)
  have hw' : (weylWeight j : ℝ) ≤ (j : ℝ)*(j-1) := by
    have h := min_le_right (2^(j-1)) (j*(j-1))
    exact_mod_cast (by simpa only [weylWeight, Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ j),
      Nat.cast_one] using (show ((weylWeight j : ℕ) : ℝ) ≤ ((j*(j-1) : ℕ) : ℝ) by
        exact_mod_cast h) : (weylWeight j : ℝ) ≤ (j : ℝ)*(j-1))
  have hw : (weylWeight j : ℝ)*σ ≤ σ*slope*(slope+1/cut)*M^2 := by
    have hm := mul_le_mul hjM hjm (sub_nonneg.mpr (show (1 : ℝ) ≤ j by exact_mod_cast (by omega : 1 ≤ j)))
      (mul_nonneg hb0 hM.le)
    nlinarith only [mul_le_mul_of_nonneg_right (hw'.trans hm) hσ]
  have hden : 0 < (j : ℝ)+1 := by positivity
  have hb : 0 < slope+2/cut := by positivity
  have hju' : (j : ℝ)+1 ≤ u*(slope+2/cut) := by
    have hr : 2 ≤ (2/cut)*u := by
      calc
        2 ≤ 2*(u/cut) := by linarith
        _ = _ := by ring
    linarith only [hjupper, hr]
  have hfrac₁ : 1/(slope+2/cut) ≤ u/(j+1) := by
    apply (div_le_div_iff₀ hb hden).mpr
    simpa only [one_mul] using hju'
  have hfrac₂ : u/(j+1) ≤ 1/slope := by
    apply (div_le_div_iff₀ hden hs).mpr
    linarith only [hjlower]
  have hprod := mul_le_mul_of_nonneg_right hjM hθ
  have hrest : (slope-1)*cut ≤ (j : ℝ)-u := by
    have h := mul_le_mul_of_nonneg_left hlo (show 0 ≤ slope-1 by linarith)
    linarith only [hjlower,h]
  refine ⟨j,hjtwo,hjk,?_,?_,?_⟩
  · linarith only [hw,h₁,hfrac₁,hprod]
  · linarith only [hw,h₂,hfrac₂]
  · linarith only [hw,h₃,hrest,hprod]

#print axioms weylAt_iff_endpoints
#print axioms continuous_weyl_tail

end WaringEnvelope
