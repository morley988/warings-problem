import Waring.RationalHeightMin
import Mathlib.Tactic.Linarith

/-!
# Rational transference, with explicit constants

The complementary approximant used after (4.13) of Vaughan--Wooley (1995)
is constructed from Dirichlet approximation. This file proves the separation
and transference steps. Any reciprocal-sum estimate supplied as a premise is
kept explicit; it is not asserted by a new axiom.
-/

noncomputable section

namespace Waring.RationalHeight

def error (α : ℝ) (r : ℚ) : ℝ := |(r.den : ℝ) * α - (r.num : ℝ)|

theorem error_nonneg (α : ℝ) (r : ℚ) : 0 ≤ error α r := abs_nonneg _

theorem rational_separation {α : ℝ} {r s : ℚ} (hrs : r ≠ s) :
    1 ≤ (s.den : ℝ) * error α r + (r.den : ℝ) * error α s := by
  let d : ℤ := r.num * (s.den : ℤ) - s.num * (r.den : ℤ)
  have hd : d ≠ 0 := by
    intro hz
    apply hrs
    apply Rat.eq_iff_mul_eq_mul.mpr
    exact sub_eq_zero.mp hz
  have h1Z : (1 : ℤ) ≤ |d| := by
    have h := abs_pos.mpr hd
    omega
  have h1 : (1 : ℝ) ≤ |(d : ℝ)| := by exact_mod_cast h1Z
  have hid : (d : ℝ) =
      (r.den : ℝ) * ((s.den : ℝ) * α - (s.num : ℝ)) -
        (s.den : ℝ) * ((r.den : ℝ) * α - (r.num : ℝ)) := by
    dsimp [d]
    push_cast
    ring
  apply h1.trans
  rw [hid]
  apply (abs_sub _ _).trans
  rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ r.den),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ s.den)]
  unfold error
  exact le_of_eq (by ring)

/-- A complementary good approximant has denominator comparable to the
inverse error of the original approximant and half its absolute error. -/
theorem exists_complementary_approximant {α : ℝ} (r : ℚ)
    (he : 0 < error α r) (hgood : (r.den : ℝ) * error α r ≤ 1) :
    ∃ s : ℚ, s ≠ r ∧
      1 / (2 * error α r) ≤ (s.den : ℝ) ∧
      (s.den : ℝ) ≤ 2 / error α r ∧
      error α s ≤ error α r / 2 ∧
      (s.den : ℝ) * error α s ≤ 1 := by
  let e := error α r
  have he0 : 0 < e := he
  have hden : (1 : ℝ) ≤ r.den := by exact_mod_cast r.pos
  have he1 : e ≤ 1 := by
    have hm := mul_le_mul_of_nonneg_right hden he0.le
    nlinarith
  have heN : e ≠ 0 := he0.ne'
  have hscale : 1 ≤ 2 / e := by
    apply (le_div_iff₀ he0).mpr
    linarith
  have hV : 1 ≤ (2 / e)^2 := by nlinarith
  obtain ⟨s, hs, hsgood⟩ := exists_good_minimizer hV α
  have hsclpos : 0 < (2 : ℝ) / e := div_pos (by norm_num) he0
  have hscost : cost ((2/e)^2) α s ≤ 2 / e := by
    rw [hs]
    have HH := height_le_sqrt hV α
    simpa only [Real.sqrt_sq_eq_abs, abs_of_pos hsclpos] using HH
  have hsd : (s.den : ℝ) ≤ 2 / e := (le_max_left _ _).trans hscost
  have hse0 : (2/e)^2 * error α s ≤ 2 / e := (le_max_right _ _).trans hscost
  have hse : error α s ≤ e / 2 := by
    have hmul := mul_le_mul_of_nonneg_right hse0 (sq_nonneg e)
    have h1 : (2/e)^2 * error α s * e^2 = 4 * error α s := by field_simp; ring
    have h2 : (2/e) * e^2 = 2 * e := by field_simp
    rw [h1, h2] at hmul
    linarith
  have hsr : s ≠ r := by
    intro h
    subst s
    change e ≤ e / 2 at hse
    linarith
  have hsep := rational_separation (α := α) hsr.symm
  have hqse : (r.den : ℝ) * error α s ≤ (r.den : ℝ) * e / 2 := by
    have hm := mul_le_mul_of_nonneg_left hse (show (0 : ℝ) ≤ r.den by positivity)
    simpa only [mul_div_assoc] using hm
  have hslo : 1 / (2 * e) ≤ (s.den : ℝ) := by
    apply (div_le_iff₀ (mul_pos (by norm_num) he0)).mpr
    change (r.den : ℝ) * e ≤ 1 at hgood
    change 1 ≤ (s.den : ℝ) * e + (r.den : ℝ) * error α s at hsep
    nlinarith
  exact ⟨s, hsr, hslo, hsd, hse, hsgood⟩

/-- Transfer any denominator-form estimate to the denominator plus scaled
error. The base estimate is an explicit hypothesis for every good rational
approximant; the complementary-approximant argument is proved here. -/
theorem transfer_denominator_bound {α F V B K : ℝ}
    (hV : 0 ≤ V) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hbase : ∀ s : ℚ, (s.den : ℝ) * error α s ≤ 1 →
      F ≤ K * (V / (s.den : ℝ) + B + (s.den : ℝ)))
    (r : ℚ) (hgood : (r.den : ℝ) * error α r ≤ 1) :
    F ≤ 4 * K * (V / sumCost V α r + B + sumCost V α r) := by
  let q : ℝ := r.den
  let e := error α r
  let L := q + V * e
  have hq : 0 < q := by dsimp [q]; exact_mod_cast r.pos
  have he0 : 0 ≤ e := error_nonneg α r
  have hL : 0 < L := add_pos_of_pos_of_nonneg hq (mul_nonneg hV he0)
  have hqL : q ≤ L := le_add_of_nonneg_right (mul_nonneg hV he0)
  change F ≤ 4 * K * (V / L + B + L)
  have hVL : 0 ≤ V / L := div_nonneg hV hL.le
  by_cases hsmall : V * e ≤ q
  · have hLq : L ≤ 2 * q := by dsimp [L]; linarith
    have hrecip : V / q ≤ 2 * V / L := by
      apply (div_le_div_iff₀ hq hL).mpr
      have hm := mul_le_mul_of_nonneg_left hLq hV
      nlinarith
    rw [mul_div_assoc] at hrecip
    have hb := hbase r hgood
    change F ≤ K * (V / q + B + q) at hb
    calc
      F ≤ K * (V / q + B + q) := hb
      _ ≤ K * (4 * (V / L + B + L)) := by
        apply mul_le_mul_of_nonneg_left _ hK
        nlinarith
      _ = 4 * K * (V / L + B + L) := by ring
  · have hlarge : q < V * e := lt_of_not_ge hsmall
    have he : 0 < e := by
      by_contra hh
      have hh0 : V * e ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hV (le_of_not_gt hh)
      linarith
    obtain ⟨s, _, hslow, hsup, _, hsgood⟩ := exists_complementary_approximant r he hgood
    have hs : (0 : ℝ) < s.den := by exact_mod_cast s.pos
    have hsprod : 1 ≤ (s.den : ℝ) * (2 * e) :=
      (div_le_iff₀ (mul_pos (by norm_num) he)).mp hslow
    have hrecip : V / (s.den : ℝ) ≤ 2 * V * e := by
      apply (div_le_iff₀ hs).mpr
      have hm := mul_le_mul_of_nonneg_left hsprod hV
      nlinarith
    have hLL : L ≤ 2 * V * e := by dsimp [L]; linarith
    have hinv : 2 / e ≤ 4 * V / L := by
      apply (div_le_div_iff₀ he hL).mpr
      nlinarith
    have hsd : (s.den : ℝ) ≤ 4 * V / L := hsup.trans hinv
    rw [mul_div_assoc] at hsd
    have hVe : V * e ≤ L := le_add_of_nonneg_left hq.le
    have hb := hbase s hsgood
    calc
      F ≤ K * (V / (s.den : ℝ) + B + (s.den : ℝ)) := hb
      _ ≤ K * (4 * (V / L + B + L)) := by
        apply mul_le_mul_of_nonneg_left _ hK
        nlinarith
      _ = 4 * K * (V / L + B + L) := by ring

/-- Intrinsic-height form of the transference step. In applications
`V=N*J`, `B=N+J`, and `F` is the reciprocal sum or large-sieve quantity.
Only its denominator-form bound remains a premise. -/
theorem transfer_to_intrinsic_height {α F V B K : ℝ}
    (hV : 1 ≤ V) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hbase : ∀ s : ℚ, (s.den : ℝ) * error α s ≤ 1 →
      F ≤ K * (V / (s.den : ℝ) + B + (s.den : ℝ))) :
    F ≤ 8 * K * (V / height V α + B + height V α) := by
  have hV0 : 0 ≤ V := zero_le_one.trans hV
  obtain ⟨r, hr, hgood⟩ := exists_good_minimizer hV α
  have h := transfer_denominator_bound hV0 hB hK hbase r hgood
  have hcompare := max_sum_cost_comparison hV0 α r
  rw [hr] at hcompare
  have hH : 0 < height V α := height_pos V α
  have hL : 0 < sumCost V α r := hH.trans_le hcompare.1
  have hrecip : V / sumCost V α r ≤ V / height V α :=
    div_le_div_of_nonneg_left hV0 hH hcompare.1
  have hVdiv : 0 ≤ V / height V α := div_nonneg hV0 hH.le
  calc
    F ≤ 4 * K * (V / sumCost V α r + B + sumCost V α r) := h
    _ ≤ 4 * K * (2 * (V / height V α + B + height V α)) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) hK)
      linarith [hcompare.2]
    _ = 8 * K * (V / height V α + B + height V α) := by ring

#print axioms exists_complementary_approximant
#print axioms transfer_to_intrinsic_height

end Waring.RationalHeight
