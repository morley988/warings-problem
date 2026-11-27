import Waring.RationalTransference
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Exact matching-cutoff arithmetic for the published basic coefficient bounds

The analytic estimates in Vaughan--Wooley 1995 Corollary 4.2.1 and Lemma 4.3
are not asserted here. We formalize their rational approximation and scale
hypotheses, including the original auxiliary-arc error cutoff and fixed
positive integer phase multipliers.
-/

noncomputable section
namespace Waring.BasicMatching
open Waring.RationalHeight

/-- The literal auxiliary minor-arc exclusion at denominator cutoff P and
approximation-error cutoff 1/X. Intersect with [0,1] if an arc set is needed. -/
def MinorAtCutoff (P X α : ℝ) : Prop :=
  ∀ r : ℚ, error α r ≤ 1/X → P < (r.den : ℝ)

/-- Dirichlet supplies a reduced approximant at every real cutoff X≥1. -/
theorem exists_approximant {X : ℝ} (hX : 1 ≤ X) (α : ℝ) :
    ∃ r : ℚ, (r.den : ℝ) ≤ X ∧ error α r ≤ 1/X := by
  let n := ⌊X⌋₊
  have hn : 0 < n := Nat.floor_pos.mpr hX
  have hXp : 0 < X := zero_lt_one.trans_le hX
  obtain ⟨r,herr,hden⟩ := Real.exists_rat_abs_sub_le_and_den_le α hn
  refine ⟨r,(show (r.den:ℝ) ≤ n by exact_mod_cast hden).trans (Nat.floor_le hXp.le),?_⟩
  have hrd : (0:ℝ) < r.den := by exact_mod_cast r.pos
  have hn1 : (0:ℝ) < (n:ℝ)+1 := by positivity
  calc
    error α r = (r.den:ℝ)*|α-(r:ℝ)| := denominator_error α r
    _ ≤ (r.den:ℝ)*(1/(((n:ℝ)+1)*(r.den:ℝ))) := mul_le_mul_of_nonneg_left herr hrd.le
    _ = 1/((n:ℝ)+1) := by field_simp
    _ ≤ 1/X := one_div_le_one_div_of_le hXp (Nat.lt_floor_add_one X).le

/-- The original auxiliary minor-arc exclusion gives a genuine intrinsic
height lower bound with its error-cutoff loss retained. -/
theorem minor_height_lower {P X V α : ℝ} (hminor : MinorAtCutoff P X α)
    (hX : 0 < X) (hV : 0 < V) : min P (V/X) < height V α := by
  obtain ⟨r,hr⟩ := exists_minimizer hV α
  rw [← hr]
  by_cases he : error α r ≤ 1/X
  · exact (min_le_left _ _).trans_lt ((hminor r he).trans_le (le_max_left _ _))
  · have he' : 1/X < error α r := lt_of_not_ge he
    have hm := mul_lt_mul_of_pos_left he' hV
    have hm' : V/X < V*error α r := by simpa only [mul_one_div] using hm
    exact (min_le_right _ _).trans_lt (hm'.trans_le (le_max_right _ _))

/-- A fixed phase multiplier costs only that fixed factor in the denominator
cutoff. The original minor arcs need not be invariant under multiplication. -/
theorem denominator_lower_after_multiplier {P X α : ℝ}
    (hminor : MinorAtCutoff P X α) (hP : 0 < P) (hX : 0 < X)
    (c : ℕ) (hc : 0 < c) (r : ℚ) (herr : error ((c:ℝ)*α) r ≤ 1/X) :
    P < (c:ℝ)*(r.den:ℝ) := by
  have hheight : P < height (P*X) α := by
    have hh := minor_height_lower hminor hX (mul_pos hP hX)
    simpa only [mul_div_cancel_right₀ P hX.ne',min_self] using hh
  have hq : 0 < c*r.den := Nat.mul_pos hc r.pos
  have hb := height_le_unreduced (V := P*X) (α := α) (mul_nonneg hP.le hX.le) r.num hq
  have heq : |((c*r.den:ℕ):ℝ)*α-(r.num:ℝ)| = error ((c:ℝ)*α) r := by
    unfold error
    push_cast
    congr 1
    ring
  rw [heq] at hb
  have herr' : (P*X)*error ((c:ℝ)*α) r ≤ P := by
    have hh := mul_le_mul_of_nonneg_left herr (mul_nonneg hP.le hX.le)
    have hid : (P*X)*(1/X)=P := by field_simp
    rwa [hid] at hh
  by_contra hn
  have hden : (c:ℝ)*(r.den:ℝ) ≤ P := le_of_not_gt hn
  have hb' : height (P*X) α ≤ P := hb.trans (max_le (by exact_mod_cast hden) herr')
  linarith

/-- The source's external matching interval retains the positive R power.
Here v is the conductor exponent, kb is k times the proposed basic saving,
and rho is k(k-j) in the original auxiliary-arc definition. -/
theorem matchingCutoff_bounds {P R v kb rho η : ℝ}
    (hP : 1 ≤ P) (hR : 1 ≤ R) (hRup : R ≤ P^η) (hrho : 0 ≤ rho)
    (hlower : kb ≤ v-1) (hmargin : rho*η ≤ 1-kb) :
    P^kb ≤ P^(v-1)*R^rho ∧ P^(v-1)*R^rho ≤ P^v/P^kb := by
  have hPp : 0 < P := zero_lt_one.trans_le hP
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  constructor
  · apply (Real.rpow_le_rpow_of_exponent_le hP hlower).trans
    exact le_mul_of_one_le_right (Real.rpow_nonneg hPp.le _) (Real.one_le_rpow hR hrho)
  · calc
      P^(v-1)*R^rho ≤ P^(v-1)*(P^η)^rho :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hR0 hRup hrho) (Real.rpow_nonneg hPp.le _)
      _ = P^(v-1+η*rho) := by rw [← Real.rpow_mul hPp.le, ← Real.rpow_add hPp]
      _ ≤ P^(v-kb) := Real.rpow_le_rpow_of_exponent_le hP (by nlinarith only [hmargin])
      _ = _ := Real.rpow_sub hPp _ _

/-- The checked strict cap kb<1 permits a positive smoothness exponent. -/
theorem exists_matching_smoothness {kb rho : ℝ} (hkb : kb < 1) (hrho : 0 ≤ rho) :
    ∃ η : ℝ, 0 < η ∧ rho*η ≤ 1-kb := by
  have hgap : 0 < 1-kb := sub_pos.mpr hkb
  refine ⟨(1-kb)/(2*(rho+1)),by positivity,?_⟩
  have hden : 0 < 2*(rho+1) := by positivity
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hden).mpr
  nlinarith only [hgap,hrho,mul_nonneg hrho hgap.le]

#print axioms exists_approximant
#print axioms minor_height_lower
#print axioms denominator_lower_after_multiplier
#print axioms matchingCutoff_bounds
#print axioms exists_matching_smoothness

end Waring.BasicMatching
