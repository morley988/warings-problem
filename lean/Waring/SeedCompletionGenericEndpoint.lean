import Waring.FirstStageAdmissibility

/-! # Rational endpoint moments in every degree at least two -/

noncomputable section
namespace Waring.SeedCompletionGenericEndpoint
open SmoothMoments FirstStageTransport

def offsetExponent (k : ℕ) : ℕ → ℚ
  | 0 => 2
  | n+1 => 1+offsetExponent k n+(2*((n : ℚ)+2)-offsetExponent k n)/(k : ℚ)

def genericMomentExponent (k s : ℕ) : ℚ := offsetExponent k (s-2)

def genericMomentExcess (k s : ℕ) : ℚ := genericMomentExponent k s-s

theorem offsetExponent_bounds {k : ℕ} (hk : 2≤k) (n : ℕ) :
    (n : ℚ)+2≤offsetExponent k n ∧ offsetExponent k n≤2*(n : ℚ)+2 := by
  have hk2 : (2 : ℚ)≤k := by exact_mod_cast hk
  have hkp : (0 : ℚ)<k := by linarith
  induction n with
  | zero => norm_num [offsetExponent]
  | succ n ih =>
    have hn : 0≤(2*((n : ℚ)+2)-offsetExponent k n)/(k : ℚ) :=
      div_nonneg (by linarith [ih.2]) hkp.le
    have hu : (2*((n : ℚ)+2)-offsetExponent k n)/(k : ℚ)≤
        2*(n : ℚ)+3-offsetExponent k n := by
      apply (div_le_iff₀ hkp).mpr
      have hm := mul_nonneg (show (0 : ℚ)≤k-2 by linarith)
        (show (0 : ℚ)≤2*(n : ℚ)+3-offsetExponent k n by linarith [ih.2])
      nlinarith [ih.2]
    rw [offsetExponent]
    push_cast
    constructor <;> linarith [ih.1]

theorem offset_excess_monotone {k : ℕ} (hk : 2≤k) :
    Monotone (fun n : ℕ => offsetExponent k n-((n : ℚ)+2)) := by
  apply monotone_nat_of_le_succ
  intro n
  have hb := offsetExponent_bounds hk n
  have hk0 : (0 : ℚ)≤k := by positivity
  have hd : 0≤(2*((n : ℚ)+2)-offsetExponent k n)/(k : ℚ) :=
    div_nonneg (by linarith [hb.2]) hk0
  rw [offsetExponent]
  push_cast
  linarith

theorem offsetExponent_admissible {k : ℕ} (hk : 2≤k) (n : ℕ) :
    AdmissibleExponent k (2*(n+2)) (offsetExponent k n : ℝ) := by
  induction n with
  | zero => simpa [offsetExponent] using FourthMomentSeed.admissibleExponent_four hk
  | succ n ih =>
    have hu : (offsetExponent k n : ℝ)≤2*(n : ℝ)+2 := by
      exact_mod_cast (offsetExponent_bounds hk n).2
    have hi : AdmissibleExponent k (2*((n+1)+1)) (offsetExponent k n : ℝ) := by
      simpa only [Nat.add_assoc] using ih
    have H := endpoint_admissible (s := n+1) (show 0<k by omega) hi (by push_cast; linarith)
    convert H using 1 <;>
      simp only [offsetExponent,Rat.cast_add,Rat.cast_one,Rat.cast_div,Rat.cast_sub,
        Rat.cast_mul,Rat.cast_ofNat,Rat.cast_natCast] <;> push_cast <;> ring

theorem genericMomentExponent_admissible {k s : ℕ} (hk : 2≤k) (hs : 2≤s) :
    AdmissibleExponent k (2*s) (genericMomentExponent k s : ℝ) := by
  simpa only [genericMomentExponent,Nat.sub_add_cancel hs] using offsetExponent_admissible hk (s-2)

theorem genericMomentExponent_bounds {k s : ℕ} (hk : 2≤k) (hs : 2≤s) :
    (s : ℚ)≤genericMomentExponent k s ∧ genericMomentExponent k s≤2*(s : ℚ)-2 := by
  have hh := offsetExponent_bounds hk (s-2)
  have he : ((s-2 : ℕ) : ℚ)=(s : ℚ)-2 := by rw [Nat.cast_sub hs]; norm_num
  rw [he] at hh
  dsimp only [genericMomentExponent]
  constructor <;> linarith [hh.1,hh.2]

theorem genericMomentExcess_nonneg {k s : ℕ} (hk : 2≤k) (hs : 2≤s) :
    0≤genericMomentExcess k s := sub_nonneg.mpr (genericMomentExponent_bounds hk hs).1

theorem genericMomentExcess_mono {k s t : ℕ} (hk : 2≤k) (hs : 2≤s) (hst : s≤t) :
    genericMomentExcess k s≤genericMomentExcess k t := by
  have ht : 2≤t := hs.trans hst
  have h := offset_excess_monotone hk (Nat.sub_le_sub_right hst 2)
  have he (u : ℕ) (hu : 2≤u) : ((u-2 : ℕ) : ℚ)+2=(u : ℚ) := by
    exact_mod_cast Nat.sub_add_cancel hu
  simpa only [genericMomentExcess,genericMomentExponent,he s hs,he t ht] using h

#print axioms genericMomentExponent_admissible
#print axioms genericMomentExcess_mono
end Waring.SeedCompletionGenericEndpoint
