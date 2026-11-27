import WaringFieldSmall.Trace
import WaringLinear.FieldMarkedEndgame

/-! # The physical shortening rule for the finite field schedules -/
noncomputable section
open WaringLinear WaringEnvelope
namespace WaringFieldSmall
variable {K : Type*} [Field K] [NumberField K]

/-- The conductor condition is restricted to the finitely many moduli
and positive savings which appear in the given schedule. -/
def RowCoverage (Listed : Schedule → Prop) (k : ℕ) : Prop :=
  ∀ band, Listed band → band.lo≤k → k≤band.hi → ∀ u∈band.data,
    let s := unpack u
    let M := (s.modulus:ℝ)/modulusScale
    let z := (s.gain:ℝ)/(2*scale)
    0<z ∧ 1<M ∧ M<k ∧ ∃ σ, 2*z<σ ∧ ∀ v : ℝ, 1<v → v≤M → fieldConductorStage k (M/k) v σ

private theorem defect_mono (W : ℝ → TraceSumFamily K) {k r : ℕ} {x y : ℝ}
    (h : cutoffAdmissible W k r x) (hxy : x≤y) : cutoffAdmissible W k r y := by
  intro ε hε
  obtain ⟨η,hη,hwin⟩ := h ε hε
  refine ⟨η,hη,?_⟩
  intro t ht hT
  obtain ⟨D,hD,old⟩ := hwin t ht hT
  refine ⟨D,hD,?_⟩
  intro X hX
  exact (old X hX).trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast hX) (by linarith only [mul_le_mul_of_nonneg_left hxy (Nat.cast_nonneg (α:=ℝ) k)])) hD)

private theorem rounded_fibre_majorizes (k hi d : ℕ) (s : Run) (hk : 0<k) (hhi : k≤hi) :
    max 0 (normalized k d-(2/(k:ℝ))*min ((s.gain:ℝ)/(2*scale))
        (((U:ℝ)/V)*((s.modulus:ℝ)/modulusScale)*normalized k d/2)) ≤
      normalized k (fibreRound hi s d) := by
  let n := min s.gain (d*thetaNum*s.modulus/(hi*thetaDen*modulusScale))
  have hkp : 0<(k:ℝ) := by exact_mod_cast hk
  have hhip : 0<(hi:ℝ) := by exact_mod_cast hk.trans_le hhi
  have hscale : (0:ℝ)<scale := by norm_num [scale]
  have hn : (n:ℝ)≤s.gain := by exact_mod_cast min_le_left s.gain (d*thetaNum*s.modulus/(hi*thetaDen*modulusScale))
  have hnq : (n:ℝ)≤(d:ℝ)*thetaNum*s.modulus/(hi*thetaDen*modulusScale) := by
    have hb := Nat.cast_div_le (α:=ℝ) (m:=d*thetaNum*s.modulus) (n:=hi*thetaDen*modulusScale)
    push_cast at hb
    exact (show (n:ℝ)≤(d*thetaNum*s.modulus/(hi*thetaDen*modulusScale):ℕ) by
      exact_mod_cast min_le_right s.gain (d*thetaNum*s.modulus/(hi*thetaDen*modulusScale))).trans hb
  have hh : (k:ℝ)≤hi := by exact_mod_cast hhi
  have hd1 : 0<(k:ℝ)*thetaDen*modulusScale := by norm_num [thetaDen,modulusScale];positivity
  have hd2 : (k:ℝ)*thetaDen*modulusScale≤hi*thetaDen*modulusScale := by
    norm_num [thetaDen,modulusScale];linarith
  have hq := hnq.trans (div_le_div_of_nonneg_left (by positivity) hd1 hd2)
  have hlin : (n:ℝ)/(scale*k)≤2/k*((U:ℝ)/V*((s.modulus:ℝ)/modulusScale)*normalized k d/2) := by
    have h' := div_le_div_of_nonneg_right hq (mul_nonneg hscale.le hkp.le)
    convert h' using 1
    norm_num [U,V,thetaNum,thetaDen,modulusScale,normalized,scale]
    <;> ring
  have hconst : (n:ℝ)/(scale*k)≤2/k*((s.gain:ℝ)/(2*scale)) := by
    have h' := div_le_div_of_nonneg_right hn (mul_nonneg hscale.le hkp.le)
    convert h' using 1
    ring
  have hmin : (n:ℝ)/(scale*k)≤2/k*min ((s.gain:ℝ)/(2*scale))
        (((U:ℝ)/V)*((s.modulus:ℝ)/modulusScale)*normalized k d/2) := by
    rw [mul_min_of_nonneg _ _ (by positivity)]
    exact le_min hconst hlin
  have hds : (d:ℝ)-n≤((d-n:ℕ):ℝ) := by
    by_cases h : n≤d
    · rw [Nat.cast_sub h]
    · have hh' : (d:ℝ)≤n := by exact_mod_cast (le_of_not_ge h)
      rw [Nat.sub_eq_zero_of_le (le_of_not_ge h),Nat.cast_zero];linarith
  have hD := div_le_div_of_nonneg_right hds (mul_nonneg hscale.le hkp.le)
  rw [sub_div] at hD
  apply max_le (div_nonneg (Nat.cast_nonneg _) (mul_nonneg hscale.le hkp.le))
  change (d:ℝ)/(scale*k)-_≤((d-n:ℕ):ℝ)/(scale*k)
  linarith only [hD,hmin]

theorem roundedShortening_of_physical (Listed : Schedule → Prop) (W : ℝ → TraceSumFamily K) (k : ℕ) (hk : 0<k)
    (cov : RowCoverage Listed k) (step : ShorteningStep fieldConductorStage (cutoffAdmissible W k) k) :
    RoundedShortening Listed W k := by
  intro band hlist hl hh u hu r d hr er old
  obtain ⟨hz,hlow,hhigh,cert⟩ := cov band hlist hl hh u hu
  have result := step r (normalized k d) _ _ hr (Nat.even_iff.mpr er) old
    (by unfold normalized; positivity) hz hlow hhigh cert
  exact defect_mono W result (rounded_fibre_majorizes k band.hi d (unpack u) hk hh)

#print axioms roundedShortening_of_physical
end WaringFieldSmall
