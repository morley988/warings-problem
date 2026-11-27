import WaringEnvelope.PotentialIntegral
import WaringEnvelope.Check
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! # Integral charge of the real conductor tail

At modulus `m` the height is `1/(14 m²)` and the retained length is `λ*m`.
The cubic breakpoint permits exact integration between any two positive
moduli, followed by the logarithmic charge below the final conductor cap.
-/
noncomputable section
namespace WaringEnvelope
open MeasureTheory Set
open scoped BigOperators Interval

def tailKnee (v m : ℝ) : ℝ := 1/(7*v*m^3)

private lemma tailKnee_pos {v m : ℝ} (hv : 0<v) (hm : 0<m) : 0<tailKnee v m := by
  unfold tailKnee
  positivity

private lemma tailKnee_deriv {v x : ℝ} (hv : 0<v) (hx : 0<x) :
    HasDerivAt (tailKnee v) (-3/(7*v*x^4)) x := by
  have hd : HasDerivAt (fun m : ℝ => 7*v*m^3) (7*v*(3*x^2)) x := by
    simpa using (hasDerivAt_pow 3 x).const_mul (7*v)
  have hz : 7*v*x^3≠0 := by positivity
  convert (hasDerivAt_const x (1:ℝ)).div hd hz using 1
  field_simp
  ring

private lemma tail_sixth_deriv {v x : ℝ} (hv : 0<v) (hx : 0<x) :
    HasDerivAt (fun m : ℝ => 6/(v*m)) (-6/(v*x^2)) x := by
  have hd : HasDerivAt (fun m : ℝ => v*m) v x := by simpa using (hasDerivAt_id x).const_mul v
  have hz : v*x≠0 := by positivity
  convert (hasDerivAt_const x (6:ℝ)).div hd hz using 1
  field_simp
  ring

/-- Exact continuous contribution between the two cubic breakpoints. -/
theorem tail_between_knees (P : ℝ → ℝ) (v f g : ℝ) (hv : 0<v) (hf : 0<f) (hfg : f≤g)
    (hc : ContinuousOn P (Ioi 0)) (hp : ∀ t, 0<t → 0<P t)
    (hb : ∀ m ∈ Icc f g, ∀ t, 0<t → min (1/(14*m^2)) (v*m*t/2)≤P t) :
    (∫ t in tailKnee v g..tailKnee v f, 1/P t) ≤ 6/(v*f)-6/(v*g) := by
  let G (t : ℝ) := 1/P t
  let d' (m : ℝ) := -3/(7*v*m^4)
  let j' (m : ℝ) := -6/(v*m^2)
  have hI (x : ℝ) (hx : x∈uIcc f g) : x∈Icc f g := by simpa [uIcc_of_le hfg] using hx
  have hpos (x : ℝ) (hx : x∈uIcc f g) : 0<x := hf.trans_le (hI x hx).1
  have hder (x : ℝ) (hx : x∈uIcc f g) : HasDerivAt (tailKnee v) (d' x) x := tailKnee_deriv hv (hpos x hx)
  have hdiff : ContinuousOn (tailKnee v) (uIcc f g) := fun x hx => (hder x hx).continuousAt.continuousWithinAt
  have hdc : ContinuousOn d' (uIcc f g) := by
    unfold d'
    exact continuousOn_const.div (continuousOn_const.mul (continuousOn_id.pow 4)) (fun x hx => by
      change 7*v*x^4≠0
      exact ne_of_gt (mul_pos (by positivity) (pow_pos (hpos x hx) _)))
  have hG : ContinuousOn G (Ioi 0) := continuousOn_const.div hc (fun t ht => (hp t ht).ne')
  have hmap : MapsTo (tailKnee v) (uIcc f g) (Ioi 0) := fun x hx => tailKnee_pos hv (hpos x hx)
  have hsub := intervalIntegral.integral_comp_mul_deriv' hder hdc (hG.mono (mapsTo_iff_image_subset.mp hmap))
  have hjs : ContinuousOn j' (uIcc f g) := by
    unfold j'
    apply continuousOn_const.div (continuousOn_const.mul (continuousOn_id.pow 2))
    intro x hx
    change v*x^2≠0
    exact (mul_pos hv (pow_pos (hpos x hx) _)).ne'
  have hgds : ContinuousOn (fun x => (G ∘ tailKnee v) x*d' x) (uIcc f g) :=
    (hG.comp hdiff hmap).mul hdc
  have hpoint (x : ℝ) (hx : x∈Icc f g) : j' x ≤ (G ∘ tailKnee v) x*d' x := by
    have hxp : 0<x := hf.trans_le hx.1
    have hk : v*x*(tailKnee v x)/2=1/(14*x^2) := by unfold tailKnee; field_simp; ring
    have hh := hb x hx (tailKnee v x) (tailKnee_pos hv hxp)
    rw [hk,min_self] at hh
    have hrec : G (tailKnee v x) ≤ 14*x^2 := by
      simpa [G] using (one_div_le_one_div_of_le (by positivity : 0<1/(14*x^2)) hh)
    have hneg : d' x≤0 := div_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity)
    have hcal : j' x=(14*x^2)*d' x := by unfold j' d'; field_simp; ring
    rw [hcal]
    exact mul_le_mul_of_nonpos_right hrec hneg
  have hmono := intervalIntegral.integral_mono_on (μ := volume) hfg hjs.intervalIntegrable hgds.intervalIntegrable hpoint
  have hjder (x : ℝ) (hx : x∈uIcc f g) : HasDerivAt (fun m : ℝ => 6/(v*m)) (j' x) x :=
    tail_sixth_deriv hv (hpos x hx)
  have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt hjder hjs.intervalIntegrable
  rw [hfund,hsub] at hmono
  rw [intervalIntegral.integral_symm]
  dsimp [G] at hmono
  linarith

private theorem linear_tail_interval (P : ℝ → ℝ) (L x y : ℝ)
    (hL : 0<L) (hx : 0<x) (hxy : x≤y) (hc : ContinuousOn P (Ioi 0))
    (hp : ∀ t, 0<t → 0<P t) (hb : ∀ t ∈ Icc x y, L*t/2≤P t) :
    (∫ t in x..y, 1/P t) ≤ (2/L)*Real.log (y/x) := by
  have hpos (t : ℝ) (ht : t∈uIcc x y) : 0<t := hx.trans_le ((Set.uIcc_of_le hxy ▸ ht : t ∈ Icc x y).1)
  have hP : ContinuousOn (fun t => 1/P t) (Ioi 0) :=
    continuousOn_const.div hc (fun t ht => (hp t ht).ne')
  have hG : ContinuousOn (fun t : ℝ => (2/L)*(1/t)) (uIcc x y) :=
    continuousOn_const.mul (continuousOn_const.div continuousOn_id (fun t ht => (hpos t ht).ne'))
  have hcmp : (∫ t in x..y, 1/P t) ≤ ∫ t in x..y, (2/L)*(1/t) := by
    apply intervalIntegral.integral_mono_on hxy (hP.mono (fun t ht => hpos t ht)).intervalIntegrable hG.intervalIntegrable
    intro t ht
    have htp : 0<t := hx.trans_le ht.1
    calc
      _ ≤ 1/(L*t/2) := one_div_le_one_div_of_le (by positivity) (hb t ht)
      _ = _ := by field_simp
  rwa [intervalIntegral.integral_const_mul,integral_one_div_of_pos hx (hx.trans_le hxy)] at hcmp

/-- Integrated cost from the last finite height `Z` down to a positive stop
below the final cubic breakpoint. The negative endpoint saving is kept. -/
theorem clipped_tail_integral (P : ℝ → ℝ) (v f g Z stop : ℝ)
    (hv : 0<v) (hf : 0<f) (hfg : f≤g) (hstop : 0<stop)
    (hcap : stop≤tailKnee v g) (hZ : 1/(14*f^2)≤Z)
    (hc : ContinuousOn P (Ioi 0)) (hp : ∀ t, 0<t → 0<P t)
    (hfinite : ∀ t, 0<t → min Z (v*f*t/2)≤P t)
    (htail : ∀ m ∈ Icc f g, ∀ t, 0<t → min (1/(14*m^2)) (v*m*t/2)≤P t) :
    (∫ t in stop..(2*Z/(v*f)), 1/P t) ≤
      2/(v*f)*Real.log (14*f^2*Z)+6/(v*f)-6/(v*g)+2/(v*g)*Real.log (tailKnee v g/stop) := by
  have hg : 0<g := hf.trans_le hfg
  have hZp : 0<Z := (show 0<1/(14*f^2) by positivity).trans_le hZ
  have hGH : tailKnee v f ≤ 2*Z/(v*f) := by
    unfold tailKnee
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hpre := (div_le_iff₀ (by positivity : 0<14*f^2)).mp hZ
    nlinarith [mul_le_mul_of_nonneg_left hpre (mul_pos hv hf).le]
  have htop := linear_tail_interval P (v*f) (tailKnee v f) (2*Z/(v*f)) (mul_pos hv hf)
    (tailKnee_pos hv hf) hGH hc hp (by
      intro t ht
      have hsub : v*f*t/2≤Z := by nlinarith [(le_div_iff₀ (mul_pos hv hf)).mp ht.2]
      simpa [min_eq_right hsub] using hfinite t ((tailKnee_pos hv hf).trans_le ht.1))
  have hlog : (2*Z/(v*f))/tailKnee v f=14*f^2*Z := by unfold tailKnee; field_simp; ring
  rw [hlog] at htop
  have hbottom := linear_tail_interval P (v*g) stop (tailKnee v g) (mul_pos hv hg)
    hstop hcap hc hp (by
      intro t ht
      have hsub : v*g*t/2≤1/(14*g^2) := by
        apply (le_div_iff₀ (by positivity : 0<14*g^2)).mpr
        have htk := (le_div_iff₀ (by positivity : 0<7*v*g^3)).mp ht.2
        nlinarith [htk]
      exact (min_eq_right hsub ▸ htail g ⟨hfg,le_rfl⟩ t (hstop.trans_le ht.1)))
  have hmiddle := tail_between_knees P v f g hv hf hfg hc hp htail
  have hPc : ContinuousOn (fun t => 1/P t) (Ioi 0) := continuousOn_const.div hc (fun t ht => (hp t ht).ne')
  have hi (x y : ℝ) (hx : 0<x) (hy : 0<y) : IntervalIntegrable (fun t => 1/P t) volume x y :=
    (hPc.mono (fun t ht => (lt_min hx hy).trans_le ht.1 : uIcc x y ⊆ Ioi 0)).intervalIntegrable
  have a := intervalIntegral.integral_add_adjacent_intervals (hi _ _ hstop (tailKnee_pos hv hg))
    (hi _ _ (tailKnee_pos hv hg) (tailKnee_pos hv hf))
  have b := intervalIntegral.integral_add_adjacent_intervals (hi _ _ hstop (tailKnee_pos hv hf))
    (hi _ _ (tailKnee_pos hv hf) (by positivity : 0<2*Z/(v*f)))
  linarith

/-- Terminal defect used by the unbounded numerical band. -/
def clippedStop (k : ℝ) : ℝ := 16/(Real.sqrt k*k*(Real.log k+81/10))

/-- The bound at the actual degree, with the negative reciprocal from the last
finite stage included. Here `v=U/V`, `f=F`, and `Z` is the last menu height. -/
theorem clipped_degree_price (P : ℝ → ℝ) (v f k Z : ℝ)
    (hv : 0<v) (hv1 : v≤1) (hf : 0<f) (hk : 1≤k) (hfg : f≤Real.sqrt k/8)
    (hZ : 1/(14*f^2)≤Z) (hc : ContinuousOn P (Ioi 0)) (hp : ∀ t, 0<t → 0<P t)
    (hfinite : ∀ t, 0<t → min Z (v*f*t/2)≤P t)
    (htail : ∀ m ∈ Icc f (Real.sqrt k/8), ∀ t, 0<t → min (1/(14*m^2)) (v*m*t/2)≤P t) :
    -2/(v*f)+(∫ t in clippedStop k..(2*Z/(v*f)), 1/P t) ≤
      2/(v*f)*Real.log (14*f^2*Z)+4/(v*f)+
        16/v*(Real.log ((64/(14*v))*(Real.log k+81/10))/Real.sqrt k) := by
  have hkp : 0<k := zero_lt_one.trans_le hk
  have hsp : 0<Real.sqrt k := Real.sqrt_pos.mpr hkp
  have hlog := Real.log_nonneg hk
  have hlogp : 0<Real.log k+81/10 := by linarith
  have hs : 0<clippedStop k := by unfold clippedStop; positivity
  have hr : tailKnee v (Real.sqrt k/8)/clippedStop k = (64/(14*v))*(Real.log k+81/10) := by
    unfold tailKnee clippedStop
    generalize hroot : Real.sqrt k = q
    have hq : 0<q := hroot ▸ hsp
    have hq2 : q^2=k := by rw [←hroot, Real.sq_sqrt hkp.le]
    rw [← hq2] at hlogp ⊢
    field_simp
    ring
  have hc1 : 1≤64/(14*v) := (le_div_iff₀ (by positivity)).2 (by linarith)
  have hc2 : 1≤Real.log k+81/10 := by linarith
  have hce : clippedStop k≤tailKnee v (Real.sqrt k/8) := by
    have hprod := one_le_mul_of_one_le_of_one_le hc1 hc2
    rw [←hr,le_div_iff₀ hs,one_mul] at hprod
    exact hprod
  have hb := clipped_tail_integral P v f (Real.sqrt k/8) Z (clippedStop k) hv hf hfg hs hce hZ
    hc hp hfinite htail
  rw [hr] at hb
  have hlinear (x : ℝ) : 2/(v*(Real.sqrt k/8))*x = 16/v*(x/Real.sqrt k) := by field_simp; ring
  rw [hlinear] at hb
  have hneg : 0≤6/(v*(Real.sqrt k/8)) := by positivity
  have hnum : -2/(v*f)+6/(v*f)=4/(v*f) := by ring
  linarith only [hb,hnum,hneg]

#print axioms clipped_degree_price
#print axioms clipped_tail_integral
#print axioms tail_between_knees
end WaringEnvelope
