import WaringEnvelope.FiniteDrift
import WaringEnvelope.ClippedPotential
import WaringEnvelope.TailCellSound

/-! # An attained drift for finite stages and the compact real tail

Every value of the gain is achieved by either an indexed certified action or
one real conductor in the compact conductor interval. Joint continuity and
compactness give continuity of the optimal gain in the normalized defect.
-/
noncomputable section
namespace WaringEnvelope
open Set MeasureTheory
open scoped BigOperators Interval

def tailRow (v m t : ℝ) : ℝ := min (1/(14*m^2)) (v*m*t/2)

def tailEnvelope (v f g t : ℝ) : ℝ :=
  sSup ((fun m : ℝ => tailRow v (max f m) t) '' Icc f g)

private theorem tailRow_continuous_clamped (v f : ℝ) (hf : 0<f) :
    Continuous (fun z : ℝ×ℝ => tailRow v (max f z.2) z.1) := by
  have hm : Continuous (fun z : ℝ×ℝ => max f z.2) := continuous_const.max continuous_snd
  have hpos (z : ℝ×ℝ) : 0<max f z.2 := hf.trans_le (le_max_left _ _)
  exact (continuous_const.div (continuous_const.mul (hm.pow 2))
    (fun z => (mul_pos (by norm_num) (pow_pos (hpos z) _)).ne')).min
    (((continuous_const.mul hm).mul continuous_fst).div_const 2)

theorem continuous_tailEnvelope (v f g : ℝ) (hf : 0<f) : Continuous (tailEnvelope v f g) :=
  isCompact_Icc.continuous_sSup (tailRow_continuous_clamped v f hf)

theorem tailEnvelope_attained (v f g t : ℝ) (hf : 0<f) (hfg : f≤g) :
    ∃ m∈Icc f g, tailEnvelope v f g t=tailRow v m t ∧
      ∀ n∈Icc f g, tailRow v n t≤tailRow v m t := by
  have hc : Continuous (fun m : ℝ => tailRow v (max f m) t) :=
    (tailRow_continuous_clamped v f hf).comp (Continuous.prodMk_right t)
  obtain ⟨m,hm,he,hmax⟩ := isCompact_Icc.exists_sSup_image_eq_and_ge (nonempty_Icc.mpr hfg) hc.continuousOn
  refine ⟨m,hm,?_,?_⟩
  · simpa only [tailEnvelope,max_eq_right hm.1] using he
  · intro n hn
    simpa only [max_eq_right hn.1,max_eq_right hm.1] using hmax n hn

theorem tailRow_le_envelope (v f g m t : ℝ) (hf : 0<f) (hm : m∈Icc f g) :
    tailRow v m t≤tailEnvelope v f g t := by
  obtain ⟨n,_,hn,hmax⟩ := tailEnvelope_attained v f g t hf (hm.1.trans hm.2)
  rw [hn]
  exact hmax m hm

theorem monotone_tailEnvelope (v f g : ℝ) (hv : 0<v) (hf : 0<f) (hfg : f≤g) :
    Monotone (tailEnvelope v f g) := by
  intro x y hxy
  obtain ⟨m,hm,he,_⟩ := tailEnvelope_attained v f g x hf hfg
  rw [he]
  refine le_trans ?_ (tailRow_le_envelope v f g m y hf hm)
  exact min_le_min le_rfl (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hxy
    (mul_pos hv (hf.trans_le hm.1)).le) (by norm_num))

namespace IndexedStages
variable {C k z₀ z m R} (p : IndexedStages C k z₀ z m R)

def extendedDrift (v f g t : ℝ) : ℝ := max (p.drift t) (tailEnvelope v f g t)

theorem continuous_extendedDrift (v f g : ℝ) (hf : 0<f) : Continuous (p.extendedDrift v f g) :=
  p.continuous_drift.max (continuous_tailEnvelope v f g hf)

theorem positive_extendedDrift (v f g t : ℝ) (ht : 0<t) : 0<p.extendedDrift v f g t :=
  (p.positive_drift t ht).trans_le (le_max_left _ _)

theorem monotone_extendedDrift (v f g : ℝ) (hv : 0<v) (hf : 0<f) (hfg : f≤g) :
    Monotone (p.extendedDrift v f g) :=
  fun _ _ hxy => max_le_max (p.monotone_drift hxy) ((monotone_tailEnvelope v f g hv hf hfg) hxy)

theorem row_le_extendedDrift (v f g : ℝ) (i : ℕ) (hi : i≤p.N) (t : ℝ) :
    p.rowDrift i t≤p.extendedDrift v f g t :=
  (p.row_le_drift i hi t).trans (le_max_left _ _)

theorem tail_le_extendedDrift (v f g M t : ℝ) (hf : 0<f) (hM : M∈Icc f g) :
    tailRow v M t≤p.extendedDrift v f g t :=
  (tailRow_le_envelope v f g M t hf hM).trans (le_max_right _ _)

theorem extendedDrift_attained (v f g t : ℝ) (hf : 0<f) (hfg : f≤g) :
    (∃ i≤p.N, p.extendedDrift v f g t=p.rowDrift i t) ∨
      ∃ M∈Icc f g, p.extendedDrift v f g t=tailRow v M t := by
  rcases le_total (tailEnvelope v f g t) (p.drift t) with h|h
  · left
    simpa only [extendedDrift,max_eq_left h] using p.exists_active t
  · right
    obtain ⟨M,hM,he,_⟩ := tailEnvelope_attained v f g t hf hfg
    exact ⟨M,hM,(max_eq_right h).trans he⟩

/-- The integral of the attained extended drift from the actual clipped stop
through *both* the real tail and all finite certified rows. -/
theorem extended_degree_integral (v f K D₀ : ℝ) (hv : 0<v) (hv1 : v≤1) (hf : 0<f)
    (hk : 1≤K) (hfg : f≤Real.sqrt K/8) (hlast : p.lengthAt p.N=v*f)
    (hZ : 1/(14*f^2)≤p.heightAt p.N) (hstart : 2*p.heightAt 0/p.lengthAt 0≤D₀) :
    (∫ t in clippedStop K..D₀, 1/p.extendedDrift v f (Real.sqrt K/8) t) ≤
      D₀/p.heightAt 0+R+2/(v*f)*Real.log (14*f^2*p.heightAt p.N)+4/(v*f)+
        16/v*(Real.log ((64/(14*v))*(Real.log K+81/10))/Real.sqrt K) := by
  let P := p.extendedDrift v f (Real.sqrt K/8)
  let knee := 2*p.heightAt p.N/(v*f)
  have hc : ContinuousOn P (Ioi 0) := (p.continuous_extendedDrift v f _ hf).continuousOn
  have hp (t : ℝ) (ht : 0<t) : 0<P t := p.positive_extendedDrift v f _ t ht
  have hfinite := potential_integral_bound P p.heightAt p.lengthAt p.N D₀ knee hc hp
    p.positive_height p.positive_length
    (fun i hi => div_le_div_of_nonneg_right (by exact_mod_cast (p.decreasing i hi).le) (Nat.cast_nonneg T))
    (fun i hi => div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
      (by exact_mod_cast p.increasing i hi) (Nat.cast_nonneg U)) (by positivity))
    (fun i hi t _ => p.row_le_extendedDrift v f _ i hi t) hstart (by rw [hlast])
  have he : (∑ i∈Finset.range p.N, 2/p.lengthAt i*Real.log (p.heightAt i/p.heightAt (i+1)))=R := by
    refine Eq.trans ?_ p.cost
    apply Finset.sum_congr rfl
    intro i _
    have hdiv : p.heightAt i/p.heightAt (i+1)=(p.height i:ℝ)/p.height (i+1) :=
      div_div_div_cancel_right₀ (by norm_num [T] : (T:ℝ)≠0) _ _
    rw [hdiv]; unfold lengthAt; ring
  rw [he,hlast] at hfinite
  have htail := clipped_degree_price P v f K (p.heightAt p.N) hv hv1 hf hk hfg hZ hc hp
    (fun t _ => by simpa only [rowDrift,hlast] using p.row_le_extendedDrift v f _ p.N le_rfl t)
    (fun M hm t _ => p.tail_le_extendedDrift v f _ M t hf hm)
  have hkn : 0<knee := div_pos (mul_pos (by norm_num) (p.positive_height _ le_rfl)) (mul_pos hv hf)
  have hD₀ : 0<D₀ := (div_pos (mul_pos (by norm_num) (p.positive_height 0 (by omega)))
    (p.positive_length 0 (by omega))).trans_le hstart
  have hsp : 0<clippedStop K := by
    have hK : 0<K:=zero_lt_one.trans_le hk
    have hlog := Real.log_nonneg hk
    unfold clippedStop
    positivity
  have hrec : ContinuousOn (fun t => 1/P t) (Ioi 0) :=
    continuousOn_const.div hc (fun t ht => (hp t ht).ne')
  have hi (x y : ℝ) (hx : 0<x) (hy : 0<y) : IntervalIntegrable (fun t => 1/P t)
      MeasureTheory.volume x y := (hrec.mono (fun t ht => (lt_min hx hy).trans_le ht.1 : uIcc x y⊆Ioi 0)).intervalIntegrable
  have hadd := intervalIntegral.integral_add_adjacent_intervals (hi _ _ hsp hkn) (hi _ _ hkn hD₀)
  change -2/(v*f)+(∫ t in clippedStop K..knee, 1/P t)≤_ at htail
  change (∫ t in clippedStop K..D₀, 1/P t) ≤ _
  rw [neg_div] at htail
  linarith only [hfinite,htail,hadd]

end IndexedStages

/-- The ordinary Weyl action is strictly above twice the requested tail
height for the entire large-conductor interval, at the actual radical loss. -/
theorem real_tail_weyl_action (k : ℕ) (M u : ℝ) (hF : (F:ℝ)≤u) (hu : u≤M)
    (hcap : M≤Real.sqrt (k:ℝ)/8) :
    2*(1/(14*M^2)) < ((1/7:ℝ)+1/1000)/M^2 ∧
      WeylBranch k (M/k) u (((1/7:ℝ)+1/1000)/M^2) := by
  have h120 : (120:ℝ)≤u := by simpa [F] using hF
  have hM : 0<M := by linarith
  have hM8 : 8*M≤Real.sqrt (k:ℝ) := by linarith
  have hpow := pow_le_pow_left₀ (by positivity : 0≤8*M) hM8 2
  rw [Real.sq_sqrt (Nat.cast_nonneg _)] at hpow
  have hbound : 64*M^2≤(k:ℝ) := by nlinarith
  have h := infinite_weyl_tail k (M/k) u M (by positivity) le_rfl h120 hu hbound
  constructor
  · calc
      2*(1/(14*M^2))=2/(14*M^2) := by ring
      _ < _ := h.1
  · exact h.2

#print axioms IndexedStages.extended_degree_integral
#print axioms IndexedStages.extendedDrift_attained
#print axioms IndexedStages.continuous_extendedDrift
#print axioms real_tail_weyl_action
end WaringEnvelope
