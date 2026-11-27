import WaringFieldSmall.Schedules
import WaringFieldSmall.Rounding
import WaringLinear.MarkedMinorAbsorption

/-! # The finite field schedules on the trace torus
The ED input counts literal cubic-or-higher power equalities. The field
shortening estimate is needed only for runs in the certified schedule. -/
noncomputable section
open WaringLinear WaringEnvelope MeasureTheory WaringSiegel WaringSiegel.WSL2
namespace WaringFieldSmall
variable {K : Type*} [Field K] [NumberField K]
def normalized (k d : ℕ) : ℝ := d/(scale*(k:ℝ))

/-- Only the specific finitely many single-step bounds used at the
degree and interval are requested. The defect units in this formulation
are the integers in the checker; each update rounds upward. -/
def RoundedShortening (Listed : Schedule → Prop) (W : ℝ → TraceSumFamily K) (k : ℕ) : Prop :=
  ∀ band, Listed band → band.lo≤k → k≤band.hi → ∀ u∈band.data, ∀ r d : ℕ,
    k≤r → r%2=0 → cutoffAdmissible W k r (normalized k d) →
    cutoffAdmissible W k (r+2) (normalized k (fibreRound band.hi (unpack u) d))

theorem small_field_marked_orders (Listed : Schedule → Prop) (W : ℝ → TraceSumFamily K) (k : ℕ)
    (hk : 11≤k) (witness : ∃ s : Schedule, Listed s ∧ s.lo≤k ∧ k≤s.hi ∧ s.good)
    (ed : DifferencingCounts W k) (shorten : RoundedShortening Listed W k) :
    ∃ r a : ℕ, ∃ x : ℝ, Even r ∧ Even a ∧ 0<a ∧ cutoffAdmissible W k r x ∧ 0≤x ∧
      (k:ℝ)*x<((a:ℝ)-1)*(1/(15*k)) ∧ 2*k<r+a ∧ ((r+a+1:ℕ):ℝ)/k<6873/1000 := by
  let P := fun r d => cutoffAdmissible W k r (normalized k d)
  have hp : 0<(k:ℝ) := by exact_mod_cast (show 0<k by omega)
  have hscale : (0:ℝ)<scale := by norm_num [scale]
  have hApp : ∀ band, Listed band → band.lo≤k → k≤band.hi → band.good → Applicable band k P := by
    intro band list hl hh ok
    refine ⟨?_,shorten band list hl hh⟩
    have hlo : 2≤band.lo := by
      simp only [Schedule.good,checked,Bool.and_eq_true,decide_eq_true_eq,and_assoc] at ok
      have := ok.1; omega
    have hseed := edDefect_le_start hlo hl hh band.edIndex
    intro ε hε
    obtain ⟨η,hη,data⟩ := ed band.edIndex ε hε
    refine ⟨η,hη,?_⟩
    intro t ht hT
    obtain ⟨D,hD,major⟩ := data t ht hT
    refine ⟨D,hD,?_⟩
    intro X hX
    rw [TraceSumFamily.trace_moment_eq_powerEnergy]
    apply (major X hX).trans (mul_le_mul_of_nonneg_left _ hD)
    apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hX)
    have he (n : Nat) : (k:ℝ)*normalized k n=(n:ℝ)/scale := by
      unfold normalized;field_simp
    rw [he]
    push_cast
    linarith only [hseed]
  obtain ⟨r,a,d,er,ea,ha,hP,hgap,hm,hprice⟩ := trace_schedule Listed k P witness hApp
  refine ⟨r,a,normalized k d,Nat.even_iff.mpr er,Nat.even_iff.mpr ea,ha,hP,
    div_nonneg (by positivity) (by positivity),?_,hm,?_⟩
  · have gap : (15:ℝ)*k*d<((a:ℝ)-1)*scale := by
      rw [←Nat.cast_one,←Nat.cast_sub (show 1≤a by omega)]
      exact_mod_cast hgap
    unfold normalized
    rw [mul_one_div,show (k:ℝ)*(d/(scale*(k:ℝ)))=d/scale by field_simp]
    apply (div_lt_div_iff₀ hscale (by positivity : (0:ℝ)<15*k)).2
    linarith only [gap]
  · apply (div_lt_iff₀ hp).2
    have h : (1000:ℝ)*((r+a+1:Nat):ℝ)<6873*(k:ℝ) := by exact_mod_cast hprice
    linarith only [h]

#print axioms small_field_marked_orders
end WaringFieldSmall
