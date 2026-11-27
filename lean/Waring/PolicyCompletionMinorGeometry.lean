import Waring.PolicyCompletionMinorRanges
import Waring.PolicyCompletionMajorIntegral
import Waring.EndgameCompletionPolicySemanticsParameters
import Waring.PolicyCompletionTerminalShape

/-! # Actual minor-domain measure and exact nonauxiliary terminal parameters -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace Waring.PolicyCompletionMinorGeometry
open Certificate SmoothMoments RationalHeight AuxiliaryMajorArcs AuxiliaryMinorHeights
open PolicyCompletionMajorBoxRanges PolicyCompletionMajorIntegral PolicyCompletionMajorPowerRanges
open PolicyCompletionTerminalShape PolicyCompletionMinorRanges

def boxMinorSet {j : ℕ} (k : ℕ) (L R : ℝ) (M : Fin j→ℝ) : Set ℝ :=
  Set.Ioc 0 1 ∩ {α | ¬MajorAtCutoff L ((boxConductor k L M/L)*R^(k*(k-j))) α}

def boxMinorIntegral {j : ℕ} (k s : ℕ) (L Q R : ℝ) (M : Fin j→ℝ) : ℝ :=
  ∫ α in boxMinorSet k L R M,
    ‖boxSourceFamily k L Q R M α‖*‖smoothWeyl k (boxSmoothLength L M) R α‖^(2*s)

def boxTerminalIntegral {j : ℕ} (k s : ℕ) (L Q R : ℝ) (M : Fin j→ℝ) : ℝ :=
  ∫ α in Set.Ioc 0 1,
    ‖boxSourceFamily k L Q R M α‖*‖smoothWeyl k (boxSmoothLength L M) R α‖^(2*s)

theorem boxMinorSet_measurable {j : ℕ} (k : ℕ) (L R : ℝ) (M : Fin j→ℝ) :
    MeasurableSet (boxMinorSet k L R M) :=
  measurableSet_Ioc.inter (measurableSet_major _ _).compl

theorem boxMinorIntegral_lintegral {j : ℕ} (k s : ℕ) (L Q R : ℝ) (M : Fin j→ℝ) :
    ENNReal.ofReal (boxMinorIntegral k s L Q R M)=
      ∫⁻ α,ENNReal.ofReal ‖boxSourceFamily k L Q R M α‖*
        ENNReal.ofReal (‖smoothWeyl k (boxSmoothLength L M) R α‖^(2*s))
          ∂(volume.restrict (boxMinorSet k L R M)) := by
  have hi : IntegrableOn (fun α=>‖boxSourceFamily k L Q R M α‖*
      ‖smoothWeyl k (boxSmoothLength L M) R α‖^(2*s)) (Set.Ioc (0:ℝ) 1) :=
    ((continuous_boxSourceFamily k L Q R M).norm.mul
      ((continuous_smoothWeyl k (boxSmoothLength L M) R).norm.pow (2*s))).integrableOn_Ioc
  have hb := ofReal_integral_eq_lintegral_ofReal
    (hi.mono_set (show boxMinorSet k L R M⊆Set.Ioc (0:ℝ) 1 from Set.inter_subset_left))
    (Filter.Eventually.of_forall (fun α=>mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) (2*s))))
  simpa only [boxMinorIntegral,ENNReal.ofReal_mul (norm_nonneg _)] using hb

theorem terminal_integral_split {j : ℕ} (k s : ℕ) (L Q R : ℝ) (M : Fin j→ℝ) :
    boxTerminalIntegral k s L Q R M=
      boxMajorIntegral k s L Q R M+boxMinorIntegral k s L Q R M := by
  let f := fun α=>‖boxSourceFamily k L Q R M α‖*‖smoothWeyl k (boxSmoothLength L M) R α‖^(2*s)
  have hi : IntegrableOn f (Set.Ioc (0:ℝ) 1) :=
    ((continuous_boxSourceFamily k L Q R M).norm.mul
      ((continuous_smoothWeyl k (boxSmoothLength L M) R).norm.pow (2*s))).integrableOn_Ioc
  have hd : Disjoint (boxMajorSet k L R M) (boxMinorSet k L R M) := by
    apply Set.disjoint_left.mpr
    intro α hα hβ
    exact hβ.2 hα.2
  have hu : boxMajorSet k L R M∪boxMinorSet k L R M=Set.Ioc 0 1 := by
    ext α
    simp only [boxMajorSet,boxMinorSet,Set.mem_union,Set.mem_inter_iff,Set.mem_setOf_eq]
    tauto
  have hh := setIntegral_union hd (boxMinorSet_measurable k L R M)
    (hi.mono_set Set.inter_subset_left) (hi.mono_set Set.inter_subset_left)
  rw [hu] at hh
  exact hh

theorem nonauxiliary_parameters (k : ℕ) (curve : Curve) (p : Policy) (s : Shape)
    (hdim : p.phi.size+extra s+2=k) (haux : p.auxiliaryOrder=none) :
    ((terminalParameters k curve p).base:ℝ)=amplitude k (phiReal p)+
      ((((2*terminalHalfOrder p:ℕ):ℝ)-(k:ℝ))*(1-total (phiReal p))) ∧
    ((terminalParameters k curve p).slope:ℝ)=
      2*((delta k curve (2*terminalHalfOrder p)).getD 0:ℝ)/(k:ℝ) ∧
    ((terminalParameters k curve p).scale:ℝ)=1/root s := by
  have hw : terminalWeightReal p=1 := by simp [terminalWeightReal,haux]
  have ho : terminalFullOrder p=2*terminalHalfOrder p := by simp [terminalFullOrder,haux]
  have hx : k-p.phi.size-2=extra s := by omega
  rw [terminalParameters_base_cast,terminalParameters_slope_cast,terminalParameters_scale_cast,hw,ho,hx]
  constructor
  · ring
  constructor
  · ring
  · cases s <;> norm_num [extra,root]

theorem normalizedHeight_nonneg {P : ℝ} (hP : 1<P) (V α : ℝ) :
    0≤normalizedHeight P V α :=
  div_nonneg (Real.log_nonneg (one_le_height V α)) (Real.log_pos hP).le

/-- At the power cutoff, the fixed dilation costs one additional small
smoothness exponent in the actual resource height threshold. -/
theorem source_minor_height_power {k j : ℕ} (hk : 1≤k) {D P η : ℝ}
    (hD : 1≤D) (hP : 1<P) (hη : 0≤η) (φ : Fin j→ℝ) (hφ : ∀i,0≤φ i)
    (hscale : D^k/D≤P^η) {α : ℝ}
    (hminor : α∈boxMinorSet k (D*P) (P^η) (fun i=>P^(φ i))) :
    P/(P^η)^((((k*(k-j):ℕ):ℝ)+1))≤height (P^((k:ℝ)*(1-total φ))) α := by
  have hPp : 0<P := zero_lt_one.trans hP
  have hR : 1≤P^η := Real.one_le_rpow hP.le hη
  have hDp : 0<D := zero_lt_one.trans_le hD
  have hc : 1≤D^k/D := by
    apply (le_div_iff₀ hDp).mpr
    simpa only [one_mul,pow_one] using pow_le_pow_right₀ hD hk
  have hm := source_minor_at_base hk hD hPp φ hφ
    (show ¬MajorAtCutoff (D*P)
      ((boxConductor k (D*P) (fun i=>P^(φ i))/(D*P))*(P^η)^(((k*(k-j):ℕ):ℝ))) α by
      simpa only [Real.rpow_natCast] using hminor.2)
  have hh := minor_height_lower_scaled hPp (Real.rpow_pos_of_pos hPp _) hR
    (Nat.cast_nonneg (k*(k-j))) hc hm
  apply le_trans _ hh.le
  apply div_le_div_of_nonneg_left hPp.le (by positivity)
  rw [Real.rpow_add (zero_lt_one.trans_le hR),Real.rpow_one]
  nlinarith [Real.rpow_nonneg (zero_le_one.trans hR) (((k*(k-j):ℕ):ℝ))]

#print axioms terminal_integral_split
#print axioms source_minor_height_power
end Waring.PolicyCompletionMinorGeometry
