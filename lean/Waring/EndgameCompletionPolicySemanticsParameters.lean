import Waring.EndgameCompletionPolicySemanticsLookups
import Waring.PolicyCompletionMajorSourceBound

/-! # Exact real parameters of the frozen policy formulas -/

noncomputable section
open scoped BigOperators
namespace Waring.Certificate
open PolicyCompletionMajorPowerRanges PolicyCompletionMajorSourceBound

def phiReal (p : Policy) (i : Fin p.phi.size) : ℝ := (p.phi[i.val]! : ℝ)

theorem sumQ_eq_fin_sum (xs : Array Q) : sumQ xs=∑ i : Fin xs.size,xs[i.val]! := by
  unfold sumQ
  rw [← List.sum_eq_foldl]
  have he : List.ofFn (fun i : Fin xs.size => xs[i.val]!)=xs.toList := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp only [List.getElem_ofFn,Array.getElem_toList]
      exact getElem!_pos xs i (by simpa using hj)
  rw [← he,Fin.sum_ofFn]

theorem sumQ_cast_eq_total (p : Policy) : (sumQ p.phi : ℝ)=total (phiReal p) := by
  rw [sumQ_eq_fin_sum]
  simp only [Rat.cast_sum,total,phiReal]

theorem phiReal_pos {k : ℕ} {p : Policy} (hguard : PolicyAnalyticGuards k p)
    (i : Fin p.phi.size) : 0<phiReal p i := by
  have hi : p.phi[i.val]! ∈ p.phi.toList := by
    rw [getElem!_pos p.phi i.val i.isLt]
    exact Array.mem_toList_iff.mpr (Array.getElem_mem i.isLt)
  unfold phiReal
  exact_mod_cast (hguard.2.2.1 _ hi).1

theorem phiReal_lt_reciprocal {k : ℕ} {p : Policy} (hguard : PolicyAnalyticGuards k p)
    (i : Fin p.phi.size) : phiReal p i<1/(k : ℝ) := by
  have hi : p.phi[i.val]! ∈ p.phi.toList := by
    rw [getElem!_pos p.phi i.val i.isLt]
    exact Array.mem_toList_iff.mpr (Array.getElem_mem i.isLt)
  have H := (hguard.2.2.1 _ hi).2
  change p.phi[i.val]! < 1/(k : Q) at H
  unfold phiReal
  simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_natCast] using
    (Rat.cast_lt (K := ℝ)).mpr H

theorem phiReal_shift_pos {k : ℕ} {p : Policy} (hk : 0<k)
    (hguard : PolicyAnalyticGuards k p) (i : Fin p.phi.size) :
    0<shiftExponents k (phiReal p) i := by
  have hkR : 0<(k : ℝ) := by exact_mod_cast hk
  have H := (lt_div_iff₀ hkR).mp (phiReal_lt_reciprocal hguard i)
  unfold shiftExponents
  nlinarith

def terminalHalfOrder (p : Policy) : ℕ := p.path[p.phi.size-1]!
def terminalFullOrder (p : Policy) : ℕ := p.auxiliaryOrder.getD (2*terminalHalfOrder p)
def terminalWeightQ (p : Policy) : Q :=
  if p.auxiliaryOrder.isSome then q (2*terminalHalfOrder p)/q (terminalFullOrder p) else 1
def terminalWeightReal (p : Policy) : ℝ :=
  if p.auxiliaryOrder.isSome then ((2*terminalHalfOrder p : ℕ) : ℝ)/(terminalFullOrder p : ℝ) else 1
def terminalAmplitudeQ (k : ℕ) (p : Policy) : Q :=
  1+(q p.phi.size-q k*sumQ p.phi)+sumQ p.phi

theorem terminalWeightQ_cast (p : Policy) :
    (terminalWeightQ p : ℝ)=terminalWeightReal p := by
  unfold terminalWeightQ terminalWeightReal
  split_ifs <;> norm_num [q]

theorem terminalAmplitudeQ_cast (k : ℕ) (p : Policy) :
    (terminalAmplitudeQ k p : ℝ)=amplitude k (phiReal p) := by
  simp only [terminalAmplitudeQ,q,Rat.cast_add,Rat.cast_sub,Rat.cast_mul,
    Rat.cast_one,Rat.cast_natCast,sumQ_cast_eq_total,amplitude]
  ring

theorem terminalParameters_top_cast (k : ℕ) (curve : Curve) (p : Policy) :
    ((terminalParameters k curve p).top : ℝ)=
      (k : ℝ)/2*(1-total (phiReal p)) := by
  simp only [terminalParameters,q,Rat.cast_mul,Rat.cast_div,Rat.cast_natCast,
    Rat.cast_ofNat,Rat.cast_sub,Rat.cast_one,sumQ_cast_eq_total]

theorem terminalParameters_base_cast (k : ℕ) (curve : Curve) (p : Policy) :
    ((terminalParameters k curve p).base : ℝ)=
      ((1-2*(1-terminalWeightReal p))+(1-terminalWeightReal p))*amplitude k (phiReal p)+
        terminalWeightReal p*((terminalFullOrder p : ℝ)-(k : ℝ))*(1-total (phiReal p)) := by
  change ((((1-2*(1-terminalWeightQ p))+(1-terminalWeightQ p))*terminalAmplitudeQ k p+
    terminalWeightQ p*(q (terminalFullOrder p)-q k)*(1-sumQ p.phi) : Q) : ℝ) = _
  push_cast
  rw [terminalWeightQ_cast,terminalAmplitudeQ_cast,sumQ_cast_eq_total]
  simp only [q,Rat.cast_natCast]

theorem terminalParameters_slope_cast (k : ℕ) (curve : Curve) (p : Policy) :
    ((terminalParameters k curve p).slope : ℝ)=
      2/(k : ℝ)*terminalWeightReal p*((delta k curve (terminalFullOrder p)).getD 0 : ℝ) := by
  change ((2/q k*terminalWeightQ p*(delta k curve (terminalFullOrder p)).getD 0 : Q) : ℝ)=_
  simp only [Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat,q,Rat.cast_natCast,terminalWeightQ_cast]

theorem terminalParameters_scale_cast (k : ℕ) (curve : Curve) (p : Policy) :
    ((terminalParameters k curve p).scale : ℝ)=
      (1-2*(1-terminalWeightReal p))/(2 : ℝ)^(k-p.phi.size-2) := by
  change (((1-2*(1-terminalWeightQ p))*(1/q (2^(k-p.phi.size-2))) : Q) : ℝ)=_
  simp only [Rat.cast_mul,Rat.cast_sub,Rat.cast_one,Rat.cast_ofNat,Rat.cast_div,
    q,Rat.cast_natCast,Nat.cast_pow,Nat.cast_ofNat,Rat.cast_pow,terminalWeightQ_cast]
  ring

def terminalMajorFormula (k : ℕ) (curve : Curve) (p : Policy) : Q :=
  terminalAmplitudeQ k p+(q (2*terminalHalfOrder p)-q k)*(1-sumQ p.phi)+
    qmax 0 (2/q k*(delta k curve (2*terminalHalfOrder p)).getD 0-1/q (k-p.phi.size))

theorem terminalMajorFormula_cast (k : ℕ) (curve : Curve) (p : Policy) :
    (terminalMajorFormula k curve p : ℝ)=
      majorSourceExponent k (terminalHalfOrder p) (phiReal p)
        ((delta k curve (2*terminalHalfOrder p)).getD 0 : ℝ) := by
  simp only [terminalMajorFormula,Rat.cast_add,Rat.cast_sub,Rat.cast_mul,Rat.cast_div,
    Rat.cast_zero,Rat.cast_one,Rat.cast_ofNat,q,Rat.cast_natCast,cast_qmax,
    terminalAmplitudeQ_cast,sumQ_cast_eq_total,majorSourceExponent]
  congr 1 <;> ring

#print axioms sumQ_cast_eq_total
#print axioms terminalParameters_base_cast
#print axioms terminalMajorFormula_cast
end Waring.Certificate
