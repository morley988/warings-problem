import Waring.CertificateBoundaryRecurrence
import Waring.CertificateInterpolation

/-! # Actual analytic meanings of successful certificate moment lookups

No default value is accepted as a moment. An even order and an in-range
index, or an actual successful Option lookup, provide the exact admissible
exponent. The evaluator's nonnegative excess is justified by monotonicity.
-/

noncomputable section
namespace Waring.Certificate
open SmoothMoments

def MomentAvailable (curve : Curve) (p : ℕ) : Prop :=
  p % 2=0 ∧ p/2<curve.size

instance (curve : Curve) (p : ℕ) : Decidable (MomentAvailable curve p) := by
  unfold MomentAvailable
  infer_instance

theorem moment_eq_some_of_available {curve : Curve} {p : ℕ}
    (h : MomentAvailable curve p) : moment curve p=some curve[p/2]! := by
  simp [moment,h.1,h.2]

theorem moment_available_of_eq_some {curve : Curve} {p : ℕ} {value : Q}
    (h : moment curve p=some value) : MomentAvailable curve p := by
  by_cases hp : p%2=0
  · refine ⟨hp,?_⟩
    by_contra hi
    simp [moment,hp,hi] at h
  · simp [moment,hp] at h

theorem moment_getD_eq_of_available {curve : Curve} {p : ℕ}
    (h : MomentAvailable curve p) : (moment curve p).getD 0=curve[p/2]! := by
  rw [moment_eq_some_of_available h]
  rfl

theorem moment_getD_admissible {k p : ℕ} {curve : Curve}
    (hcurve : AdmissibleCurve k curve) (h : MomentAvailable curve p) :
    AdmissibleExponent k p ((moment curve p).getD 0 : ℝ) := by
  have hp : 2*(p/2)=p := by have hh := h.1; omega
  rw [moment_getD_eq_of_available h]
  simpa only [hp] using hcurve (p/2) h.2

theorem moment_admissible_of_eq_some {k p : ℕ} {curve : Curve} {value : Q}
    (hcurve : AdmissibleCurve k curve) (h : moment curve p=some value) :
    AdmissibleExponent k p (value : ℝ) := by
  have H := moment_getD_admissible hcurve (moment_available_of_eq_some h)
  simpa only [h,Option.getD_some] using H

theorem delta_getD_eq_of_available {k p : ℕ} {curve : Curve}
    (h : MomentAvailable curve p) :
    (delta k curve p).getD 0=qmax 0 ((moment curve p).getD 0-q p+q k) := by
  simp [delta,moment_eq_some_of_available h]

theorem delta_getD_nonneg {k p : ℕ} {curve : Curve}
    (h : MomentAvailable curve p) : 0≤((delta k curve p).getD 0 : ℝ) := by
  rw [delta_getD_eq_of_available h,cast_qmax]
  simpa only [Rat.cast_zero] using le_max_left (0 : ℝ)
    (((moment curve p).getD 0-q p+q k : Q) : ℝ)

theorem delta_getD_admissible {k p : ℕ} {curve : Curve}
    (hcurve : AdmissibleCurve k curve) (h : MomentAvailable curve p) :
    AdmissibleExcess k p ((delta k curve p).getD 0 : ℝ) := by
  apply admissibleExponent_mono (moment_getD_admissible hcurve h)
  rw [delta_getD_eq_of_available h,cast_qmax]
  simp only [Rat.cast_sub,Rat.cast_add,Rat.cast_zero,q,Rat.cast_natCast]
  have hm := le_max_right (0 : ℝ) (((moment curve p).getD 0 : ℝ)-(p : ℝ)+(k : ℝ))
  linarith

theorem delta_admissible_of_eq_some {k p : ℕ} {curve : Curve} {value : Q}
    (hcurve : AdmissibleCurve k curve) (h : delta k curve p=some value) :
    AdmissibleExcess k p (value : ℝ) ∧ 0≤(value : ℝ) := by
  have hm : MomentAvailable curve p := by
    unfold delta at h
    cases he : moment curve p with
    | none => simp [he] at h
    | some v => exact moment_available_of_eq_some he
  have ha := delta_getD_admissible hcurve hm
  have hn := delta_getD_nonneg (k := k) hm
  simpa only [h,Option.getD_some] using And.intro ha hn

#print axioms moment_admissible_of_eq_some
#print axioms delta_admissible_of_eq_some
end Waring.Certificate
