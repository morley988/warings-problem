import Waring.RestrictedSmoothCommutation
import Waring.EndgameCompletionCoefficients
import Mathlib.Algebra.Ring.Periodic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Exact scaling of reduced-residue arc integrals

Multiplication by an integer coprime to q permutes its reduced residues.
Periodicity and the exact interval substitution retain the original
Jacobian and enlarged arc width.
-/

noncomputable section
open scoped BigOperators
namespace Waring.RestrictedSmoothArcs
open Waring.EndgameCompletion

theorem periodic_mod_fraction {F : ℝ → ℝ} (hF : Function.Periodic F 1)
    (n q : ℕ) (hq : 0 < q) (x : ℝ) :
    F ((n : ℝ)/(q : ℝ)+x) = F (((n%q : ℕ) : ℝ)/(q : ℝ)+x) := by
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hn : ((n%q : ℕ) : ℝ)+(q : ℝ)*(n/q : ℕ)=n := by
    exact_mod_cast Nat.mod_add_div n q
  have he : (n : ℝ)/(q : ℝ)+x =
      ((n%q : ℕ) : ℝ)/(q : ℝ)+x+(n/q : ℕ) := by
    field_simp
    nlinarith
  rw [he]
  simpa only [mul_one] using (hF.nat_mul (n/q)) (((n%q : ℕ) : ℝ)/(q : ℝ)+x)

def rationalArcSum (q : ℕ) [NeZero q] (F : ℝ → ℝ) (δ : ℝ) : ℝ :=
  ∑ a : (ZMod q)ˣ, ∫ β in -(δ/(q : ℝ))..δ/(q : ℝ),
    F ((((a : ZMod q).val : ℕ) : ℝ)/(q : ℝ)+β)

theorem unit_mul_representative {q : ℕ} [NeZero q] (c : ℕ) (hcq : c.Coprime q)
    (a : (ZMod q)ˣ) :
    ((a*ZMod.unitOfCoprime c hcq : (ZMod q)ˣ) : ZMod q).val =
      ((a : ZMod q).val*c)%q := by
  rw [Units.val_mul,ZMod.coe_unitOfCoprime,ZMod.val_mul,ZMod.val_natCast]
  exact Nat.mul_mod_mod _ _ _

theorem rationalArcSum_mul_nat (q : ℕ) [NeZero q] {F : ℝ → ℝ}
    (hF : Function.Periodic F 1) (c : ℕ) (hc : 0 < c) (hcq : c.Coprime q) (δ : ℝ) :
    rationalArcSum q (fun x => F ((c : ℝ)*x)) δ =
      (c : ℝ)⁻¹*rationalArcSum q F ((c : ℝ)*δ) := by
  have hq : 0 < q := NeZero.pos q
  have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
  let u : (ZMod q)ˣ := ZMod.unitOfCoprime c hcq
  have hpoint (a : (ZMod q)ˣ) (β : ℝ) :
      F ((c : ℝ)*(((a : ZMod q).val : ℝ)/(q : ℝ)+β)) =
      F ((((a*u : (ZMod q)ˣ) : ZMod q).val : ℝ)/(q : ℝ)+(c : ℝ)*β) := by
    calc
      _ = F ((((a : ZMod q).val*c : ℕ) : ℝ)/(q : ℝ)+(c : ℝ)*β) := by
        congr 1
        push_cast
        ring
      _ = F (((((a : ZMod q).val*c)%q : ℕ) : ℝ)/(q : ℝ)+(c : ℝ)*β) :=
        periodic_mod_fraction hF _ q hq _
      _ = _ := by rw [unit_mul_representative]
  have hint (a : (ZMod q)ˣ) :
      (∫ β in -(δ/(q : ℝ))..δ/(q : ℝ),
        F ((c : ℝ)*(((a : ZMod q).val : ℝ)/(q : ℝ)+β))) =
      (c : ℝ)⁻¹*(∫ γ in -((c : ℝ)*δ/(q : ℝ))..((c : ℝ)*δ/(q : ℝ)),
        F ((((a*u : (ZMod q)ˣ) : ZMod q).val : ℝ)/(q : ℝ)+γ)) := by
    simp_rw [hpoint]
    have h := intervalIntegral.integral_comp_mul_left
      (fun γ => F ((((a*u : (ZMod q)ˣ) : ZMod q).val : ℝ)/(q : ℝ)+γ))
      (a := -(δ/(q : ℝ))) (b := δ/(q : ℝ)) hcR
    simpa only [smul_eq_mul,mul_neg,mul_div_assoc] using h
  unfold rationalArcSum
  simp_rw [hint]
  rw [← Finset.mul_sum]
  congr 1
  exact sum_units_mul_right u (fun a =>
    ∫ γ in -((c : ℝ)*δ/(q : ℝ))..((c : ℝ)*δ/(q : ℝ)),
      F (((a : ZMod q).val : ℝ)/(q : ℝ)+γ))

#print axioms rationalArcSum_mul_nat
end Waring.RestrictedSmoothArcs
