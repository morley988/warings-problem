import Waring.CubicDivisorClasses
import Waring.RationalTransference
import Mathlib.NumberTheory.Divisors

/-!
# Exceptional cubic samples and the refined height denominator

Once close rational approximants have the same cross product, their reduced
denominators determine a divisor class. The actual finite sum over all
exceptional samples is bounded by `4*tau(t)*H^3/L`. This is the discrete
improvement used by the new coefficient estimate. Cross-product equality
can be obtained from `SamplingArithmetic.exceptional_rigidity`.
-/

noncomputable section
open scoped BigOperators

namespace Waring.CubicExceptionalSampling
open Waring.RationalHeight Waring.CubicDivisorClasses

def CrossMatch (r s : ℚ) (h : ℕ) : Prop :=
  r.num * (h : ℤ)^3 * (s.den : ℤ) = s.num * (r.den : ℤ)

theorem rat_isCoprime (r : ℚ) : IsCoprime r.num (r.den : ℤ) := by
  apply Int.isCoprime_iff_nat_coprime.mpr
  simpa only [Int.natAbs_natCast] using r.reduced

theorem denominator_class {r s : ℚ} {h : ℕ} (hm : CrossMatch r s h) :
    s.den ∣ r.den ∧ (r.den / s.den) ∣ h^3 := by
  have hs : (s.den : ℤ) ≠ 0 := by exact_mod_cast s.den_nz
  have H := SamplingArithmetic.exceptional_quotient_divides_cube
    (rat_isCoprime r) (rat_isCoprime s) hs hm
  constructor
  · exact_mod_cast H.1
  · exact_mod_cast H.2

theorem class_mem_divisors {r s : ℚ} {h : ℕ} (hm : CrossMatch r s h) :
    (r.den / s.den) ∈ r.den.divisors :=
  Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd (denominator_class hm).1, r.den_nz⟩

/-- Exact denominator identity for a matched reduced fraction. -/
theorem matched_sumCost {r s : ℚ} {h : ℕ} (hm : CrossMatch r s h)
    (U α : ℝ) :
    sumCost U (α*(h:ℝ)^3) s = (s.den : ℝ) *
      (1 + (U * error α r / (r.den : ℝ)) * (h : ℝ)^3) := by
  have ht : (0 : ℝ) < r.den := by exact_mod_cast r.pos
  have hc : (r.num : ℝ)*(h:ℝ)^3*(s.den:ℝ) = (s.num:ℝ)*(r.den:ℝ) := by
    exact_mod_cast hm
  have heq : (s.den:ℝ)*(α*(h:ℝ)^3)-(s.num:ℝ) =
      ((s.den:ℝ)*(h:ℝ)^3/(r.den:ℝ))*((r.den:ℝ)*α-(r.num:ℝ)) := by
    field_simp
    nlinarith [hc]
  have he : error (α*(h:ℝ)^3) s =
      ((s.den:ℝ)*(h:ℝ)^3/(r.den:ℝ))*error α r := by
    unfold error
    rw [heq, abs_mul, abs_of_nonneg (by positivity)]
  change (s.den:ℝ) + U * error (α*(h:ℝ)^3) s = _
  rw [he]
  ring

theorem matched_reciprocal {r s : ℚ} {h : ℕ} (hm : CrossMatch r s h)
    (U α : ℝ) :
    1 / sumCost U (α*(h:ℝ)^3) s =
      ((r.den / s.den : ℕ):ℝ) / (r.den:ℝ) *
        (1 / (1 + (U * error α r / (r.den:ℝ)) * (h:ℝ)^3)) := by
  have hd := (denominator_class hm).1
  have ht : (r.den:ℝ) ≠ 0 := by exact_mod_cast r.den_nz
  have hs : (s.den:ℝ) ≠ 0 := by exact_mod_cast s.den_nz
  have hprod : ((r.den / s.den : ℕ):ℝ) * (s.den:ℝ) = (r.den:ℝ) := by
    exact_mod_cast Nat.div_mul_cancel hd
  have hinv : 1 / (s.den:ℝ) = ((r.den / s.den : ℕ):ℝ)/(r.den:ℝ) := by
    apply (div_eq_div_iff hs ht).mpr
    simpa using hprod.symm
  rw [matched_sumCost hm U α, ← one_div_mul_one_div, hinv]

/-- Actual finite exceptional sum, grouped into reduced-denominator divisor
classes. The divisor-count factor is explicit. -/
theorem exceptional_reciprocal_sum (S : Finset ℕ) (H : ℕ) (r : ℚ) (s : ℕ → ℚ)
    {U α : ℝ} (hU : 0 ≤ U) (hS : S ⊆ Finset.Icc 1 H)
    (hmatch : ∀ h ∈ S, CrossMatch r (s h) h) :
    (∑ h ∈ S, 1 / sumCost U (α*(h:ℝ)^3) (s h)) ≤
      4 * (r.den.divisors.card : ℝ) * (H:ℝ)^3 /
        sumCost ((H:ℝ)^3*U) α r := by
  classical
  let A := U * error α r / (r.den:ℝ)
  have ht : (0:ℝ) < r.den := by exact_mod_cast r.pos
  have hA : 0 ≤ A := by dsimp [A]; exact div_nonneg (mul_nonneg hU (error_nonneg α r)) ht.le
  let weight : ℕ → ℕ → ℝ := fun d h =>
    if d ∣ h^3 then (d:ℝ)/(r.den:ℝ) * (1/(1+A*(h:ℝ)^3)) else 0
  have hw (d h : ℕ) : 0 ≤ weight d h := by dsimp [weight]; split_ifs <;> positivity
  have hsingle (h : ℕ) (hh : h ∈ S) :
      1 / sumCost U (α*(h:ℝ)^3) (s h) ≤ ∑ d ∈ r.den.divisors, weight d h := by
    have hm := hmatch h hh
    have hdmem := class_mem_divisors hm
    have hdcube := (denominator_class hm).2
    have hh := Finset.single_le_sum (fun d _ => hw d h) hdmem
    simpa only [weight, if_pos hdcube, matched_reciprocal hm U α, A] using hh
  have hgroup (d : ℕ) :
      (∑ h ∈ Finset.Icc 1 H, weight d h) = originalClassContribution H d A (r.den:ℝ) := by
    unfold originalClassContribution
    dsimp [weight]
    rw [← Finset.sum_filter, Finset.mul_sum]
  have hden : (r.den:ℝ)+A*(H:ℝ)^3*(r.den:ℝ) = sumCost ((H:ℝ)^3*U) α r := by
    unfold sumCost
    dsimp [A, error]
    field_simp
  calc
    (∑ h ∈ S, 1 / sumCost U (α*(h:ℝ)^3) (s h)) ≤
        ∑ h ∈ S, ∑ d ∈ r.den.divisors, weight d h := Finset.sum_le_sum hsingle
    _ ≤ ∑ h ∈ Finset.Icc 1 H, ∑ d ∈ r.den.divisors, weight d h :=
      Finset.sum_le_sum_of_subset_of_nonneg hS (fun h _ _ => Finset.sum_nonneg (fun d _ => hw d h))
    _ = ∑ d ∈ r.den.divisors, originalClassContribution H d A (r.den:ℝ) := by
      rw [Finset.sum_comm]
      simp_rw [hgroup]
    _ ≤ ∑ d ∈ r.den.divisors,
        4*(H:ℝ)^3/((r.den:ℝ)+A*(H:ℝ)^3*(r.den:ℝ)) := by
      apply Finset.sum_le_sum
      intro d hd
      have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
      exact originalClassContribution_height_bound hdpos hA ht
    _ = 4 * (r.den.divisors.card : ℝ) * (H:ℝ)^3 / sumCost ((H:ℝ)^3*U) α r := by
      rw [hden]
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring

#print axioms matched_reciprocal
#print axioms exceptional_reciprocal_sum

end Waring.CubicExceptionalSampling
