import WaringLinear.MarkedArc
import Mathlib.Data.ZMod.Basic

/-! # Rational complete sums in the marked major-arc estimate -/

noncomputable section
open MeasureTheory Finset
open scoped BigOperators Interval
namespace WaringLinear

theorem zmod_full_period {q : ℕ} [NeZero q] (f : ZMod q → ℂ) :
    (∑ n∈range q,f n)=∑ x : ZMod q,f x := by
  rw [←Fin.sum_univ_eq_sum_range]
  convert (ZMod.finEquiv q).toEquiv.sum_comp f using 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  cases q with
  | zero => exact False.elim (NeZero.ne 0 rfl)
  | succ q => exact Fin.cast_val_eq_self _

/-- A true complete rational factor times a common archimedean integral,
with no periodicity or complete-mean assumptions. Take f to be any
additive character of Z/qZ composed with multiplication by the numerator. -/
theorem zmod_marked_arc {ι : Type*} (D : Finset ι) (q k : ℕ) [NeZero q]
    (d : ι → ℕ) (N : ι → ℕ) (u : ι → (ZMod q)ˣ)
    (hd : ∀ i∈D, 0<d i) (hu : ∀ i∈D,(u i : ZMod q)=(d i : ZMod q))
    (f : ZMod q → ℂ) (hf : ∀ x, ‖f x‖≤1)
    (c P : ℝ) (hlo : ∀ i∈D, (d i:ℝ)*N i≤P)
    (hhi : ∀ i∈D, P≤(d i:ℝ)*(N i+1)) :
    let a := (∑ x : ZMod q, f (x^k))/(q:ℂ)
    ‖(∑ i∈D, ∑ n∈range (N i),
       monomialWeight (c*(d i:ℝ)^k) k n*f (((d i:ZMod q)*(n:ZMod q))^k)) -
      a*((∑ i∈D,(d i:ℝ)⁻¹) • ∫ x in (0:ℝ)..P, monomialWeight c k x)‖ ≤
      (D.card:ℝ)*(2*(q:ℝ)*(1+2*|c| *P^k)+2*|c| *P^k+1) := by
  intro a
  have hq : 0<q := Nat.pos_of_ne_zero (NeZero.ne q)
  have qC : (q:ℂ)≠0 := Nat.cast_ne_zero.mpr hq.ne'
  have qR : 0<(q:ℝ) := by exact_mod_cast hq
  have hsum : ‖∑ x : ZMod q,f (x^k)‖ ≤ (q:ℝ) := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _x : ZMod q,(1:ℝ) := Finset.sum_le_sum (fun x _ => hf _)
      _ = _ := by simp [ZMod.card]
  have ha : ‖a‖≤1 := by
    simp only [a,norm_div,Complex.norm_natCast]
    exact (div_le_one qR).mpr hsum
  apply marked_support_arc_approximation D _ _ N q k hq a c P ha
  · intro i hi; exact_mod_cast hd i hi
  · exact hlo
  · exact hhi
  · intro i hi n; exact hf _
  · intro i hi n; simp
  · intro i hi
    rw [zmod_full_period (f := fun n : ZMod q => f (((d i:ZMod q)*n)^k)),←hu i hi,
      complete_unit_dilation (u i) f k]
    dsimp [a]
    field_simp

#print axioms zmod_marked_arc
end WaringLinear
