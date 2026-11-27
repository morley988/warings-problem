import WaringSiegel.WSL2MomentDifferencing
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Positivity

/-! # Arithmetic van der Corput averaging with an arbitrary lattice of shifts

The support and the enlarged box are arbitrary finite sets. The right
side sums the genuine shifted correlations, so this applies to masks,
initial intervals, and a line or a number-field lattice without a
period-sized enclosing group.
-/
noncomputable section
open scoped BigOperators ComplexConjugate Classical
open WaringSiegel.WSL2
namespace WaringLinear
variable {G V : Type*} [AddCommGroup G] [AddCommGroup V] [DecidableEq G]

private theorem translated_support_sum (X Ω : Finset G) (a : G) (u : G→ℂ)
    (hx : ∀x∉X,u x=0) (hc : ∀x∈X,x-a∈Ω) :
    ∑ x∈Ω,u (x+a)=∑ x∈X,u x := by
  classical
  let D := Ω.image (fun x => x+a)
  have hd : X⊆D := by
    intro x hm
    exact Finset.mem_image.mpr ⟨x-a,hc x hm,sub_add_cancel x a⟩
  calc
    _ = ∑ x∈D,u x := (Finset.sum_image (fun x _ y _ h => add_right_cancel h)).symm
    _ = _ := (Finset.sum_subset hd (fun x _ hn => hx x hn)).symm

/-- For one shift box S, its differences H and an enlarged support Ω.
Cardinality factors are explicit and no positivity or boundedness of the
coefficients is required. -/
theorem shift_average_sq (X Ω : Finset G) (S H : Finset V) (φ : V→+G)
    (f : G→ℂ) (hsupp : ∀x∉X,f x=0) (hS : S.Nonempty)
    (hcov : ∀s∈S,∀x∈X,x-φ s∈Ω)
    (hdiff : ∀s∈S,∀t∈S,s-t∈H) :
    (S.card:ℝ)*‖∑x∈X,f x‖^2 ≤ (Ω.card:ℝ)*
      ∑h∈H,‖∑ x∈X,f (x+φ h)*conj (f x)‖ := by
  classical
  let A (x:G) := ∑s∈S,f (x+φ s)
  let C (h:V) := ∑x∈X,f (x+φ h)*conj (f x)
  have ha : (∑x∈Ω,A x)=(S.card:ℂ)*(∑x∈X,f x) := by
    unfold A
    rw [Finset.sum_comm]
    calc
      _ = ∑ _s∈S,∑x∈X,f x := Finset.sum_congr rfl (fun s hs =>
        translated_support_sum X Ω (φ s) f hsupp (hcov s hs))
      _ = _ := by simp
  have hf (h s : V) (hs : s∈S) :
      (∑x∈Ω, f (x+φ (s+h))*conj (f (x+φ s)))=C h := by
    have hv := translated_support_sum X Ω (φ s) (fun x => f (x+φ h)*conj (f x))
      (fun x hx => by simp [hsupp x hx]) (hcov s hs)
    simpa only [map_add,add_assoc,C] using hv
  have hcomplex : ((∑x∈Ω,‖A x‖^2:ℝ):ℂ)=
      ∑h∈H,((additiveOverlap S h).card:ℂ)*C h := by
    rw [Complex.ofReal_sum]
    calc
      _ = ∑x∈Ω,∑h∈H,∑s∈additiveOverlap S h,
          f (x+φ (s+h))*conj (f (x+φ s)) := by
        apply Finset.sum_congr rfl
        intro x _
        exact finite_sum_norm_sq_autocorrelations S H hdiff (fun s => f (x+φ s))
      _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro h _
        rw [Finset.sum_comm]
        calc
          _ = ∑ _s∈additiveOverlap S h,C h := Finset.sum_congr rfl (fun s hs =>
            hf h s (additiveOverlap_subset S h hs))
          _ = _ := by simp
  have mass : (∑x∈Ω,‖A x‖^2) ≤ (S.card:ℝ)*∑h∈H,‖C h‖ := by
    have hh := norm_sum_le H (fun h => ((additiveOverlap S h).card:ℂ)*C h)
    rw [←hcomplex,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _))] at hh
    apply hh.trans
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro h _
    simp only [norm_mul,Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_card (additiveOverlap_subset S h)) (norm_nonneg _)
  have cs := (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le Ω A) 2).trans
    (sq_sum_le_card_mul_sum_sq (s := Ω) (f := fun x => ‖A x‖))
  rw [ha,norm_mul,Complex.norm_natCast,mul_pow] at cs
  have comb := cs.trans (mul_le_mul_of_nonneg_left mass (Nat.cast_nonneg _))
  have pos : 0<(S.card:ℝ) := by exact_mod_cast Finset.card_pos.mpr hS
  apply le_of_mul_le_mul_left _ pos
  simpa only [pow_two,mul_assoc,mul_left_comm,mul_comm,C] using comb

#print axioms shift_average_sq
end WaringLinear
