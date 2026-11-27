import Waring.FirstDifferenceSecond

/-!
# Divisor-controlled fibers and the actual first-difference second moment

The only size condition in the intermediate uniform estimate is an explicit
polynomial bound on the integer frequencies. The following source-box module
will discharge it for the literal first centered differences.
-/

noncomputable section
open scoped BigOperators
namespace Waring.FirstDifferenceSecond
open AuxiliaryL2Grouping

abbrev Index := ℕ × ℕ × ℕ

def indexPhase (d : ℕ) (x : Index) : ℤ := (evenPhase d x.1 x.2.1 x.2.2 : ℤ)
def heightCenter (x : Index) : Fin 2 → ℕ := ![x.1,x.2.2]

theorem indexPhase_ne_zero {d : ℕ} (hd : 2 ≤ d) (x : Index)
    (hh : 0 < x.1) (hz : 0 < x.2.2) : indexPhase d x ≠ 0 := by
  have hp := evenPhase_pos (m := x.2.1) (by omega : 0 < d) hh hz
  unfold indexPhase
  exact_mod_cast hp.ne'

theorem heightCenter_dvd (d : ℕ) (x : Index) (i : Fin 2) :
    (heightCenter x i : ℤ) ∣ indexPhase d x := by
  fin_cases i
  · simpa only [heightCenter,Matrix.cons_val_zero,indexPhase] using
      (show (x.1 : ℤ) ∣ (evenPhase d x.1 x.2.1 x.2.2 : ℤ) by
        exact_mod_cast height_dvd_evenPhase d x.1 x.2.1 x.2.2)
  · simpa only [heightCenter,Matrix.cons_val_one,Matrix.cons_val_zero,indexPhase] using
      (show (x.2.2 : ℤ) ∣ (evenPhase d x.1 x.2.1 x.2.2 : ℤ) by
        exact_mod_cast center_dvd_evenPhase d x.1 x.2.1 x.2.2)

theorem heightCenter_injOn_fiber {d : ℕ} (hd : 2 ≤ d) (A : Finset Index)
    (hpos : ∀ x ∈ A, 0 < x.1 ∧ 0 < x.2.2) (n : ℤ) :
    Set.InjOn heightCenter ((A.filter (fun x => indexPhase d x=n)) : Set Index) := by
  intro x hx y hy hkey
  have hh := congrFun hkey 0
  have hz := congrFun hkey 1
  simp only [heightCenter,Matrix.cons_val_zero] at hh
  simp only [heightCenter,Matrix.cons_val_one,Matrix.cons_val_zero] at hz
  have hf := (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm
  dsimp only [indexPhase] at hf
  have heq : evenPhase d x.1 x.2.1 x.2.2 = evenPhase d y.1 y.2.1 y.2.2 := by
    exact_mod_cast hf
  have hxp := hpos x (Finset.mem_filter.mp hx).1
  rw [← hh,← hz] at heq
  have hm := (evenPhase_strictMono hd hxp.1 hxp.2).injective heq
  exact Prod.ext hh (Prod.ext hm hz)

/-- Arbitrarily small power loss in each actual frequency fiber, uniformly
over all finite domains and all half-degrees at least two. -/
theorem first_difference_fiber_le_rpow {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P → ∀ d : ℕ, 2 ≤ d →
      ∀ A : Finset Index,
      (∀ x ∈ A, 0 < x.1 ∧ 0 < x.2.2) →
      (∀ x ∈ A, ((indexPhase d x).natAbs : ℝ) ≤ P^B) →
      ∀ n ∈ A.image (indexPhase d),
        ((A.filter (fun x => indexPhase d x=n)).card : ℝ) ≤ C*P^ε := by
  obtain ⟨C,hC,hbound⟩ := frequency_key_multiplicity 2 hB hε
  refine ⟨C,hC,?_⟩
  intro P hP d hd A hpos hsize n hn
  have hb := hbound P hP Index A (indexPhase d) heightCenter
    (fun x hx => ⟨indexPhase_ne_zero hd x (hpos x hx).1 (hpos x hx).2,hsize x hx⟩)
    (fun x hx i => heightCenter_dvd d x i) n hn
  have hcard := Finset.card_image_of_injOn (heightCenter_injOn_fiber hd A hpos n)
  rwa [hcard] at hb

/-- A uniform bound on genuine frequency fibers controls the exact second
moment, without taking pointwise norms of partial exponential sums. -/
theorem collision_energy_le_fiber_bound {ι : Type*} (A : Finset ι) (f : ι → ℤ)
    {D : ℝ} (hbound : ∀ n ∈ A.image f,
      ((A.filter (fun x => f x=n)).card : ℝ) ≤ D) :
    ((collisionPairs A f).card : ℝ) ≤ D*(A.card : ℝ) := by
  classical
  rw [collision_card_eq_sum A f (A.image f) (fun x hx => Finset.mem_image_of_mem f hx),
    Nat.cast_sum]
  simp only [Nat.cast_pow]
  calc
    _ ≤ ∑ n ∈ A.image f, D*((A.filter (fun x => f x=n)).card : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [pow_two]
      exact mul_le_mul_of_nonneg_right (hbound n hn) (Nat.cast_nonneg _)
    _ = D*(A.card : ℝ) := by
      rw [← Finset.mul_sum,← Nat.cast_sum,← Finset.card_eq_sum_card_image f A]

/-- The actual first-difference Fourier sum has a diagonal-sized L2 moment
up to any positive power loss. -/
theorem first_difference_second_moment {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P → ∀ d : ℕ, 2 ≤ d →
      ∀ A : Finset Index,
      (∀ x ∈ A, 0 < x.1 ∧ 0 < x.2.2) →
      (∀ x ∈ A, ((indexPhase d x).natAbs : ℝ) ≤ P^B) →
      (∫ α in (0 : ℝ)..1,
        ‖∑ x ∈ A, fourier (indexPhase d x) (α : AddCircle (1 : ℝ))‖^2) ≤
          C*P^ε*(A.card : ℝ) := by
  obtain ⟨C,hC,hbound⟩ := first_difference_fiber_le_rpow hB hε
  refine ⟨C,hC,?_⟩
  intro P hP d hd A hpos hsize
  rw [interval_integral_sq_norm_eq_collision_count]
  exact collision_energy_le_fiber_bound A (indexPhase d) (hbound P hP d hd A hpos hsize)

#print axioms first_difference_fiber_le_rpow
#print axioms first_difference_second_moment
end Waring.FirstDifferenceSecond
