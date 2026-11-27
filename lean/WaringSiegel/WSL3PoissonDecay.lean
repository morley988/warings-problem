import WaringSiegel.WSL3PoissonPeriodization
import WaringSiegel.WSL2MomentLatticeDecay
import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Data.Int.Interval
import Mathlib.Data.Fintype.BigOperators

/-!
# Summable tails on the integer coordinate lattice

The dimension-dependent polynomial tail is proved summable by actual finite
integer-box counts. It will discharge the normal convergence hypotheses of
Poisson summation for rapidly decreasing functions.
-/

noncomputable section
open MeasureTheory Topology TopologicalSpace
open scoped BigOperators Classical SchwartzMap
namespace WaringSiegel.WSL3Poisson
variable {ι : Type*} [Fintype ι]

/-- Counting an annulus by the enclosing integer coordinate box. -/
theorem integer_annulus_card (S : Finset (ι → ℤ)) (N : ℕ) :
    ((S.filter (fun n => ⌊‖intVector n‖⌋₊ = N)).card : ℝ) ≤
      (3:ℝ)^(Fintype.card ι)*((N:ℝ)+1)^(Fintype.card ι) := by
  let box : Finset (ι → ℤ) := Fintype.piFinset fun _ =>
    Finset.Icc (-(N:ℤ)-1) ((N:ℤ)+1)
  have hsub : S.filter (fun n => ⌊‖intVector n‖⌋₊ = N) ⊆ box := by
    intro n hn
    have hf := (Finset.mem_filter.mp hn).2
    have hnorm : ‖intVector n‖ ≤ (N:ℝ)+1 := by
      have h := Nat.lt_floor_add_one ‖intVector n‖
      rw [hf] at h
      exact h.le
    apply Fintype.mem_piFinset.mpr
    intro i
    have hi : |(n i : ℝ)| ≤ (N:ℝ)+1 :=
      (norm_le_pi_norm (intVector n) i).trans hnorm
    have hbounds := abs_le.mp hi
    apply Finset.mem_Icc.mpr
    constructor
    · have h : -(N:ℤ)-1 ≤ n i := by
        norm_cast at hbounds
        omega
      exact h
    · exact_mod_cast hbounds.2
  have hcard : box.card = (2*N+3)^(Fintype.card ι) := by
    simp only [box, Fintype.card_piFinset, Int.card_Icc, sub_sub,
      sub_neg_eq_add, Finset.prod_const, Finset.card_univ]
    congr 1
    omega
  calc
    _ ≤ (box.card : ℝ) := Nat.cast_le.mpr (Finset.card_le_card hsub)
    _ = ((2*N+3:ℕ):ℝ)^(Fintype.card ι) := by rw [hcard, Nat.cast_pow]
    _ ≤ (3*((N:ℝ)+1))^(Fintype.card ι) := by
      apply pow_le_pow_left₀ (by positivity)
      have hN : (0:ℝ) ≤ N := by positivity
      push_cast
      linarith
    _ = _ := by rw [mul_pow]

/-- A summable radial majorant with an explicit finite-sum bound. -/
theorem integer_radial_decay_summable :
    Summable (fun n : ι → ℤ => 1/(1+‖intVector n‖)^(Fintype.card ι+2)) ∧
    (∑' n : ι → ℤ, 1/(1+‖intVector n‖)^(Fintype.card ι+2)) ≤
      2*(3:ℝ)^(Fintype.card ι) := by
  have hbound (S : Finset (ι → ℤ)) :
      (∑n∈S, 1/(1+‖intVector n‖)^(Fintype.card ι+2)) ≤
        2*(3:ℝ)^(Fintype.card ι) :=
    WSL2.finite_annular_decay_bound S (fun n => ‖intVector n‖)
      (fun _ _ => norm_nonneg _) (Fintype.card ι) ((3:ℝ)^(Fintype.card ι))
      (by positivity) (integer_annulus_card S)
  have hs := summable_of_sum_le (fun n : ι → ℤ => by
    positivity : ∀ n : ι → ℤ, 0 ≤ 1/(1+‖intVector n‖)^(Fintype.card ι+2)) hbound
  exact ⟨hs, hs.tsum_le_of_sum_le hbound⟩

/-- Translation of a polynomial weight, uniformly on a norm-bounded set. -/
theorem polynomial_weight_translate (x y : ι → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hx : ‖x‖ ≤ R) (k : ℕ) :
    (1+‖y‖)^k ≤ (1+R)^k * (1+‖x+y‖)^k := by
  rw [← mul_pow]
  apply pow_le_pow_left₀ (by positivity)
  have ht : ‖y‖ ≤ ‖x+y‖+‖x‖ := by
    simpa only [add_sub_cancel_left] using norm_sub_le (x+y) x
  have hh : 0 ≤ R*‖x+y‖ := mul_nonneg hR (norm_nonneg _)
  nlinarith

/-- Polynomial decay of order dimension plus two gives locally normal
convergence of the actual lattice translate series. -/
theorem locally_normal_of_polynomial_bound (f : C((ι → ℝ), ℂ))
    (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ x, (1+‖x‖)^(Fintype.card ι+2)*‖f x‖ ≤ C)
    (K : Compacts (ι → ℝ)) :
    Summable fun n : ι → ℤ =>
      ‖(f.comp (ContinuousMap.addRight (intVector n))).restrict K‖ := by
  obtain ⟨R, hR, hb⟩ := K.isCompact.isBounded.exists_pos_norm_le
  have hbound (n : ι → ℤ) :
      ‖(f.comp (ContinuousMap.addRight (intVector n))).restrict K‖ ≤
        ((1+R)^(Fintype.card ι+2)*C) *
          (1/(1+‖intVector n‖)^(Fintype.card ι+2)) := by
    apply (ContinuousMap.norm_le _ (by positivity)).mpr
    intro x
    change ‖f ((x:ι→ℝ)+intVector n)‖ ≤ _
    rw [mul_one_div, le_div_iff₀ (by positivity)]
    calc
      _ ≤ ‖f ((x:ι→ℝ)+intVector n)‖ *
          ((1+R)^(Fintype.card ι+2)*(1+‖(x:ι→ℝ)+intVector n‖)^(Fintype.card ι+2)) :=
        mul_le_mul_of_nonneg_left
          (polynomial_weight_translate (x:ι→ℝ) (intVector n) R hR.le (hb x x.property) _)
          (norm_nonneg _)
      _ = (1+R)^(Fintype.card ι+2)*
          ((1+‖(x:ι→ℝ)+intVector n‖)^(Fintype.card ι+2)*‖f ((x:ι→ℝ)+intVector n)‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hf _) (by positivity)
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound
    (integer_radial_decay_summable.1.mul_left _)

/-- Every Schwartz function has a genuine global polynomial bound. -/
theorem schwartz_polynomial_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : 𝓢(E, ℂ)) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, (1+‖x‖)^k * ‖f x‖ ≤ C := by
  let C : ℝ := 2^k * (Finset.Iic (k, 0)).sup
    (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f
  refine ⟨C, by positivity, fun x => ?_⟩
  simpa only [norm_iteratedFDeriv_zero] using
    (SchwartzMap.one_add_le_sup_seminorm_apply (𝕜:=ℝ) (m:=(k,0))
      (k:=k) (n:=0) le_rfl le_rfl f x)

/-- Normal convergence is proved, not retained as an assumption, for Schwartz data. -/
theorem schwartz_locally_normal (f : 𝓢((ι → ℝ), ℂ)) (K : Compacts (ι → ℝ)) :
    Summable fun n : ι → ℤ =>
      ‖(f.toContinuousMap.comp (ContinuousMap.addRight (intVector n))).restrict K‖ := by
  obtain ⟨C, hC, hf⟩ := schwartz_polynomial_bound f (Fintype.card ι+2)
  exact locally_normal_of_polynomial_bound f.toContinuousMap C hC hf K

/-- Absolute summability of actual Schwartz samples on the integer lattice. -/
theorem schwartz_integer_summable (f : 𝓢((ι → ℝ), ℂ)) :
    Summable fun n : ι → ℤ => f (intVector n) := by
  obtain ⟨C, hC, hf⟩ := schwartz_polynomial_bound f (Fintype.card ι+2)
  apply Summable.of_norm_bounded (integer_radial_decay_summable.1.mul_left C)
  intro n
  rw [mul_one_div, le_div_iff₀ (by positivity)]
  simpa only [mul_comm] using hf (intVector n)

end WaringSiegel.WSL3Poisson
