import WaringSiegel.WSL3PoissonMixedTorus

/-! # Uniform diagonal pair count for the sixth-power variables -/
noncomputable section
open scoped BigOperators Classical NumberField
open NumberField WaringSiegel.WSL2
namespace WaringSiegel.WSL3Poisson

variable {R α : Type*} [CommRing R] [IsDomain R] [Fintype α]

theorem equal_power_pair_card_le (x : α → R) (hx : Function.Injective x)
    (k : ℕ) (hk : 0 < k) :
    ((Finset.univ : Finset (α × α)).filter (fun p => x p.1^k = x p.2^k)).card ≤
      k*Fintype.card α := by
  have he : ((Finset.univ : Finset (α × α)).filter (fun p => x p.1^k = x p.2^k)).card =
      ∑ a : α, (Finset.univ.filter (fun b => x b^k = x a^k)).card := by
    simp only [Finset.card_eq_sum_ones,Finset.sum_filter,Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [eq_comm (a:=x a^k) (b:=x b^k)]
  rw [he]
  calc
    _ ≤ ∑ _a : α, k := Finset.sum_le_sum (fun a _ => indexed_power_fiber_card_le x hx k hk (x a^k))
    _ = _ := by simp [Nat.mul_comm]

/-- A pair sum separates into at most k*N zero differences and at most N^2
nonzero differences; no height or norm of a nonzero difference enters. -/
theorem power_pair_cost_bound (x : α → R) (hx : Function.Injective x)
    (k : ℕ) (hk : 0 < k) (F : R → ℝ) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hzero : F 0 ≤ A) (hoff : ∀ d : R, d ≠ 0 → F d ≤ B) :
    (∑ p : α × α, F (x p.1^k-x p.2^k)) ≤
      k*(Fintype.card α : ℝ)*A+(Fintype.card α : ℝ)^2*B := by
  let S := (Finset.univ : Finset (α × α)).filter (fun p => x p.1^k = x p.2^k)
  have hcard : (S.card:ℝ) ≤ k*(Fintype.card α:ℝ) := by
    exact_mod_cast equal_power_pair_card_le x hx k hk
  have hsum : (∑ p : α × α, F (x p.1^k-x p.2^k)) ≤
      ∑ p : α × α, ((if x p.1^k=x p.2^k then A else 0)+B) := by
    apply Finset.sum_le_sum
    intro p _
    by_cases hp : x p.1^k=x p.2^k
    · simp only [hp,sub_self,if_true]
      exact hzero.trans (le_add_of_nonneg_right hB)
    · simp only [if_neg hp,zero_add]
      exact hoff _ (sub_ne_zero.mpr hp)
  calc
    _ ≤ _ := hsum
    _ = (S.card:ℝ)*A+(Fintype.card α:ℝ)^2*B := by
      rw [Finset.sum_add_distrib]
      have hfirst : (∑ p : α × α, if x p.1^k=x p.2^k then A else 0) = (S.card:ℝ)*A := by
        rw [← Finset.sum_filter]
        simp only [S,Finset.sum_const,nsmul_eq_mul]
      rw [hfirst]
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,nsmul_eq_mul,Nat.cast_mul]
      ring
    _ ≤ _ := add_le_add_right (mul_le_mul_of_nonneg_right hcard hA) _

end WaringSiegel.WSL3Poisson
