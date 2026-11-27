import WaringSiegel.WSL2MomentCounting

/-! # WSL2: finite collision counts with a separate zero fiber -/

noncomputable section
open scoped BigOperators Classical

namespace WaringSiegel.WSL2

variable {α β R : Type*} [Zero R]

theorem finite_collision_card_eq_sum
    (A : Finset α) (B : Finset β) (f : α → R) (g : β → R) :
    ((A.product B).filter (fun p => f p.1 = g p.2)).card =
      ∑ a ∈ A, (B.filter (fun b => g b = f a)).card := by
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  calc
    _ = ∑ a ∈ A, ∑ b ∈ B, if f a = g b then (1 : ℕ) else 0 :=
      Finset.sum_product A B (fun p => if f p.1 = g p.2 then (1 : ℕ) else 0)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      simp only [eq_comm]

/-- Separate the zero fiber before using a uniform bound on every nonzero
fiber. All sets and counts in this inequality are literal finite objects. -/
theorem finite_collision_card_le
    (A : Finset α) (B : Finset β) (f : α → R) (g : β → R) (Zg M : ℕ)
    (hz : (B.filter (fun b => g b = 0)).card ≤ Zg)
    (hnz : ∀ r : R, r ≠ 0 → (B.filter (fun b => g b = r)).card ≤ M) :
    ((A.product B).filter (fun p => f p.1 = g p.2)).card ≤
      (A.filter (fun a => f a = 0)).card * Zg + A.card * M := by
  rw [finite_collision_card_eq_sum]
  calc
    _ ≤ ∑ a ∈ A, ((if f a = 0 then Zg else 0) + M) := by
      apply Finset.sum_le_sum
      intro a ha
      by_cases h : f a = 0
      · rw [h, if_pos rfl]
        exact hz.trans (Nat.le_add_right _ _)
      · rw [if_neg h, zero_add]
        exact hnz (f a) h
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.sum_filter, Finset.sum_const,
        Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
      simp only [Nat.cast_id]

theorem finite_collision_card_le_of_zero_bounds
    (A : Finset α) (B : Finset β) (f : α → R) (g : β → R) (Zf Zg M : ℕ)
    (hf : (A.filter (fun a => f a = 0)).card ≤ Zf)
    (hg : (B.filter (fun b => g b = 0)).card ≤ Zg)
    (hnz : ∀ r : R, r ≠ 0 → (B.filter (fun b => g b = r)).card ≤ M) :
    ((A.product B).filter (fun p => f p.1 = g p.2)).card ≤ Zf * Zg + A.card * M :=
  (finite_collision_card_le A B f g Zg M hg hnz).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_right _ hf) _)

end WaringSiegel.WSL2
