import WaringSiegel.WSL3MomentSystemEnergy

/-!
# Finite partition loss for literal system energies

Finite Hölder bounds the whole Fourier moment by the sum of moments on
its classes with the exact cardinality factor.  No unspecified counting
reduction or averaging hypothesis is used.
-/

noncomputable section
open Finset GafniTao
open scoped BigOperators Classical

namespace WaringSiegel.WSL3

variable {α β : Type*} [Fintype α] [Fintype β]

theorem sum_fibers_eq {T : Type*} [AddCommMonoid T] (tag : α → β) (f : α → T) :
    (∑ t : β, ∑ x : {x // tag x=t}, f x) = ∑ x, f x := by
  calc
    _ = ∑ x : (Σ t : β, {x // tag x=t}), f x.2 :=
      (Fintype.sum_sigma (fun x : (Σ t : β, {x // tag x=t}) => f x.2)).symm
    _ = _ := (Equiv.sigmaFiberEquiv tag).sum_comp f

theorem fiber_mass_le (tag : α → β) (w : α → ℝ) (t : β) :
    (∑ x : {x // tag x=t}, w x^2) ≤ ∑ x, w x^2 := by
  have h : (∑ x : {x // tag x=t}, w x^2) ≤
      ∑ t : β, ∑ x : {x // tag x=t}, w x^2 := by
    apply Finset.single_le_sum (f := fun t : β => ∑ x : {x // tag x=t}, w x^2) _ (Finset.mem_univ t)
    intro t ht
    exact Finset.sum_nonneg (fun x _ => sq_nonneg (w x))
  exact h.trans_eq (sum_fibers_eq tag (fun x => w x^2))

theorem weightedSystemEnergy_partition_le (q r s : ℕ) [NeZero q] (hs : 1 ≤ s)
    (value : α → Fin r → ZMod q) (w : α → ℝ) (tag : α → β) :
    weightedSystemEnergy s value w ≤
      (Fintype.card β : ℝ)^(2*s-1) *
        ∑ t : β, weightedSystemEnergy s (fun x : {x // tag x=t} => value x) (fun x => w x) := by
  let F (t : β) (a : Fin r → ZMod q) : ℂ :=
    ∑ x : {x // tag x=t}, (w x : ℂ)*ZMod.stdAddChar (∑ j, a j*value x j)
  have hsum (a : Fin r → ZMod q) :
      (∑ x, (w x : ℂ)*ZMod.stdAddChar (∑ j, a j*value x j)) = ∑ t, F t a := by
    exact (sum_fibers_eq tag _).symm
  have hpoint (a : Fin r → ZMod q) :
      ‖∑ t, F t a‖^(2*s) ≤ (Fintype.card β : ℝ)^(2*s-1)*∑ t, ‖F t a‖^(2*s) := by
    calc
      _ ≤ (∑ t, ‖F t a‖)^(2*s) := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) _
      _ ≤ _ := by
        simpa only [Finset.card_univ, show 2*s-1+1=2*s by omega] using
          pow_sum_le_card_mul_sum_pow (s := Finset.univ) (f := fun t => ‖F t a‖)
            (fun t ht => norm_nonneg _) (2*s-1)
  rw [← weighted_system_grid_mean q r s value w]
  simp_rw [hsum]
  calc
    _ ≤ ((q^r : ℕ) : ℝ)⁻¹ *
        ∑ a : Fin r → ZMod q, (Fintype.card β : ℝ)^(2*s-1)*∑ t, ‖F t a‖^(2*s) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun a _ => hpoint a)) (by positivity)
    _ = (Fintype.card β : ℝ)^(2*s-1)*
        ∑ t : β, (((q^r : ℕ) : ℝ)⁻¹ * ∑ a : Fin r → ZMod q, ‖F t a‖^(2*s)) := by
      rw [← Finset.mul_sum, Finset.sum_comm, ← Finset.mul_sum]
      ring
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro t ht
      exact weighted_system_grid_mean q r s _ _

theorem weightedSystemEnergy_subsingleton {A : Type*} [AddCommMonoid A]
    [Subsingleton α] (s : ℕ) (hs : 1 ≤ s) (value : α → A) (w : α → ℝ) :
    weightedSystemEnergy s value w = (∑ x, w x^2)^s := by
  cases isEmpty_or_nonempty α with
  | inl hempty =>
    letI : IsEmpty α := hempty
    haveI : IsEmpty (Fin s → α) := ⟨fun f => isEmptyElim (f ⟨0,hs⟩)⟩
    simp [weightedSystemEnergy, Nat.ne_of_gt hs]
  | inr hnonempty =>
    letI : Nonempty α := hnonempty
    letI : Unique α := uniqueOfSubsingleton (Classical.choice hnonempty)
    letI : Unique (Fin s → α) := uniqueOfSubsingleton (fun _ => default)
    letI : Unique ((Fin s → α) × (Fin s → α)) := uniqueOfSubsingleton (default, default)
    simp only [weightedSystemEnergy, Finset.univ_unique, Finset.sum_singleton]
    have heq : (∑ i, value ((default : (Fin s → α) × (Fin s → α)).1 i)) =
        ∑ i, value ((default : (Fin s → α) × (Fin s → α)).2 i) := by rfl
    rw [if_pos heq]
    have hwconst (x : α) : w x=w default := congrArg w (Subsingleton.elim x default)
    simp only [hwconst, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    ring

#print axioms weightedSystemEnergy_partition_le

end WaringSiegel.WSL3
