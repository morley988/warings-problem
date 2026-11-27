import WaringSiegel.WSL2MomentBounds

/-!
# Exact multiplicities of power maps on finite unit groups

Every nonempty power fiber is explicitly bijective to the kernel, by division
by one chosen point in the fiber.  This is the arithmetic multiplicity used by
the averaged mixed-moment Cauchy step.
-/

noncomputable section
open scoped BigOperators Classical

namespace WaringSiegel.WSL2

variable {G : Type*} [CommGroup G] [Fintype G]

def powerKernel (G : Type*) [CommGroup G] [Fintype G] (k : ℕ) : Finset G :=
  Finset.univ.filter (fun u => u^k=1)

theorem power_fiber_card_eq_kernel (k : ℕ) (a : G) :
    (Finset.univ.filter (fun u : G => u^k=a^k)).card = (powerKernel G k).card := by
  apply Finset.card_bij (fun u _ => a⁻¹*u)
  · intro u hu
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [mul_pow, inv_pow, (Finset.mem_filter.mp hu).2, inv_mul_cancel]
  · intro u hu v hv heq
    exact mul_left_cancel heq
  · intro u hu
    refine ⟨a*u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · rw [mul_pow, (Finset.mem_filter.mp hu).2, mul_one]
    · simp

theorem power_fiber_card_le_kernel (k : ℕ) (b : G) :
    (Finset.univ.filter (fun u : G => u^k=b)).card ≤ (powerKernel G k).card := by
  by_cases h : (Finset.univ.filter (fun u : G => u^k=b)).Nonempty
  · obtain ⟨a,ha⟩ := h
    rw [← (Finset.mem_filter.mp ha).2, power_fiber_card_eq_kernel]
  · simp only [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.card_empty]
    exact Nat.zero_le _

variable {R : Type*} [CommRing R] [Fintype R]

def unitPowerKernel (R : Type*) [CommRing R] [Fintype R] (k : ℕ) : Finset Rˣ :=
  powerKernel Rˣ k

theorem unit_power_fiber_card_le (k : ℕ) (b : R) :
    (Finset.univ.filter (fun u : Rˣ => (u : R)^k=b)).card ≤ (unitPowerKernel R k).card := by
  by_cases h : (Finset.univ.filter (fun u : Rˣ => (u : R)^k=b)).Nonempty
  · obtain ⟨a,ha⟩ := h
    have hab : (a:R)^k=b := (Finset.mem_filter.mp ha).2
    apply Finset.card_le_card_of_injOn (fun u => a⁻¹*u)
    · intro u hu
      have hupow : u^k=a^k := by
        apply Units.ext
        change (u : R)^k=(a : R)^k
        exact (Finset.mem_filter.mp hu).2.trans hab.symm
      simp only [Finset.mem_coe, unitPowerKernel, powerKernel, Finset.mem_filter,
        Finset.mem_univ, true_and]
      rw [mul_pow, inv_pow, hupow, inv_mul_cancel]
    · intro u hu v hv heq
      exact mul_left_cancel heq
  · simp only [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.card_empty]
    exact Nat.zero_le _

end WaringSiegel.WSL2
