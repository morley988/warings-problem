import WaringSiegel.WSL3MomentSparsePolynomial

/-!
# Exact common-translation identities for the localized moment

The lower power-sum equations persist under a common translation. The
remaining top equation picks up exactly the single k*z*sigma_(k-1) term.
These identities hold in any commutative ring.
-/

noncomputable section
open Polynomial
open scoped BigOperators Classical

namespace WaringSiegel.WSL3

variable {A : Type*} [CommRing A]

def powerSumDifference (j s : ℕ) (x y : Fin s → A) : A :=
  (∑ i, x i^j) - ∑ i, y i^j

theorem powerSumDifference_add (n s : ℕ) (x y : Fin s → A) (z : A) :
    powerSumDifference n s (fun i => x i+z) (fun i => y i+z) =
      ∑ j ∈ Finset.range (n+1), powerSumDifference j s x y * z^(n-j) * (n.choose j : A) := by
  simp only [powerSumDifference, add_pow]
  rw [Finset.sum_comm, Finset.sum_comm (s := Finset.univ), ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Finset.sum_mul, sub_mul]

theorem powerSumDifference_zero (s : ℕ) (x y : Fin s → A) : powerSumDifference 0 s x y = 0 := by
  simp [powerSumDifference]

theorem common_shift_top_identity_succ (R s : ℕ) (x y : Fin s → A) (z : A)
    (hlow : ∀ j, j < R+1 → powerSumDifference j s x y = 0) :
    powerSumDifference (R+2) s (fun i => x i-z) (fun i => y i-z) =
      powerSumDifference (R+2) s x y - (R+2 : ℕ)*z*powerSumDifference (R+1) s x y := by
  simp only [sub_eq_add_neg]
  rw [powerSumDifference_add, Finset.sum_range_succ, Finset.sum_range_succ]
  have hlo : (∑ j ∈ Finset.range (R+1),
      powerSumDifference j s x y * (-z)^(R+2-j) * ((R+2).choose j : A)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [hlow j (Finset.mem_range.mp hj), zero_mul, zero_mul]
  rw [hlo]
  simp only [show R+2-(R+1)=1 by omega, Nat.sub_self, pow_one, pow_zero,
    Nat.choose_self, Nat.cast_one, mul_one, zero_add,
    show (R+2).choose (R+1)=R+2 from Nat.choose_succ_self_right (R+1)]
  ring

theorem common_shift_top_identity (k s : ℕ) (hk : 2 ≤ k) (x y : Fin s → A) (z : A)
    (hlow : ∀ j, j < k-1 → powerSumDifference j s x y = 0) :
    powerSumDifference k s (fun i => x i-z) (fun i => y i-z) =
      powerSumDifference k s x y - (k : A)*z*powerSumDifference (k-1) s x y := by
  have h := common_shift_top_identity_succ (k-2) s x y z
    (fun j hj => hlow j (by omega))
  simpa only [show k-2+2=k by omega, show k-2+1=k-1 by omega] using h

theorem common_shift_preserves_lower_equations (r s : ℕ) (x y : Fin s → A) (z : A)
    (hlow : ∀ j, j < r → powerSumDifference j s x y = 0) :
    ∀ j, j < r → powerSumDifference j s (fun i => x i-z) (fun i => y i-z) = 0 := by
  have h := powerSums_below_translation r s x y z
    (fun j hj => sub_eq_zero.mp (hlow j hj))
  intro j hj
  exact sub_eq_zero.mpr (h j hj)

#print axioms common_shift_top_identity
#print axioms common_shift_preserves_lower_equations

end WaringSiegel.WSL3
