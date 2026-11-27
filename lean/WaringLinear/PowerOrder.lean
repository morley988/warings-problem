import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import WaringSiegel.NumberFieldTargets

/-! The additive span of kth powers is a unital ring and contains the
factorial conductor k! R in any commutative ring. This identifies a
finite modulus for the eligibility condition on algebraic integers. -/

open Finset
open scoped BigOperators NumberField

namespace WaringLinear.PowerOrder

variable {R : Type*} [CommRing R]

/-- Additive subgroups containing the kth powers contain the k! multiples.
Take k−1 forward differences in the translating variable of
(t+x)^k−t^k. -/
theorem factorial_mul_mem (J : AddSubgroup R) {k : ℕ} (hk : 0 < k)
    (hp : ∀ x : R, x ^ k ∈ J) (x : R) : (k.factorial : R) * x ∈ J := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  let c (j : ℕ) : R := x ^ (n + 1 - j) * ((n + 1).choose j : R)
  have expansion : (fun t : R => (t + x) ^ (n + 1) - t ^ (n + 1)) =
      (fun t : R => ∑ j ∈ range n, c j * t ^ j) +
        c n • (fun t : R => t ^ n) := by
    funext t
    rw [add_pow, sum_range_succ, sum_range_succ]
    simp only [Nat.sub_self, pow_zero, mul_one, Nat.choose_self, Nat.cast_one,
      add_sub_cancel_right, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    congr 1
    · exact sum_congr rfl fun j _ => by dsimp [c]; ring
    · dsimp [c]; ring
  let f (t : R) := (t + x) ^ (n + 1) - t ^ (n + 1)
  have hf (t : R) : f t ∈ J := J.sub_mem (hp (t + x)) (hp t)
  have hf_diff : (fwdDiff (1 : R))^[n] f 0 ∈ J := by
    rw [fwdDiff_iter_eq_sum_shift]
    exact J.sum_mem fun j _ => J.zsmul_mem (hf _) _
  have evaluate : (fwdDiff (1 : R))^[n] f =
      c n • ((n.factorial : R → R)) := by
    change (fwdDiff (1 : R))^[n] (fun t : R => (t+x)^(n+1)-t^(n+1)) = _
    rw [expansion, fwdDiff_iter_add, fwdDiff_iter_sum_mul_pow_eq_zero,
      fwdDiff_iter_const_smul, fwdDiff_iter_eq_factorial, zero_add]
  rw [evaluate] at hf_diff
  simpa [c, Nat.factorial_succ, mul_comm, mul_left_comm, mul_assoc] using hf_diff

/-- Products of elements in the additive span of powers again lie in the span. -/
theorem mul_mem_powerClosure (k : ℕ) {x y : R}
    (hx : x ∈ AddSubgroup.closure (Set.range fun z : R => z ^ k))
    (hy : y ∈ AddSubgroup.closure (Set.range fun z : R => z ^ k)) :
    x*y ∈ AddSubgroup.closure (Set.range fun z : R => z ^ k) := by
  let J := AddSubgroup.closure (Set.range fun z : R => z ^ k)
  apply AddSubgroup.closure_induction₂
      (p := fun a b _ _ => a*b ∈ J) _ _ _ _ _ _ _ hx hy
  · rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact AddSubgroup.subset_closure ⟨a*b, mul_pow a b k⟩
  · intro a _; simp
  · intro a _; simp
  · intro a b t _ _ _ ha hb; simpa [add_mul] using J.add_mem ha hb
  · intro a b t _ _ _ ha hb; simpa [mul_add] using J.add_mem ha hb
  · intro a b _ _ hab; simpa using J.neg_mem hab
  · intro a b _ _ hab; simpa using J.neg_mem hab

variable {K : Type*} [Field K]

theorem eligible_factorial_mul {k : ℕ} (hk : 0 < k) (x : 𝓞 K) :
    WaringSiegel.Eligible k ((k.factorial : 𝓞 K) * x) :=
  factorial_mul_mem (WaringSiegel.powerSubgroup k) hk
    (fun y => AddSubgroup.subset_closure ⟨y, rfl⟩) x

theorem eligible_one (k : ℕ) : WaringSiegel.Eligible k (1 : 𝓞 K) :=
  AddSubgroup.subset_closure ⟨1, one_pow k⟩

theorem eligible_mul {k : ℕ} {x y : 𝓞 K}
    (hx : WaringSiegel.Eligible k x) (hy : WaringSiegel.Eligible k y) :
    WaringSiegel.Eligible k (x*y) :=
  mul_mem_powerClosure k hx hy

/-- Congruence modulo the factorial conductor determines eligibility. -/
theorem eligible_iff_of_factorial_dvd_sub {k : ℕ} (hk : 0 < k) {x y : 𝓞 K}
    (hxy : (k.factorial : 𝓞 K) ∣ x-y) :
    WaringSiegel.Eligible k x ↔ WaringSiegel.Eligible k y := by
  obtain ⟨z, hz⟩ := hxy
  have hd : x-y ∈ WaringSiegel.powerSubgroup k := hz ▸ eligible_factorial_mul hk z
  constructor
  · intro hx
    simpa using (WaringSiegel.powerSubgroup k).sub_mem hx hd
  · intro hy
    simpa using (WaringSiegel.powerSubgroup k).add_mem hd hy

variable [NumberField K]

/-- The additive index divides (k!)^[K:ℚ], with no ideal-class assumptions. -/
theorem powerSubgroup_index_dvd {k : ℕ} (hk : 0 < k) :
    (WaringSiegel.powerSubgroup (K := K) k).index ∣ k.factorial ^ Module.finrank ℚ K := by
  let I : Ideal (𝓞 K) := Ideal.span {(k.factorial : 𝓞 K)}
  have hI : I.toAddSubgroup ≤ WaringSiegel.powerSubgroup k := by
    intro y hy
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton.mp (show y ∈ I from hy)
    rw [hz]
    exact eligible_factorial_mul hk z
  have hd := AddSubgroup.index_dvd_of_le hI
  change _ ∣ Ideal.absNorm I at hd
  rw [show I = Ideal.span {(k.factorial : 𝓞 K)} from rfl,
    Ideal.absNorm_span_singleton] at hd
  have hnorm := Algebra.norm_algebraMap_of_basis (NumberField.RingOfIntegers.basis K)
    (k.factorial : ℤ)
  rw [← Module.finrank_eq_card_basis (NumberField.RingOfIntegers.basis K),
    NumberField.RingOfIntegers.rank] at hnorm
  simp only [map_natCast] at hnorm
  rwa [hnorm, Int.natAbs_pow, Int.natAbs_natCast] at hd

theorem finite_powerSubgroup_quotient {k : ℕ} (hk : 0 < k) :
    Finite ((𝓞 K) ⧸ WaringSiegel.powerSubgroup (K := K) k) := by
  apply AddSubgroup.index_ne_zero_iff_finite.mp
  exact ne_zero_of_dvd_ne_zero (pow_ne_zero _ (Nat.factorial_ne_zero k))
    (powerSubgroup_index_dvd hk)

#print axioms powerSubgroup_index_dvd
#print axioms finite_powerSubgroup_quotient
#print axioms factorial_mul_mem
#print axioms eligible_mul
#print axioms eligible_iff_of_factorial_dvd_sub

end WaringLinear.PowerOrder
