import Mathlib.Combinatorics.Additive.CauchyDavenport
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Actual nonsingular power-sum solutions modulo every good prime

Cauchy--Davenport and the elementary polynomial root bound show that
every residue modulo a prime is a sum of k kth powers. Reserving one
additional variable equal to one gives a nonzero coordinate. No local
solubility assumption is introduced.
-/

noncomputable section
open scoped BigOperators Pointwise
namespace Waring.LocalSolubility

def iteratedSumset {G : Type*} [DecidableEq G] [AddMonoid G] (A : Finset G) : ℕ → Finset G
  | 0 => {0}
  | n+1 => A+iteratedSumset A n

theorem zero_mem_iteratedSumset {G : Type*} [DecidableEq G] [AddMonoid G]
    {A : Finset G} (hA : 0 ∈ A) (n : ℕ) : 0 ∈ iteratedSumset A n := by
  induction n with
  | zero => simp [iteratedSumset]
  | succ n ih =>
      exact Finset.mem_add.mpr ⟨0,hA,0,ih,zero_add 0⟩

theorem mem_iteratedSumset_iff {G : Type*} [DecidableEq G] [AddCommMonoid G]
    (A : Finset G) (n : ℕ) (z : G) :
    z ∈ iteratedSumset A n ↔ ∃ x : Fin n → G,(∀ i,x i ∈ A) ∧ ∑ i,x i=z := by
  induction n generalizing z with
  | zero => simp [iteratedSumset,eq_comm]
  | succ n ih =>
      constructor
      · intro hz
        obtain ⟨a,ha,b,hb,hab⟩ := Finset.mem_add.mp hz
        obtain ⟨x,hx,hxs⟩ := (ih b).mp hb
        refine ⟨Fin.cons a x,?_,?_⟩
        · intro i
          exact Fin.cases ha hx i
        · simpa only [Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ,hxs] using hab
      · rintro ⟨x,hx,hxs⟩
        apply Finset.mem_add.mpr
        refine ⟨x 0,hx 0,∑ i : Fin n,x i.succ,(ih _).mpr ⟨fun i => x i.succ,fun i => hx i.succ,rfl⟩,?_⟩
        simpa only [Fin.sum_univ_succ] using hxs

theorem iteratedSumset_card_lower {p : ℕ} (hp : p.Prime) [NeZero p]
    {A : Finset (ZMod p)} (hA : 0 ∈ A) (n : ℕ) :
    min p (n*(A.card-1)+1) ≤ (iteratedSumset A n).card := by
  have hAnon : A.Nonempty := ⟨0,hA⟩
  have hApos := hAnon.card_pos
  induction n with
  | zero => simp [iteratedSumset]
  | succ n ih =>
      have hsnon : (iteratedSumset A n).Nonempty := ⟨0,zero_mem_iteratedSumset hA n⟩
      have hcd := ZMod.cauchy_davenport hp hAnon hsnon
      change min p ((n+1)*(A.card-1)+1) ≤ (A+iteratedSumset A n).card
      apply le_trans _ hcd
      rw [Nat.add_mul,one_mul]
      by_cases hn : p ≤ n*(A.card-1)+1
      · rw [min_eq_left hn] at ih
        have hm : p ≤ A.card+(iteratedSumset A n).card-1 := by omega
        rw [min_eq_left hm]
        exact min_le_left _ _
      · rw [min_eq_right (le_of_not_ge hn)] at ih
        apply min_le_min_left
        omega

def powerResidues (k p : ℕ) [NeZero p] : Finset (ZMod p) :=
  Finset.univ.image (fun x : ZMod p => x^k)

theorem zero_mem_powerResidues {k p : ℕ} [NeZero p] (hk : 0 < k) :
    0 ∈ powerResidues k p :=
  Finset.mem_image.mpr ⟨0,Finset.mem_univ _,zero_pow hk.ne'⟩

theorem prime_power_fiber_card_le {k p : ℕ} (hp : p.Prime) (hk : 0 < k)
    [NeZero p] (a : ZMod p) : (Finset.univ.filter (fun x : ZMod p => x^k=a)).card ≤ k := by
  letI : Fact p.Prime := ⟨hp⟩
  classical
  calc
    _ ≤ (Polynomial.nthRootsFinset k a).card := by
      apply Finset.card_le_card
      intro x hx
      exact (Polynomial.mem_nthRootsFinset hk a).mpr (Finset.mem_filter.mp hx).2
    _ ≤ (Polynomial.nthRoots k a).card := by
      simpa only [Polynomial.nthRootsFinset_def] using Multiset.toFinset_card_le (Polynomial.nthRoots k a)
    _ ≤ k := Polynomial.card_nthRoots k a

theorem powerResidues_card_lower {k p : ℕ} (hp : p.Prime) (hk : 0 < k) [NeZero p] :
    p ≤ k*((powerResidues k p).card-1)+1 := by
  letI : Fact p.Prime := ⟨hp⟩
  classical
  let A := powerResidues k p
  let F := fun a : ZMod p => (Finset.univ.filter (fun x : ZMod p => x^k=a)).card
  have h0 : 0 ∈ A := zero_mem_powerResidues hk
  have hF0 : F 0=1 := by
    have he : (Finset.univ.filter (fun x : ZMod p => x^k=0))={0} := by
      ext x
      simp [pow_eq_zero_iff hk.ne']
    simp only [F,he,Finset.card_singleton]
  have hsum : p=∑ a ∈ A,F a := by
    simpa only [Finset.card_univ,ZMod.card,A,powerResidues,F] using
      (Finset.card_eq_sum_card_image (fun x : ZMod p => x^k) Finset.univ)
  calc
    p = ∑ a ∈ A,F a := hsum
    _ = (∑ a ∈ A.erase 0,F a)+1 := by rw [← Finset.sum_erase_add _ _ h0,hF0]
    _ ≤ (∑ _a ∈ A.erase 0,k)+1 := Nat.add_le_add_right
      (Finset.sum_le_sum (fun a _ => prime_power_fiber_card_le hp hk a)) 1
    _ = k*(A.card-1)+1 := by rw [Finset.sum_const,smul_eq_mul,Finset.card_erase_of_mem h0]; ring

theorem iterated_powerResidues_eq_univ {k p : ℕ} (hp : p.Prime) (hk : 0 < k) [NeZero p] :
    iteratedSumset (powerResidues k p) k=Finset.univ := by
  apply Finset.eq_univ_of_card
  apply le_antisymm (Finset.card_le_univ _)
  have h := iteratedSumset_card_lower hp (zero_mem_powerResidues hk) k
  rw [min_eq_left (powerResidues_card_lower hp hk)] at h
  simpa only [ZMod.card] using h

/-- Every residue is represented by exactly k kth powers, allowing zero
coordinates. This is a literal finite-field existence theorem. -/
theorem prime_sum_powers {k p : ℕ} (hp : p.Prime) (hk : 0 < k) (n : ZMod p) :
    ∃ x : Fin k → ZMod p,∑ i,(x i)^k=n := by
  letI : Fact p.Prime := ⟨hp⟩
  classical
  have hn : n ∈ iteratedSumset (powerResidues k p) k := by
    rw [iterated_powerResidues_eq_univ hp hk]
    exact Finset.mem_univ _
  obtain ⟨y,hy,hys⟩ := (mem_iteratedSumset_iff _ _ _).mp hn
  have hx : ∀ i : Fin k,∃ x : ZMod p,x^k=y i := by
    intro i
    obtain ⟨x,_,hx⟩ := Finset.mem_image.mp (hy i)
    exact ⟨x,hx⟩
  choose x hx using hx
  exact ⟨x,by simpa only [hx] using hys⟩

/-- The additional reserved unit coordinate provides the nonsingular
solution required for lifting whenever the prime does not divide k. -/
theorem prime_sum_powers_with_unit {k p : ℕ} (hp : p.Prime) (hk : 0 < k) (n : ZMod p) :
    ∃ x : Fin (k+1) → ZMod p,x 0=1 ∧ ∑ i,(x i)^k=n := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x,hx⟩ := prime_sum_powers hp hk (n-1)
  refine ⟨Fin.cons 1 x,rfl,?_⟩
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero,one_pow,Fin.cons_succ,hx]
  ring

theorem iterated_powerResidues_eq_univ_of_le {k s p : ℕ} (hp : p.Prime)
    (hk : 0 < k) (hks : k ≤ s) [NeZero p] :
    iteratedSumset (powerResidues k p) s=Finset.univ := by
  apply Finset.eq_univ_of_card
  apply le_antisymm (Finset.card_le_univ _)
  have hsize : p ≤ s*((powerResidues k p).card-1)+1 :=
    (powerResidues_card_lower hp hk).trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hks) 1)
  have hh := iteratedSumset_card_lower hp (zero_mem_powerResidues hk) s
  rw [min_eq_left hsize] at hh
  simpa only [ZMod.card] using hh

theorem prime_sum_powers_length {k s p : ℕ} (hp : p.Prime) (hk : 0 < k)
    (hks : k ≤ s) (n : ZMod p) :
    ∃ x : Fin s → ZMod p,∑ i,(x i)^k=n := by
  letI : Fact p.Prime := ⟨hp⟩
  classical
  have hn : n ∈ iteratedSumset (powerResidues k p) s := by
    rw [iterated_powerResidues_eq_univ_of_le hp hk hks]
    exact Finset.mem_univ _
  obtain ⟨y,hy,hys⟩ := (mem_iteratedSumset_iff _ _ _).mp hn
  have hx : ∀ i : Fin s,∃ x : ZMod p,x^k=y i := by
    intro i
    obtain ⟨x,_,hx⟩ := Finset.mem_image.mp (hy i)
    exact ⟨x,hx⟩
  choose x hx using hx
  exact ⟨x,by simpa only [hx] using hys⟩

theorem prime_sum_powers_length_with_unit {k s p : ℕ} (hp : p.Prime) (hk : 0 < k)
    (hks : k ≤ s) (n : ZMod p) :
    ∃ x : Fin (s+1) → ZMod p,x 0=1 ∧ ∑ i,(x i)^k=n := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x,hx⟩ := prime_sum_powers_length hp hk hks (n-1)
  refine ⟨Fin.cons 1 x,rfl,?_⟩
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero,one_pow,Fin.cons_succ,hx]
  ring

#print axioms prime_sum_powers
#print axioms prime_sum_powers_with_unit
end Waring.LocalSolubility
