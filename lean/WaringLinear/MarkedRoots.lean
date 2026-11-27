import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! # Marked roots and uniqueness of their positive coefficients

A marked root consists of one prime from each of several disjoint
windows and a smaller positive cofactor. Divisibility by a distinguished
prime is precisely equality in its marked coordinate.
-/

open scoped BigOperators
namespace WaringLinear

theorem marked_prime_divides_iff {ι : Type*} [Fintype ι]
    (p q : ℕ) (m : ι → ℕ) (hp : p.Prime) (hm : ∀ i, (m i).Prime)
    (hq : ¬p∣q) : p ∣ q*(∏ i, m i) ↔ ∃ i, m i=p := by
  constructor
  · intro h
    have hprod := (hp.dvd_mul.mp h).resolve_left hq
    obtain ⟨i,_,hi⟩ := (hp.prime.dvd_finset_prod_iff m).mp hprod
    exact ⟨i,((hm i).dvd_iff_eq hp.ne_one).mp hi⟩
  · rintro ⟨i,rfl⟩
    exact dvd_trans (Finset.dvd_prod_of_mem m (Finset.mem_univ i)) (dvd_mul_left _ _)

theorem marked_coordinate_divides_iff {ι : Type*} [Fintype ι]
    (j : ι) (p q : ℕ) (m : ι → ℕ) (hp : p.Prime) (hm : ∀ i, (m i).Prime)
    (hq : ¬p∣q) (hwin : ∀ i, m i=p → i=j) :
    p ∣ q*(∏ i, m i) ↔ m j=p := by
  rw [marked_prime_divides_iff p q m hp hm hq]
  constructor
  · rintro ⟨i,hi⟩
    simpa only [←hwin i hi] using hi
  · exact fun h => ⟨j,h⟩

theorem marked_product_unique {ι : Type*} [Fintype ι]
    (m n : ι → ℕ) (q r : ℕ) (hm : ∀ i, (m i).Prime) (hn : ∀ i, (n i).Prime)
    (hsmall : ∀ i, ¬m i∣r) (hwin : ∀ i j, n j=m i → j=i)
    (heq : q*(∏ i, m i)=r*(∏ i, n i)) : m=n ∧ q=r := by
  have hall : m=n := by
    funext i
    apply Eq.symm
    apply (marked_coordinate_divides_iff i (m i) r n (hm i) hn (hsmall i) (hwin i)).mp
    rw [←heq]
    exact dvd_trans (Finset.dvd_prod_of_mem m (Finset.mem_univ i)) (dvd_mul_left _ _)
  refine ⟨hall,?_⟩
  rw [hall] at heq
  exact Nat.eq_of_mul_eq_mul_right (Finset.prod_pos (fun i _ => (hn i).pos)) heq

/-- Coefficients obtained by counting all factorizations of a root are at most one. -/
theorem marked_root_injective {ι : Type*} [Fintype ι]
    (W : ι → Type*) (z : Type*) (primeIn : ∀ i, W i → ℕ) (bottom : z → ℕ)
    (hp : ∀ i u, (primeIn i u).Prime) (hi : ∀ i, Function.Injective (primeIn i))
    (hz : Function.Injective bottom)
    (hsmall : ∀ i u v, ¬primeIn i u ∣ bottom v)
    (hdis : ∀ i j u v, primeIn j v=primeIn i u → j=i) :
    Function.Injective (fun data : (∀ i, W i) × z =>
      bottom data.2 * ∏ i, primeIn i (data.1 i)) := by
  rintro ⟨a,b⟩ ⟨c,d⟩ heq
  obtain ⟨ha,hb⟩ := marked_product_unique
    (fun i => primeIn i (a i)) (fun i => primeIn i (c i)) (bottom b) (bottom d)
    (fun i => hp i _) (fun i => hp i _) (fun i => hsmall i _ _)
    (fun i j => hdis i j _ _) heq
  apply Prod.ext
  · funext i
    exact hi i (congrFun ha i)
  · exact hz hb

#print axioms marked_root_injective
#print axioms marked_coordinate_divides_iff
end WaringLinear
