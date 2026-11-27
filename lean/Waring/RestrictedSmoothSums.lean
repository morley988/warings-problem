import Waring.RestrictedSmoothOrdered
import Waring.PrimeSupportedCount
import Waring.EvenMoments

/-!
# Exact smooth-sum decomposition by prime support

The prime partition is used as a bijection, so these are identities of
the actual complex sums. No pointwise subsum norm inequality is invoked.
-/

noncomputable section
open scoped BigOperators
namespace Waring.RestrictedSmoothFactorization
open SmoothMoments

def primeSplitDomain (P R : ℝ) (S : ℕ → Prop) : Finset (ℕ × ℕ) := by
  classical
  exact (smoothNumbers P R ×ˢ smoothNumbers P R).filter (fun p =>
    p.1*p.2 ≤ ⌊P⌋₊ ∧ PrimeRestricted S p.1 ∧ PrimeRestricted (fun q => ¬S q) p.2)

theorem smooth_of_dvd {n m : ℕ} {R : ℝ} (hn : IsSmooth n R) (h : m ∣ n) :
    IsSmooth m R := fun q hq hqm => hn q hq (hqm.trans h)

theorem smooth_mul {n m : ℕ} {R : ℝ} (hn : IsSmooth n R) (hm : IsSmooth m R) :
    IsSmooth (n*m) R := by
  intro q hq hdiv
  exact (hq.dvd_mul.mp hdiv).elim (hn q hq) (hm q hq)

theorem primeSplit_product_mem {P R : ℝ} {S : ℕ → Prop} {p : ℕ × ℕ}
    (hp : p ∈ primeSplitDomain P R S) : p.1*p.2 ∈ smoothNumbers P R := by
  classical
  rcases Finset.mem_filter.mp hp with ⟨hp,hprod,hs,ht⟩
  rcases Finset.mem_product.mp hp with ⟨hu,hv⟩
  rcases mem_smoothNumbers.mp hu with ⟨⟨hu0,huP⟩,huR⟩
  rcases mem_smoothNumbers.mp hv with ⟨⟨hv0,hvP⟩,hvR⟩
  exact mem_smoothNumbers.mpr ⟨⟨Nat.mul_pos hu0 hv0,hprod⟩,smooth_mul huR hvR⟩

theorem primeSplit_product_injOn (P R : ℝ) (S : ℕ → Prop) :
    Set.InjOn (fun p : ℕ × ℕ => p.1*p.2) (↑(primeSplitDomain P R S) : Set (ℕ × ℕ)) := by
  classical
  intro p hp q hq heq
  rcases Finset.mem_filter.mp hp with ⟨hp,_,hs,ht⟩
  rcases Finset.mem_filter.mp hq with ⟨hq,_,hs',ht'⟩
  have hp0 := (mem_smoothNumbers.mp (Finset.mem_product.mp hp).1).1.1
  have he := prime_partition_unique hp0 heq hs ht hs' ht'
  exact Prod.ext he.1 he.2

theorem primeSplit_product_surjective {P R : ℝ} (S : ℕ → Prop) {n : ℕ}
    (hn : n ∈ smoothNumbers P R) :
    ∃ p ∈ primeSplitDomain P R S, p.1*p.2=n := by
  classical
  rcases mem_smoothNumbers.mp hn with ⟨⟨hn0,hnP⟩,hnR⟩
  obtain ⟨u,v,hnuv,hu,hv⟩ := exists_prime_partition S n hn0
  have hu0 : 0 < u := by
    by_contra h
    have he : u=0 := by omega
    simp [he] at hnuv
    omega
  have hv0 : 0 < v := by
    by_contra h
    have he : v=0 := by omega
    simp [he] at hnuv
    omega
  have hud : u ∣ n := by rw [hnuv]; exact dvd_mul_right _ _
  have hvd : v ∣ n := by rw [hnuv]; exact dvd_mul_left _ _
  have huP : u ≤ ⌊P⌋₊ := (Nat.le_of_dvd hn0 hud).trans hnP
  have hvP : v ≤ ⌊P⌋₊ := (Nat.le_of_dvd hn0 hvd).trans hnP
  refine ⟨(u,v),Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_,?_⟩,
    hnuv ▸ hnP,hu,hv⟩,hnuv.symm⟩
  · exact mem_smoothNumbers.mpr ⟨⟨hu0,huP⟩,smooth_of_dvd hnR hud⟩
  · exact mem_smoothNumbers.mpr ⟨⟨hv0,hvP⟩,smooth_of_dvd hnR hvd⟩

theorem primeSplit_product_image (P R : ℝ) (S : ℕ → Prop) :
    (primeSplitDomain P R S).image (fun p => p.1*p.2) = smoothNumbers P R := by
  ext n
  constructor
  · intro hn
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
    exact primeSplit_product_mem hp
  · intro hn
    obtain ⟨p,hp,he⟩ := primeSplit_product_surjective S hn
    exact Finset.mem_image.mpr ⟨p,hp,he⟩

/-- Exact weighted prime partition, including arbitrary complex phases. -/
theorem smooth_sum_prime_partition {A : Type*} [AddCommMonoid A]
    (P R : ℝ) (S : ℕ → Prop) (f : ℕ → A) :
    (∑ n ∈ smoothNumbers P R, f n) =
      ∑ p ∈ primeSplitDomain P R S, f (p.1*p.2) := by
  rw [← primeSplit_product_image P R S]
  exact Finset.sum_image (fun p hp q hq he => primeSplit_product_injOn P R S hp hq he)

theorem primeRestricted_not_dvd_iff_coprime (q n : ℕ) :
    PrimeRestricted (fun p => ¬p ∣ q) n ↔ n.Coprime q := by
  constructor
  · intro h
    exact Nat.coprime_of_dvd (fun p hp hpn hpq => h p hp hpn hpq)
  · intro h p hp hpn hpq
    exact Nat.not_coprime_of_dvd_of_dvd hp.one_lt hpn hpq h

def supportedCoprimeDomain (q : ℕ) (P R : ℝ) : Finset (ℕ × ℕ) := by
  classical
  exact (smoothNumbers P R ×ˢ smoothNumbers P R).filter (fun p =>
    p.1*p.2 ≤ ⌊P⌋₊ ∧ PrimeSupportedCount.IsPrimeSupported p.1 q ∧ p.2.Coprime q)

theorem supportedCoprimeDomain_eq (q : ℕ) (P R : ℝ) :
    supportedCoprimeDomain q P R=primeSplitDomain P R (fun p => p ∣ q) := by
  classical
  ext p
  simp only [supportedCoprimeDomain,primeSplitDomain,Finset.mem_filter,
    primeRestricted_not_dvd_iff_coprime]
  rfl

/-- The q-supported factor and q-coprime factor give the literal original
smooth Weyl sum at every real alpha. -/
theorem smoothWeyl_supported_coprime (k q : ℕ) (P R α : ℝ) :
    smoothWeyl k P R α =
      ∑ p ∈ supportedCoprimeDomain q P R, phase k (p.1*p.2) α := by
  rw [supportedCoprimeDomain_eq]
  exact smooth_sum_prime_partition P R (fun p => p ∣ q) (fun n => phase k n α)

#print axioms smooth_sum_prime_partition
#print axioms smoothWeyl_supported_coprime
end Waring.RestrictedSmoothFactorization
