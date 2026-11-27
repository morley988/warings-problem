import Waring.RestrictedSmoothSums

/-!
# Commuting prime partitions in the actual smooth sum

The q-supported/coprime split and the small-prime/large-prime split enumerate
the same integers. This is the finite identity behind BW2023 Lemma4.1.
-/

noncomputable section
open scoped BigOperators
namespace Waring.RestrictedSmoothFactorization
open SmoothMoments

theorem primeRestricted_or_mul_iff {S T : ℕ → Prop} {a b : ℕ}
    (hS : PrimeRestricted S a) (hnotS : PrimeRestricted (fun p => ¬S p) b) :
    PrimeRestricted (fun p => S p ∨ T p) (a*b) ↔ PrimeRestricted T b := by
  constructor
  · intro h p hp hpb
    exact (h p hp (hpb.trans (dvd_mul_left b a))).resolve_left (hnotS p hp hpb)
  · intro h p hp hpab
    exact (hp.dvd_mul.mp hpab).elim (fun hpa => Or.inl (hS p hp hpa))
      (fun hpb => Or.inr (h p hp hpb))

def mixedPrimeDomain (P R : ℝ) (S T : ℕ → Prop) : Finset (ℕ × ℕ) := by
  classical
  exact (primeSplitDomain P R S).filter (fun p => PrimeRestricted T p.2)

def unionPrimeSmooth (P R : ℝ) (S T : ℕ → Prop) : Finset ℕ := by
  classical
  exact (smoothNumbers P R).filter (fun n => PrimeRestricted (fun p => S p ∨ T p) n)

theorem mixedPrime_product_image (P R : ℝ) (S T : ℕ → Prop) :
    (mixedPrimeDomain P R S T).image (fun p => p.1*p.2) = unionPrimeSmooth P R S T := by
  classical
  ext n
  constructor
  · intro hn
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
    rcases Finset.mem_filter.mp hp with ⟨hp,hT⟩
    have hp' := (Finset.mem_filter.mp hp).2
    exact Finset.mem_filter.mpr ⟨primeSplit_product_mem hp,
      (primeRestricted_or_mul_iff hp'.2.1 hp'.2.2).mpr hT⟩
  · intro hn
    rcases Finset.mem_filter.mp hn with ⟨hn,hunion⟩
    obtain ⟨p,hp,he⟩ := primeSplit_product_surjective S hn
    have hp' := (Finset.mem_filter.mp hp).2
    refine Finset.mem_image.mpr ⟨p,Finset.mem_filter.mpr ⟨hp,?_⟩,he⟩
    change PrimeRestricted T p.2
    apply (primeRestricted_or_mul_iff (T := T) hp'.2.1 hp'.2.2).mp
    simpa only [he] using hunion

theorem mixedPrime_sum_eq {A : Type*} [AddCommMonoid A]
    (P R : ℝ) (S T : ℕ → Prop) (f : ℕ → A) :
    (∑ p ∈ mixedPrimeDomain P R S T, f (p.1*p.2)) =
      ∑ n ∈ unionPrimeSmooth P R S T, f n := by
  classical
  rw [← mixedPrime_product_image P R S T]
  symm
  exact Finset.sum_image (fun p hp q hq he => primeSplit_product_injOn P R S
    (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hq).1 he)

theorem unionPrimeSmooth_comm (P R : ℝ) (S T : ℕ → Prop) :
    unionPrimeSmooth P R S T=unionPrimeSmooth P R T S := by
  classical
  simp only [unionPrimeSmooth,PrimeRestricted,or_comm]

/-- Exact rearrangement of the q-supported and prime-threshold factors,
valid for arbitrary weights and hence for the original Fourier phases. -/
theorem mixedPrime_sum_comm {A : Type*} [AddCommMonoid A]
    (P R : ℝ) (S T : ℕ → Prop) (f : ℕ → A) :
    (∑ p ∈ mixedPrimeDomain P R S T, f (p.1*p.2)) =
      ∑ p ∈ mixedPrimeDomain P R T S, f (p.1*p.2) := by
  rw [mixedPrime_sum_eq,mixedPrime_sum_eq,unionPrimeSmooth_comm]

theorem supported_threshold_weyl_identity (k q π : ℕ) (P R α : ℝ) :
    (∑ p ∈ mixedPrimeDomain P R (fun l => l ∣ q) (fun l => l ≤ π),
      phase k (p.1*p.2) α) =
    ∑ p ∈ mixedPrimeDomain P R (fun l => l ≤ π) (fun l => l ∣ q),
      phase k (p.1*p.2) α :=
  mixedPrime_sum_comm P R (fun l => l ∣ q) (fun l => l ≤ π) (fun n => phase k n α)

#print axioms mixedPrime_sum_comm
#print axioms supported_threshold_weyl_identity
end Waring.RestrictedSmoothFactorization
