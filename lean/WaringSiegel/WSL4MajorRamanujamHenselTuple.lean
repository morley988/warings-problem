import WaringSiegel.WSL4MajorRamanujamHensel

/-! # Sharp lifting of a power-sum congruence, including in actual completions -/
noncomputable section
set_option maxHeartbeats 900000
open IsLocalRing
open scoped NumberField BigOperators Classical
namespace WaringSiegel.WSL4

variable {A : Type*} [CommRing A] [IsLocalRing A]
  [IsAdicComplete (maximalIdeal A) A]

theorem nat_isUnit_of_residue_prime_not_dvd (p n : ℕ)
    [CharP (ResidueField A) p] (hn : ¬ p ∣ n) : IsUnit (n:A) := by
  apply (residue_ne_zero_iff_isUnit _).mp
  rw [map_natCast]
  exact fun h => hn ((CharP.cast_eq_zero_iff (ResidueField A) p n).mp h)

theorem power_tuple_lift_sharp (p n r : ℕ) (hp : p.Prime)
    [CharP (ResidueField A) p] (hn : IsUnit (n:A))
    {s : ℕ} (x : Fin s → A) (a : A) (hunit : ∃ j, IsUnit (x j))
    (ha : (p:A)^(ramanujamLiftPrecision p r) ∣ a-∑ i,x i^(n*p^r)) :
    ∃ y : Fin s → A,
      (∑ i,y i^(n*p^r))=a ∧ (∃ j, IsUnit (y j)) ∧ ∀ i,(p:A) ∣ y i-x i := by
  obtain ⟨j,hj⟩ := hunit
  let b := a-∑ i∈Finset.univ.erase j,x i^(n*p^r)
  have hb : b-x j^(n*p^r)=a-∑ i,x i^(n*p^r) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
    dsimp [b]
    ring
  obtain ⟨z,hz,hzp,hzu⟩ := power_root_of_dvd_sharp p n r hp hn (x j) b hj
    (hb.symm ▸ ha)
  refine ⟨Function.update x j z,?_,⟨j,by simpa using hzu⟩,?_⟩
  · have he : (fun i => (Function.update x j z i)^(n*p^r))=
        Function.update (fun i => x i^(n*p^r)) j (z^(n*p^r)) := by
      ext i
      by_cases hi : i=j <;> simp only [Function.update_apply,hi,if_true,if_false]
    rw [he,Finset.sum_update_of_mem (Finset.mem_univ j),hz]
    simp only [b,Finset.sdiff_singleton_eq_erase]
    abel
  · intro i
    by_cases hi : i=j
    · subst i
      simpa using hzp
    · simp only [Function.update_of_ne hi,sub_self,dvd_zero]

theorem power_tuple_lift_sharp_of_not_dvd (p n r : ℕ) (hp : p.Prime)
    [CharP (ResidueField A) p] (hn : ¬ p ∣ n)
    {s : ℕ} (x : Fin s → A) (a : A) (hunit : ∃ j, IsUnit (x j))
    (ha : (p:A)^(ramanujamLiftPrecision p r) ∣ a-∑ i,x i^(n*p^r)) :
    ∃ y : Fin s → A, (∑ i,y i^(n*p^r))=a ∧ ∃ j,IsUnit (y j) := by
  obtain ⟨y,hy,hu,-⟩ := power_tuple_lift_sharp p n r hp
    (nat_isUnit_of_residue_prime_not_dvd p n hn) x a hunit ha
  exact ⟨y,hy,hu⟩

theorem completion_power_root_of_dvd_sharp
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (p n r : ℕ) (hp : p.Prime)
    [CharP (ResidueField (v.adicCompletionIntegers K)) p] (hn : ¬ p ∣ n)
    (z a : v.adicCompletionIntegers K) (hz : IsUnit z)
    (ha : (p:v.adicCompletionIntegers K)^(ramanujamLiftPrecision p r) ∣ a-z^(n*p^r)) :
    ∃ y : v.adicCompletionIntegers K,
      y^(n*p^r)=a ∧ (p:v.adicCompletionIntegers K) ∣ y-z ∧ IsUnit y := by
  letI := completionIntegers_isAdicComplete v
  exact power_root_of_dvd_sharp p n r hp
    (nat_isUnit_of_residue_prime_not_dvd p n hn) z a hz ha

theorem completion_power_tuple_lift_sharp
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (p n r : ℕ) (hp : p.Prime)
    [CharP (ResidueField (v.adicCompletionIntegers K)) p] (hn : ¬ p ∣ n)
    {s : ℕ} (x : Fin s → v.adicCompletionIntegers K)
    (a : v.adicCompletionIntegers K) (hunit : ∃ j,IsUnit (x j))
    (ha : (p:v.adicCompletionIntegers K)^(ramanujamLiftPrecision p r) ∣ a-∑ i,x i^(n*p^r)) :
    ∃ y : Fin s → v.adicCompletionIntegers K,
      (∑ i,y i^(n*p^r))=a ∧ ∃ j,IsUnit (y j) := by
  letI := completionIntegers_isAdicComplete v
  exact power_tuple_lift_sharp_of_not_dvd p n r hp hn x a hunit ha

#print axioms power_tuple_lift_sharp
#print axioms completion_power_root_of_dvd_sharp
#print axioms completion_power_tuple_lift_sharp
end WaringSiegel.WSL4
