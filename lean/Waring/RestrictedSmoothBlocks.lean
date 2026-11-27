import Waring.RestrictedSmoothSums

/-! # Literal ordered smooth blocks and their exact decomposition -/

noncomputable section
open scoped BigOperators
namespace Waring.RestrictedSmoothFactorization
open SmoothMoments

def orderedBlocks (M R : ℝ) : Finset (ℕ × ℕ) := by
  classical
  exact (Finset.Icc 2 ⌊R⌋₊ ×ˢ smoothNumbers (M*R) R).filter (fun p =>
    p.1.Prime ∧ p.1 ∣ p.2 ∧ M < (p.2 : ℝ) ∧ (p.2 : ℝ) ≤ M*(p.1 : ℝ) ∧
      PrimeRestricted (fun l => p.1 ≤ l) p.2)

theorem orderedBlocks_prime_minFac {M R : ℝ} (hM : 1 ≤ M) {p : ℕ × ℕ}
    (hp : p ∈ orderedBlocks M R) : p.1=p.2.minFac := by
  classical
  rcases Finset.mem_filter.mp hp with ⟨hp,hprime,hdiv,hlo,hhi,hrough⟩
  have hm1 : p.2 ≠ 1 := by intro he; simp [he] at hlo; linarith
  exact le_antisymm (hrough _ (Nat.minFac_prime hm1) (Nat.minFac_dvd _))
    (Nat.minFac_le_of_dvd hprime.two_le hdiv)

theorem orderedBlocks_card_le {M R : ℝ} (hM : 1 ≤ M) (hMR : 0 ≤ M*R) :
    ((orderedBlocks M R).card : ℝ) ≤ M*R := by
  classical
  have hinj : Set.InjOn Prod.snd (↑(orderedBlocks M R) : Set (ℕ × ℕ)) := by
    intro p hp q hq he
    apply Prod.ext _ he
    rw [orderedBlocks_prime_minFac hM hp,orderedBlocks_prime_minFac hM hq,he]
  have hcard : (orderedBlocks M R).card ≤ (smoothNumbers (M*R) R).card :=
    Finset.card_le_card_of_injOn Prod.snd
      (fun p hp => (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).2) hinj
  exact (Nat.cast_le.mpr (hcard.trans (smoothNumbers_card_le _ _))).trans (Nat.floor_le hMR)

def orderedTripleDomain (P R M : ℝ) : Finset ((ℕ × ℕ) × ℕ) := by
  classical
  exact (orderedBlocks M R ×ˢ smoothNumbers P R).filter (fun p =>
    p.1.2*p.2 ≤ ⌊P⌋₊ ∧ IsSmooth p.2 (p.1.1 : ℝ))

theorem orderedTriple_window {P R M : ℝ} {p : (ℕ × ℕ) × ℕ}
    (hp : p ∈ orderedTripleDomain P R M) : OrderedWindow M p.1.1 p.1.2 p.2 := by
  classical
  rcases Finset.mem_filter.mp hp with ⟨hp,_,hwπ⟩
  rcases Finset.mem_product.mp hp with ⟨hblock,hw⟩
  rcases Finset.mem_filter.mp hblock with ⟨_,hπ,hπm,hMm,hmM,hrough⟩
  exact ⟨hπ,hπm,(mem_smoothNumbers.mp hw).1.1,hMm,hmM,hrough,hwπ⟩

theorem orderedTriple_product_mem {P R M : ℝ} (hM : 1 ≤ M) {p : (ℕ × ℕ) × ℕ}
    (hp : p ∈ orderedTripleDomain P R M) :
    p.1.2*p.2 ∈ smoothNumbers P R ∧ M < ((p.1.2*p.2 : ℕ) : ℝ) := by
  classical
  have hw := orderedTriple_window hp
  rcases Finset.mem_filter.mp hp with ⟨hp,hprod,hwπ⟩
  rcases Finset.mem_product.mp hp with ⟨hb,hv⟩
  have hm := (mem_smoothNumbers.mp (Finset.mem_product.mp (Finset.mem_filter.mp hb).1).2)
  have hv := mem_smoothNumbers.mp hv
  refine ⟨mem_smoothNumbers.mpr ⟨⟨Nat.mul_pos hm.1.1 hv.1.1,hprod⟩,
    smooth_mul hm.2 hv.2⟩,?_⟩
  have hv1 : (1 : ℝ) ≤ p.2 := by exact_mod_cast hv.1.1
  have hm0 : (0 : ℝ) ≤ p.1.2 := Nat.cast_nonneg _
  have hmul := le_mul_of_one_le_right hm0 hv1
  push_cast
  exact hw.2.2.2.1.trans_le hmul

theorem orderedTriple_product_injOn {P R M : ℝ} (hM : 1 ≤ M) :
    Set.InjOn (fun p : (ℕ × ℕ) × ℕ => p.1.2*p.2)
      (↑(orderedTripleDomain P R M) : Set ((ℕ × ℕ) × ℕ)) := by
  intro p hp q hq he
  obtain ⟨hπ,hm,hw⟩ := orderedWindow_unique hM
    (orderedTriple_window hp) (orderedTriple_window hq) he
  exact Prod.ext (Prod.ext hπ hm) hw

theorem orderedTriple_product_surjective {P R M : ℝ} (hM : 1 ≤ M) {n : ℕ}
    (hn : n ∈ smoothNumbers P R) (hnM : M < (n : ℝ)) :
    ∃ p ∈ orderedTripleDomain P R M, p.1.2*p.2=n := by
  classical
  obtain ⟨π,m,w,hnmw,hw⟩ := exists_orderedWindow n hM hnM
  have hn' := mem_smoothNumbers.mp hn
  have hmpos := orderedWindow_m_pos hM hw
  have hmd : m ∣ n := by rw [hnmw]; exact dvd_mul_right _ _
  have hwd : w ∣ n := by rw [hnmw]; exact dvd_mul_left _ _
  have hπR : (π : ℝ) ≤ R := hn'.2 π hw.1 (hw.2.1.trans hmd)
  have hmMR : (m : ℝ) ≤ M*R := hw.2.2.2.2.1.trans
    (mul_le_mul_of_nonneg_left hπR (zero_le_one.trans hM))
  have hmR : m ∈ smoothNumbers (M*R) R :=
    mem_smoothNumbers.mpr ⟨⟨hmpos,Nat.le_floor hmMR⟩,smooth_of_dvd hn'.2 hmd⟩
  have hwP : w ∈ smoothNumbers P R := mem_smoothNumbers.mpr
    ⟨⟨hw.2.2.1,(Nat.le_of_dvd hn'.1.1 hwd).trans hn'.1.2⟩,smooth_of_dvd hn'.2 hwd⟩
  have hblock : (π,m) ∈ orderedBlocks M R := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨hw.1.two_le,Nat.le_floor hπR⟩,hmR⟩,
      hw.1,hw.2.1,hw.2.2.2.1,hw.2.2.2.2.1,hw.2.2.2.2.2.1⟩
  exact ⟨((π,m),w),Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hblock,hwP⟩,
    hnmw ▸ hn'.1.2,hw.2.2.2.2.2.2⟩,hnmw.symm⟩

theorem orderedTriple_product_image {P R M : ℝ} (hM : 1 ≤ M) :
    (orderedTripleDomain P R M).image (fun p => p.1.2*p.2) =
      (smoothNumbers P R).filter (fun n : ℕ => M < (n : ℝ)) := by
  classical
  ext n
  constructor
  · intro hn
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
    exact Finset.mem_filter.mpr (orderedTriple_product_mem hM hp)
  · intro hn
    obtain ⟨hn,hM⟩ := Finset.mem_filter.mp hn
    obtain ⟨p,hp,he⟩ := orderedTriple_product_surjective ‹1 ≤ M› hn hM
    exact Finset.mem_image.mpr ⟨p,hp,he⟩

/-- Exact decomposition of the large smooth variables into the source
ordered block and its smaller-prime complement. -/
theorem smooth_large_ordered_sum {A : Type*} [AddCommMonoid A] {P R M : ℝ}
    (hM : 1 ≤ M) (f : ℕ → A) :
    (∑ n ∈ (smoothNumbers P R).filter (fun n : ℕ => M < (n : ℝ)), f n) =
      ∑ p ∈ orderedTripleDomain P R M, f (p.1.2*p.2) := by
  classical
  rw [← orderedTriple_product_image hM]
  exact Finset.sum_image (fun p hp q hq he => orderedTriple_product_injOn hM hp hq he)

#print axioms orderedBlocks_card_le
#print axioms smooth_large_ordered_sum
end Waring.RestrictedSmoothFactorization
