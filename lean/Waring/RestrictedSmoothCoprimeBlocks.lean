import Waring.RestrictedSmoothBlocks
import Waring.RestrictedSmoothCommutation
import Waring.RestrictedSmoothSmall

/-! # The literal coprime ordered-block decomposition -/

noncomputable section
open scoped BigOperators
namespace Waring.RestrictedSmoothFactorization
open SmoothMoments

theorem mul_le_floor_div_iff {P : ℝ} (hP : 0 ≤ P) {m n : ℕ} (hm : 0 < m) :
    m*n ≤ ⌊P⌋₊ ↔ n ≤ ⌊P/(m : ℝ)⌋₊ := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  rw [Nat.le_floor_iff hP,Nat.le_floor_iff (div_nonneg hP hmR.le),
    le_div_iff₀ hmR]
  push_cast
  rw [mul_comm]

def coprimeBlocks (q : ℕ) (M R : ℝ) : Finset (ℕ × ℕ) :=
  (orderedBlocks M R).filter (fun p => p.2.Coprime q)

def largeCoprimeDomain (q : ℕ) (P R M : ℝ) : Finset (ℕ × ℕ) :=
  (supportedCoprimeDomain q P R).filter (fun p => M < (p.2 : ℝ))

abbrev CoprimeBlockLabel := Σ _ : ℕ × ℕ, ℕ × ℕ

def coprimeBlockDomain (q : ℕ) (P R M : ℝ) : Finset CoprimeBlockLabel := by
  classical
  exact (coprimeBlocks q M R).sigma (fun b =>
    mixedPrimeDomain (P/(b.2 : ℝ)) R (fun l => l ∣ q) (fun l => l ≤ b.1))

def coprimeBlockDecode (p : CoprimeBlockLabel) : ℕ × ℕ :=
  (p.2.1,p.1.2*p.2.2)

theorem coprimeBlock_window {q : ℕ} {P R M : ℝ} {p : CoprimeBlockLabel}
    (hp : p ∈ coprimeBlockDomain q P R M) : OrderedWindow M p.1.1 p.1.2 p.2.2 := by
  classical
  rcases Finset.mem_sigma.mp hp with ⟨hb,hp⟩
  rcases Finset.mem_filter.mp hb with ⟨hb,_⟩
  rcases Finset.mem_filter.mp hb with ⟨_,hπ,hdiv,hlo,hhi,hrough⟩
  rcases Finset.mem_filter.mp hp with ⟨hp,hsmall⟩
  have hw := (mem_smoothNumbers.mp (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).2).1.1
  refine ⟨hπ,hdiv,hw,hlo,hhi,hrough,?_⟩
  intro l hl hld
  exact_mod_cast hsmall l hl hld

theorem coprimeBlockDecode_mem {q : ℕ} {P R M : ℝ} (hP : 0 ≤ P) (hM : 1 ≤ M)
    {p : CoprimeBlockLabel} (hp : p ∈ coprimeBlockDomain q P R M) :
    coprimeBlockDecode p ∈ largeCoprimeDomain q P R M := by
  classical
  have hwin := coprimeBlock_window hp
  have hm0 := orderedWindow_m_pos hM hwin
  rcases Finset.mem_sigma.mp hp with ⟨hb,hp⟩
  rcases Finset.mem_filter.mp hb with ⟨hb,hmc⟩
  have hmR := (mem_smoothNumbers.mp (Finset.mem_product.mp (Finset.mem_filter.mp hb).1).2).2
  rcases Finset.mem_filter.mp hp with ⟨hp,_⟩
  rcases Finset.mem_filter.mp hp with ⟨hp,huw,huq,hwq⟩
  rcases Finset.mem_product.mp hp with ⟨hu,hw⟩
  have hu := mem_smoothNumbers.mp hu
  have hw := mem_smoothNumbers.mp hw
  have htot : p.1.2*(p.2.1*p.2.2) ≤ ⌊P⌋₊ := (mul_le_floor_div_iff hP hm0).mpr huw
  have hvP : p.1.2*p.2.2 ≤ ⌊P⌋₊ :=
    (Nat.mul_le_mul_left p.1.2 (Nat.le_mul_of_pos_left p.2.2 hu.1.1)).trans htot
  have huP : p.2.1 ≤ ⌊P⌋₊ := by
    calc
      _ ≤ p.2.1*p.2.2 := Nat.le_mul_of_pos_right _ hw.1.1
      _ ≤ p.1.2*(p.2.1*p.2.2) := Nat.le_mul_of_pos_left _ hm0
      _ ≤ _ := htot
  refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
    ⟨mem_smoothNumbers.mpr ⟨⟨hu.1.1,huP⟩,hu.2⟩,
      mem_smoothNumbers.mpr ⟨⟨Nat.mul_pos hm0 hw.1.1,hvP⟩,smooth_mul hmR hw.2⟩⟩,
      ?_,huq,?_⟩,?_⟩
  · change p.2.1*(p.1.2*p.2.2) ≤ ⌊P⌋₊
    convert htot using 1 <;> ring
  · exact Nat.coprime_mul_iff_left.mpr
      ⟨hmc,(primeRestricted_not_dvd_iff_coprime q p.2.2).mp hwq⟩
  · change M < ((p.1.2*p.2.2 : ℕ) : ℝ)
    have hh : (p.1.2 : ℝ) ≤ (p.1.2 : ℝ)*(p.2.2 : ℝ) :=
      le_mul_of_one_le_right (Nat.cast_nonneg _) (by exact_mod_cast hw.1.1)
    push_cast
    exact hwin.2.2.2.1.trans_le hh

theorem coprimeBlockDecode_injOn {q : ℕ} {P R M : ℝ} (hM : 1 ≤ M) :
    Set.InjOn coprimeBlockDecode (↑(coprimeBlockDomain q P R M) : Set CoprimeBlockLabel) := by
  intro p hp r hr he
  have hu := congrArg Prod.fst he
  have hprod := congrArg Prod.snd he
  obtain ⟨hπ,hm,hw⟩ := orderedWindow_unique hM (coprimeBlock_window hp)
    (coprimeBlock_window hr) hprod
  rcases p with ⟨⟨π,m⟩,⟨u,w⟩⟩
  rcases r with ⟨⟨π',m'⟩,⟨u',w'⟩⟩
  simp only [coprimeBlockDecode] at hu
  dsimp at hπ hm hw
  subst π'; subst m'; subst u'; subst w'
  rfl

theorem coprimeBlockDecode_surjective {q : ℕ} {P R M : ℝ}
    (hP : 0 ≤ P) (hM : 1 ≤ M) {p : ℕ × ℕ}
    (hp : p ∈ largeCoprimeDomain q P R M) :
    ∃ t ∈ coprimeBlockDomain q P R M, coprimeBlockDecode t=p := by
  classical
  rcases Finset.mem_filter.mp hp with ⟨hp,hlarge⟩
  rcases Finset.mem_filter.mp hp with ⟨hp,hprod,huq,hvq⟩
  rcases Finset.mem_product.mp hp with ⟨hu,hv⟩
  obtain ⟨t,ht,he⟩ := orderedTriple_product_surjective hM hv hlarge
  have hwin := orderedTriple_window ht
  have hm0 := orderedWindow_m_pos hM hwin
  rcases Finset.mem_filter.mp ht with ⟨ht,_,hwt⟩
  rcases Finset.mem_product.mp ht with ⟨hb,hw⟩
  have hcw : t.1.2.Coprime q ∧ t.2.Coprime q := by
    rw [← Nat.coprime_mul_iff_left,he]
    exact hvq
  have hu' := mem_smoothNumbers.mp hu
  have hw' := mem_smoothNumbers.mp hw
  have huw : p.1*t.2 ≤ ⌊P/(t.1.2 : ℝ)⌋₊ := by
    apply (mul_le_floor_div_iff hP hm0).mp
    calc
      _ = p.1*(t.1.2*t.2) := by ring
      _ ≤ _ := he ▸ hprod
  have huP : p.1 ≤ ⌊P/(t.1.2 : ℝ)⌋₊ :=
    (Nat.le_mul_of_pos_right _ hw'.1.1).trans huw
  have hwP : t.2 ≤ ⌊P/(t.1.2 : ℝ)⌋₊ :=
    (Nat.le_mul_of_pos_left _ hu'.1.1).trans huw
  refine ⟨⟨t.1,(p.1,t.2)⟩,Finset.mem_sigma.mpr ⟨Finset.mem_filter.mpr ⟨hb,hcw.1⟩,
    Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨mem_smoothNumbers.mpr ⟨⟨hu'.1.1,huP⟩,hu'.2⟩,
       mem_smoothNumbers.mpr ⟨⟨hw'.1.1,hwP⟩,hw'.2⟩⟩,
      huw,huq,(primeRestricted_not_dvd_iff_coprime q t.2).mpr hcw.2⟩,?_⟩⟩,?_⟩
  · intro l hl hld
    exact_mod_cast hwt l hl hld
  · exact Prod.ext rfl he

/-- The actual large coprime branch is the sum of the actual mixed-prime
block sums. Each original term occurs exactly once. -/
theorem largeCoprime_sum_blocks {A : Type*} [AddCommMonoid A]
    {q : ℕ} {P R M : ℝ} (hP : 0 ≤ P) (hM : 1 ≤ M) (f : ℕ × ℕ → A) :
    (∑ p ∈ largeCoprimeDomain q P R M, f p) =
      ∑ b ∈ coprimeBlocks q M R,
        ∑ p ∈ mixedPrimeDomain (P/(b.2 : ℝ)) R (fun l => l ∣ q) (fun l => l ≤ b.1),
          f (p.1,b.2*p.2) := by
  classical
  calc
    _ = ∑ t ∈ coprimeBlockDomain q P R M, f (coprimeBlockDecode t) := by
      symm
      apply Finset.sum_bij (fun t _ => coprimeBlockDecode t)
      · exact fun _ ht => coprimeBlockDecode_mem hP hM ht
      · exact fun _ ht _ hu he => coprimeBlockDecode_injOn hM ht hu he
      · intro p hp
        obtain ⟨t,ht,he⟩ := coprimeBlockDecode_surjective hP hM hp
        exact ⟨t,ht,he⟩
      · exact fun _ _ => rfl
    _ = _ := by simp only [coprimeBlockDomain,Finset.sum_sigma,coprimeBlockDecode]

#print axioms largeCoprime_sum_blocks
end Waring.RestrictedSmoothFactorization
