import Waring.AuxiliaryL2Grouping
import Waring.DifferenceSquaresFibers

/-!
# The same-shift quadratic collision count

After fixing h, the product of the shifts cancels from the positive integer
quadratic frequency. The coefficient zero fiber contributes at most 2|Z|;
nonzero coefficient differences are bounded by an actual signed-divisor
injection for 3(z^2-w^2)=b. Centered intervals, including both signs, are covered.
-/

noncomputable section
open scoped BigOperators
namespace Waring.AuxiliaryL2Counting
open AuxiliaryL2Grouping DifferenceSquaresFibers

def coefficientValue {r : ℕ} (k : ℕ) (h m : Fin r → ℕ) : ℤ :=
  ∑ i, (h i : ℤ)^2*(m i : ℤ)^k

def shiftProduct {r : ℕ} (h : Fin r → ℕ) : ℤ := ∏ i, (h i : ℤ)

def frequency {r : ℕ} (C : ℤ) (k : ℕ) (x : (Fin r → ℕ) × ((Fin r → ℕ) × ℤ)) : ℤ :=
  C*shiftProduct x.1*(3*x.2.2^2+coefficientValue k x.1 x.2.1)

def indexSet {r : ℕ} (H M : Finset (Fin r → ℕ)) (Z : Finset ℤ) := H ×ˢ (M ×ˢ Z)

def squareSlice (Z : Finset ℤ) (b : ℤ) : Finset (ℤ × ℤ) :=
  (Z ×ˢ Z).filter (fun p => 3*(p.1^2-p.2^2)=b)

theorem squareSlice_zero_card_le (Z : Finset ℤ) : (squareSlice Z 0).card ≤ 2*Z.card := by
  have hsub : squareSlice Z 0 ⊆ squareDifferenceFiber Z Z 0 := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hp,hv⟩
    exact Finset.mem_filter.mpr ⟨hp,by omega⟩
  exact (Finset.card_le_card hsub).trans (squareDifferenceFiber_zero_card_le Z Z)

theorem squareSlice_nonzero_card_le (Z : Finset ℤ) {b : ℤ} (hb : b ≠ 0) :
    (squareSlice Z b).card ≤ 2*b.natAbs.divisors.card := by
  apply (Finset.card_le_card_of_injOn (fun p : ℤ × ℤ => p.1-p.2) ?_ ?_).trans
    (card_signedDivisors_le b)
  · intro p hp
    apply mem_signedDivisors hb
    rw [← (Finset.mem_filter.mp hp).2]
    exact dvd_mul_of_dvd_right (sub_dvd_pow_sub_pow p.1 p.2 2) 3
  · intro p hp q hq hd
    have hpv := (Finset.mem_filter.mp hp).2
    have hqv := (Finset.mem_filter.mp hq).2
    have hnz : p.1^2-p.2^2 ≠ 0 := by intro hz; rw [hz,mul_zero] at hpv; exact hb hpv.symm
    exact pair_eq_of_difference_eq hnz rfl (by omega) hd

/-- A uniform P^epsilon bound for every nonzero same-shift quadratic slice. -/
theorem squareSlice_nonzero_polynomial {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P → ∀ Z : Finset ℤ, ∀ b : ℤ,
      b ≠ 0 → (b.natAbs : ℝ) ≤ P^B → ((squareSlice Z b).card : ℝ) ≤ C*P^ε := by
  let δ : ℝ := ε/(B+1)
  have hB1 : 0 < B+1 := by linarith
  have hδ : 0 < δ := div_pos hε hB1
  have hBδ : B*δ ≤ ε := by
    have hid : δ*(B+1)=ε := div_mul_cancel₀ ε hB1.ne'
    nlinarith
  obtain ⟨D,hD,hdiv⟩ := DivisorBound.divisor_count_le_rpow hδ
  refine ⟨2*D,by positivity,?_⟩
  intro P hP Z b hb hbP
  have hcard : ((squareSlice Z b).card : ℝ) ≤ 2*(b.natAbs.divisors.card : ℝ) := by
    exact_mod_cast squareSlice_nonzero_card_le Z hb
  calc
    _ ≤ 2*(b.natAbs.divisors.card : ℝ) := hcard
    _ ≤ 2*(D*(b.natAbs : ℝ)^δ) := mul_le_mul_of_nonneg_left
      (hdiv _ (Int.natAbs_pos.mpr hb)) (by norm_num)
    _ ≤ 2*(D*(P^B)^δ) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hbP hδ.le) hD.le) (by norm_num)
    _ = (2*D)*P^(B*δ) := by rw [← Real.rpow_mul (zero_le_one.trans hP)]; ring
    _ ≤ (2*D)*P^ε := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hP hBδ) (by positivity)

def coefficientZeroPairs {r : ℕ} (k : ℕ) (h : Fin r → ℕ) (M : Finset (Fin r → ℕ)) :=
  (M ×ˢ M).filter (fun mn => coefficientValue k h mn.1=coefficientValue k h mn.2)

def sameShiftPairs {r : ℕ} (k : ℕ) (h : Fin r → ℕ)
    (M : Finset (Fin r → ℕ)) (Z : Finset ℤ) :=
  ((M ×ˢ M) ×ˢ (Z ×ˢ Z)).filter (fun p =>
    3*(p.2.1^2-p.2.2^2)=coefficientValue k h p.1.2-coefficientValue k h p.1.1)

theorem sameShift_card_eq {r : ℕ} (k : ℕ) (h : Fin r → ℕ)
    (M : Finset (Fin r → ℕ)) (Z : Finset ℤ) :
    (sameShiftPairs k h M Z).card = ∑ mn ∈ M ×ˢ M,
      (squareSlice Z (coefficientValue k h mn.2-coefficientValue k h mn.1)).card := by
  simp only [sameShiftPairs,squareSlice,Finset.card_eq_sum_ones,Finset.sum_filter,Finset.sum_product]

theorem sameShift_card_le {r : ℕ} (k : ℕ) (h : Fin r → ℕ)
    (M : Finset (Fin r → ℕ)) (Z : Finset ℤ) {E : ℝ} (hE : 0 ≤ E)
    (hoff : ∀ mn ∈ M ×ˢ M, coefficientValue k h mn.1 ≠ coefficientValue k h mn.2 →
      ((squareSlice Z (coefficientValue k h mn.2-coefficientValue k h mn.1)).card : ℝ) ≤ E) :
    ((sameShiftPairs k h M Z).card : ℝ) ≤
      2*(Z.card : ℝ)*((coefficientZeroPairs k h M).card : ℝ)+E*(M.card : ℝ)^2 := by
  rw [sameShift_card_eq,Nat.cast_sum]
  have hpoint (mn : (Fin r → ℕ) × (Fin r → ℕ)) (hmn : mn ∈ M ×ˢ M) :
      ((squareSlice Z (coefficientValue k h mn.2-coefficientValue k h mn.1)).card : ℝ) ≤
      (if coefficientValue k h mn.1=coefficientValue k h mn.2 then 2*(Z.card : ℝ) else 0)+E := by
    by_cases hz : coefficientValue k h mn.1=coefficientValue k h mn.2
    · rw [if_pos hz,hz,sub_self]
      have hd : ((squareSlice Z 0).card : ℝ) ≤ 2*(Z.card : ℝ) := by
        exact_mod_cast squareSlice_zero_card_le Z
      linarith
    · rw [if_neg hz,zero_add]
      exact hoff mn hmn hz
  calc
    _ ≤ ∑ mn ∈ M ×ˢ M,
        ((if coefficientValue k h mn.1=coefficientValue k h mn.2 then 2*(Z.card : ℝ) else 0)+E) :=
      Finset.sum_le_sum hpoint
    _ = 2*(Z.card : ℝ)*((coefficientZeroPairs k h M).card : ℝ)+E*(M.card : ℝ)^2 := by
      rw [Finset.sum_add_distrib,← Finset.sum_filter]
      simp only [Finset.sum_const,nsmul_eq_mul,coefficientZeroPairs,Finset.card_product,Nat.cast_mul]
      ring

/-- Fixing the same nonzero shift tuple cancels the common frequency factor.
The injection retains both original coefficient tuples and both z variables. -/
theorem class_collision_card_le_sameShift {r : ℕ} (C : ℤ) (k : ℕ)
    (H M : Finset (Fin r → ℕ)) (Z : Finset ℤ) (h : Fin r → ℕ)
    (hC : C ≠ 0) (hh : shiftProduct h ≠ 0) :
    (collisionPairs (classFiber (indexSet H M Z) Prod.fst h) (frequency C k)).card ≤
      (sameShiftPairs k h M Z).card := by
  let code := fun p : (((Fin r → ℕ) × ((Fin r → ℕ) × ℤ)) ×
      ((Fin r → ℕ) × ((Fin r → ℕ) × ℤ))) => ((p.1.2.1,p.2.2.1),(p.1.2.2,p.2.2.2))
  have hkeys {x : (Fin r → ℕ) × ((Fin r → ℕ) × ℤ)}
      (hx : x ∈ classFiber (indexSet H M Z) Prod.fst h) :
      x.1=h ∧ x.2.1 ∈ M ∧ x.2.2 ∈ Z := by
    rcases Finset.mem_filter.mp hx with ⟨hx,hkey⟩
    exact ⟨hkey,(Finset.mem_product.mp (Finset.mem_product.mp hx).2).1,
      (Finset.mem_product.mp (Finset.mem_product.mp hx).2).2⟩
  apply Finset.card_le_card_of_injOn code
  · intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpair,hfreq⟩
    have hl := hkeys (Finset.mem_product.mp hpair).1
    have hr := hkeys (Finset.mem_product.mp hpair).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨hl.2.1,hr.2.1⟩,
      Finset.mem_product.mpr ⟨hl.2.2,hr.2.2⟩⟩,?_⟩
    simp only [frequency,hl.1,hr.1] at hfreq
    have hv := mul_left_cancel₀ (mul_ne_zero hC hh) hfreq
    dsimp [code]
    linarith
  · intro p hp q hq heq
    have hpkeys := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
    have hqkeys := Finset.mem_product.mp (Finset.mem_filter.mp hq).1
    have hpl := hkeys hpkeys.1
    have hpr := hkeys hpkeys.2
    have hql := hkeys hqkeys.1
    have hqr := hkeys hqkeys.2
    have hm := congrArg Prod.fst heq
    have hz := congrArg Prod.snd heq
    dsimp [code] at hm hz
    have hm1 : p.1.2.1=q.1.2.1 := congrArg (fun v : (Fin r → ℕ) × (Fin r → ℕ) => v.1) hm
    have hm2 : p.2.2.1=q.2.2.1 := congrArg (fun v : (Fin r → ℕ) × (Fin r → ℕ) => v.2) hm
    have hz1 : p.1.2.2=q.1.2.2 := congrArg (fun v : ℤ × ℤ => v.1) hz
    have hz2 : p.2.2.2=q.2.2.2 := congrArg (fun v : ℤ × ℤ => v.2) hz
    exact Prod.ext
      (Prod.ext (hpl.1.trans hql.1.symm) (Prod.ext hm1 hz1))
      (Prod.ext (hpr.1.trans hqr.1.symm) (Prod.ext hm2 hz2))

#print axioms squareSlice_nonzero_card_le
#print axioms sameShift_card_le
#print axioms class_collision_card_le_sameShift
end Waring.AuxiliaryL2Counting
