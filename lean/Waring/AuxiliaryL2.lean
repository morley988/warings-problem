import Waring.AuxiliaryL2Counting
import Waring.AuxiliaryTupleCount

/-!
# The quadratic auxiliary L2 reduction

The actual circle integral is bounded by P^(1+epsilon) times the genuine
same-shift coefficient collision count. Only finite polynomial range and
cardinality conditions are required; both divisor losses are proved here.
-/

noncomputable section
open scoped BigOperators
namespace Waring.AuxiliaryL2
open AuxiliaryL2Grouping AuxiliaryL2Counting AuxiliaryTupleCount AuxiliaryCounting

def coefficientCollisionCount {r : ℕ} (k : ℕ) (H M : Finset (Fin r → ℕ)) : ℕ :=
  ∑ h ∈ H, (coefficientZeroPairs k h M).card

def auxiliaryMoment {r : ℕ} (C : ℤ) (k : ℕ) (H M : Finset (Fin r → ℕ))
    (Z : Finset ℤ) : ℝ :=
  ∫ α in (0 : ℝ)..1, ‖∑ x ∈ indexSet H M Z,
    fourier (frequency C k x) (α : AddCircle (1 : ℝ))‖^2

theorem coefficient_diagonal_le {r : ℕ} (k : ℕ) (h : Fin r → ℕ)
    (M : Finset (Fin r → ℕ)) : M.card ≤ (coefficientZeroPairs k h M).card := by
  apply Finset.card_le_card_of_injOn (fun m => (m,m))
  · intro m hm
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hm,hm⟩,rfl⟩
  · intro m hm n hn heq
    exact congrArg Prod.fst heq

theorem diagonal_le_collisionCount {r : ℕ} (k : ℕ) (H M : Finset (Fin r → ℕ)) :
    H.card*M.card ≤ coefficientCollisionCount k H M := by
  calc
    _ = ∑ _h ∈ H, M.card := by simp
    _ ≤ ∑ h ∈ H, (coefficientZeroPairs k h M).card :=
      Finset.sum_le_sum (fun h hh => coefficient_diagonal_le k h M)

theorem coefficientCollisionCount_le_zeroCount (k r : ℕ) (H M : ℕ → ℕ) :
    coefficientCollisionCount k (coordinateBox H r) (coordinateBox M r) ≤
      zeroCount k (prefixFamily H M r) := by
  have heq (h m n : Fin r → ℕ) :
      coefficientValue k h m=coefficientValue k h n ↔
        (∑ i, (h i : ℤ)^2*((m i : ℤ)^k-(n i : ℤ)^k))=0 := by
    rw [← sub_eq_zero,coefficientValue,coefficientValue,← Finset.sum_sub_distrib]
    simp only [mul_sub]
  unfold coefficientCollisionCount coefficientZeroPairs
  simp_rw [heq]
  exact vector_collision_count_le k r H M

/-- Quantitative finite reduction before substituting the proved divisor bounds. -/
theorem auxiliaryMoment_le_of_fibers {r : ℕ} (C : ℤ) (k : ℕ)
    (H M : Finset (Fin r → ℕ)) (Z : Finset ℤ) (hC : C ≠ 0)
    (hshift : ∀ h ∈ H, shiftProduct h ≠ 0) {D E : ℝ} (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hmult : ∀ n ∈ (indexSet H M Z).image (frequency C k),
      ((((indexSet H M Z).filter (fun x => frequency C k x=n)).image Prod.fst).card : ℝ) ≤ D)
    (hoff : ∀ h ∈ H, ∀ mn ∈ M ×ˢ M,
      coefficientValue k h mn.1 ≠ coefficientValue k h mn.2 →
      ((squareSlice Z (coefficientValue k h mn.2-coefficientValue k h mn.1)).card : ℝ) ≤ E) :
    auxiliaryMoment C k H M Z ≤ D*(2*(Z.card : ℝ)*(coefficientCollisionCount k H M : ℝ)+
      E*(H.card : ℝ)*(M.card : ℝ)^2) := by
  have hb := secondMoment_le_classes (indexSet H M Z) (frequency C k) Prod.fst H
    (fun x hx => (Finset.mem_product.mp hx).1) hD hmult
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ hD
  calc
    _ ≤ ∑ h ∈ H, (2*(Z.card : ℝ)*((coefficientZeroPairs k h M).card : ℝ)+E*(M.card : ℝ)^2) := by
      apply Finset.sum_le_sum
      intro h hh
      have hc : ((collisionPairs (classFiber (indexSet H M Z) Prod.fst h) (frequency C k)).card : ℝ) ≤
          ((sameShiftPairs k h M Z).card : ℝ) := by
        exact_mod_cast class_collision_card_le_sameShift C k H M Z h hC (hshift h hh)
      exact hc.trans (sameShift_card_le k h M Z hE (hoff h hh))
    _ = 2*(Z.card : ℝ)*(coefficientCollisionCount k H M : ℝ)+E*(H.card : ℝ)*(M.card : ℝ)^2 := by
      rw [Finset.sum_add_distrib,← Finset.mul_sum]
      simp only [coefficientCollisionCount,Nat.cast_sum,Finset.sum_const,nsmul_eq_mul]
      ring

/-- The actual quadratic auxiliary L2 estimate with both divisor losses
fully discharged. The frequency range, coefficient range and finite-set sizes
are explicit arithmetic conditions, not analytic moment assumptions. -/
theorem auxiliaryMoment_le_coefficientCount (r : ℕ) {Bfreq Bcoeff ε : ℝ}
    (hBfreq : 0 ≤ Bfreq) (hBcoeff : 0 ≤ Bcoeff) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ P : ℝ, 1 ≤ P → ∀ C : ℤ, C ≠ 0 → ∀ k : ℕ,
      ∀ H M : Finset (Fin r → ℕ), ∀ Z : Finset ℤ,
      (∀ h ∈ H, shiftProduct h ≠ 0) →
      (∀ x ∈ indexSet H M Z, frequency C k x ≠ 0 ∧
        ((frequency C k x).natAbs : ℝ) ≤ P^Bfreq) →
      (∀ h ∈ H, ∀ m ∈ M, ∀ n ∈ M,
        ((coefficientValue k h n-coefficientValue k h m).natAbs : ℝ) ≤ P^Bcoeff) →
      (M.card : ℝ) ≤ P → (Z.card : ℝ) ≤ 3*P →
      auxiliaryMoment C k H M Z ≤ K*P^(1+ε)*(coefficientCollisionCount k H M : ℝ) := by
  let δ : ℝ := ε/2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨C₁,hC₁,hmult⟩ := frequency_key_multiplicity r hBfreq hδ
  obtain ⟨C₂,hC₂,hoff⟩ := squareSlice_nonzero_polynomial hBcoeff hδ
  refine ⟨C₁*(6+C₂),by positivity,?_⟩
  intro P hP C hC k H M Z hshift hfreq hcoef hM hZ
  have hPpos : 0 < P := lt_of_lt_of_le zero_lt_one hP
  have hPδ : 1 ≤ P^δ := Real.one_le_rpow hP hδ.le
  have hdiv : ∀ x ∈ indexSet H M Z, ∀ i : Fin r, (x.1 i : ℤ) ∣ frequency C k x := by
    intro x hx i
    have hd : (x.1 i : ℤ) ∣ shiftProduct x.1 := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hd C) _
  have hmultiplicity := hmult P hP _ (indexSet H M Z) (frequency C k) Prod.fst hfreq hdiv
  have hoffsets : ∀ h ∈ H, ∀ mn ∈ M ×ˢ M,
      coefficientValue k h mn.1 ≠ coefficientValue k h mn.2 →
      ((squareSlice Z (coefficientValue k h mn.2-coefficientValue k h mn.1)).card : ℝ) ≤ C₂*P^δ := by
    intro h hh mn hmn hne
    exact hoff P hP Z _ (sub_ne_zero.mpr hne.symm)
      (hcoef h hh mn.1 (Finset.mem_product.mp hmn).1 mn.2 (Finset.mem_product.mp hmn).2)
  have hb := auxiliaryMoment_le_of_fibers C k H M Z hC hshift
    (show 0 ≤ C₁*P^δ by positivity) (show 0 ≤ C₂*P^δ by positivity) hmultiplicity hoffsets
  have hdiag : (H.card : ℝ)*(M.card : ℝ) ≤ (coefficientCollisionCount k H M : ℝ) := by
    exact_mod_cast diagonal_le_collisionCount k H M
  have hvolume : (H.card : ℝ)*(M.card : ℝ)^2 ≤ P*(coefficientCollisionCount k H M : ℝ) := by
    calc
      _ = (M.card : ℝ)*((H.card : ℝ)*(M.card : ℝ)) := by ring
      _ ≤ (M.card : ℝ)*(coefficientCollisionCount k H M : ℝ) :=
        mul_le_mul_of_nonneg_left hdiag (by positivity)
      _ ≤ P*(coefficientCollisionCount k H M : ℝ) := mul_le_mul_of_nonneg_right hM (by positivity)
  have hmain : 2*(Z.card : ℝ)*(coefficientCollisionCount k H M : ℝ) ≤
      6*P*(coefficientCollisionCount k H M : ℝ) := by
    exact mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
  have hpowers : P^δ*P^δ*P = P^(1+ε) := by
    nth_rw 3 [← Real.rpow_one P]
    rw [← Real.rpow_add hPpos,← Real.rpow_add hPpos]
    congr 1
    dsimp [δ]
    ring
  calc
    _ ≤ C₁*P^δ*(2*(Z.card : ℝ)*(coefficientCollisionCount k H M : ℝ)+
        (C₂*P^δ)*(H.card : ℝ)*(M.card : ℝ)^2) := hb
    _ ≤ C₁*P^δ*((6+C₂*P^δ)*P*(coefficientCollisionCount k H M : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hv := mul_le_mul_of_nonneg_left hvolume (show 0 ≤ C₂*P^δ by positivity)
      nlinarith
    _ ≤ C₁*P^δ*(((6+C₂)*P^δ)*P*(coefficientCollisionCount k H M : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ hPpos.le
      nlinarith
    _ = (C₁*(6+C₂))*P^(1+ε)*(coefficientCollisionCount k H M : ℝ) := by
      calc
        _ = (C₁*(6+C₂))*(P^δ*P^δ*P)*(coefficientCollisionCount k H M : ℝ) := by ring
        _ = _ := by rw [hpowers]

#print axioms coefficientCollisionCount_le_zeroCount
#print axioms auxiliaryMoment_le_coefficientCount
end Waring.AuxiliaryL2
