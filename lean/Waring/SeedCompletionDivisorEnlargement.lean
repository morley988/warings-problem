import Waring.SeedCompletionTerminalDivisorBox

/-! # Integer box enlargement preserving the elementary prefix conditions -/
noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionDivisorEnlargement
open AuxiliaryCounting AuxiliaryTupleCount

def inflatedHeight (j : ℕ) (R : ℝ) (H : ℕ → ℝ) (i : ℕ) : ℕ :=
  ⌈(2*R)^j*H i⌉₊

def inflatedCoefficient (R : ℝ) (M : ℕ → ℝ) (i : ℕ) : ℕ :=
  ⌈M i*R⌉₊

theorem ceil_le_twice {x : ℝ} (hx : 1≤x) : (⌈x⌉₊ : ℝ)≤2*x := by
  have h := (Nat.ceil_lt_add_one (show 0≤x by linarith)).le
  linarith

theorem inflatedHeight_bounds {j : ℕ} {R : ℝ} (hR : 1≤R)
    (H : ℕ→ℝ) {i : ℕ} (hH : 1≤H i) :
    H i≤(inflatedHeight j R H i : ℝ) ∧
      (inflatedHeight j R H i : ℝ)≤2*(2*R)^j*H i := by
  have hF : 1≤(2*R)^j := one_le_pow₀ (by linarith)
  have hbase : 1≤(2*R)^j*H i := one_le_mul_of_one_le_of_one_le hF hH
  constructor
  · exact (le_mul_of_one_le_left (by linarith) hF).trans (Nat.le_ceil _)
  · simpa only [inflatedHeight,mul_assoc] using ceil_le_twice hbase

theorem inflatedCoefficient_bounds {R : ℝ} (hR : 1≤R)
    (M : ℕ→ℝ) {i : ℕ} (hM : 1≤M i) :
    M i*R≤(inflatedCoefficient R M i : ℝ) ∧
      (inflatedCoefficient R M i : ℝ)≤2*M i*R := by
  exact ⟨Nat.le_ceil _,by simpa only [inflatedCoefficient,mul_assoc] using
    (ceil_le_twice (one_le_mul_of_one_le_of_one_le hM hR))⟩

theorem inflated_prefix {j : ℕ} {R : ℝ} (hR : 1≤R)
    (H M : ℕ→ℝ) (hH : ∀ i<j,1≤H i) (hM : ∀ i<j,1≤M i)
    (hprefix : ∀ i<j,(∏ l ∈ Finset.range i,M l)≤H i*M i) :
    ∀ i<j,(∏ l ∈ Finset.range i,inflatedCoefficient R M l)≤
      inflatedHeight j R H i*inflatedCoefficient R M i := by
  intro i hi
  have hprod : (∏ l ∈ Finset.range i,(inflatedCoefficient R M l : ℝ))≤
      (2*R)^i*(∏ l ∈ Finset.range i,M l) := by
    calc
      _ ≤ ∏ l ∈ Finset.range i,((2*R)*M l) := by
        apply Finset.prod_le_prod (fun _ _=>Nat.cast_nonneg _)
        intro l hl
        have h := (inflatedCoefficient_bounds hR M (hM l (lt_trans (Finset.mem_range.mp hl) hi))).2
        nlinarith
      _ = _ := by rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_range]
  have hF : (2*R)^i≤(2*R)^j := pow_le_pow_right₀ (by linarith) (le_of_lt hi)
  have hMR : M i≤M i*R := le_mul_of_one_le_right (by linarith [hM i hi]) hR
  have hlower : (2*R)^j*(H i*M i)≤
      (inflatedHeight j R H i : ℝ)*(inflatedCoefficient R M i : ℝ) := by
    calc
      _ = ((2*R)^j*H i)*M i := by ring
      _ ≤ _ := mul_le_mul (Nat.le_ceil _) (hMR.trans (Nat.le_ceil _))
        (by linarith [hM i hi]) (Nat.cast_nonneg _)
  have hp : (0:ℝ)≤∏ l ∈ Finset.range i,M l := Finset.prod_nonneg (by
    intro l hl
    linarith [hM l (lt_trans (Finset.mem_range.mp hl) hi)])
  have hu := hprod.trans ((mul_le_mul hF (hprefix i hi) hp (by positivity)).trans hlower)
  exact_mod_cast hu

theorem inflated_polynomial_bounds {j : ℕ} {P R : ℝ} (hP : 2≤P)
    (hR : 1≤R) (hRP : R≤P) (H M : ℕ→ℝ)
    (hH : ∀ i<j,1≤H i ∧ H i≤P) (hM : ∀ i<j,1≤M i ∧ M i≤P) :
    ∀ i<j,(inflatedHeight j R H i : ℝ)≤P^(2*j+3) ∧
      (inflatedCoefficient R M i : ℝ)≤P^(2*j+3) := by
  intro i hi
  have hP0 : 0≤P := by linarith
  have hP1 : 1≤P := by linarith
  have htwoR : 2*R≤P^2 := by nlinarith
  have hF : (2*R)^j≤(P^2)^j := pow_le_pow_left₀ (by linarith) htwoR _
  constructor
  · calc
      _ ≤ 2*(2*R)^j*H i := (inflatedHeight_bounds (j:=j) hR H (hH i hi).1).2
      _ ≤ P*(P^2)^j*P := mul_le_mul (mul_le_mul hP hF (by positivity) hP0)
        (hH i hi).2 (by linarith [(hH i hi).1]) (by positivity)
      _ = P^(2*j+2) := by rw [← pow_mul]; ring
      _ ≤ _ := pow_le_pow_right₀ hP1 (by omega)
  · calc
      _ ≤ 2*M i*R := (inflatedCoefficient_bounds hR M (hM i hi).1).2
      _ ≤ P*P*P := mul_le_mul (mul_le_mul hP (hM i hi).2
        (by linarith [(hM i hi).1]) hP0) hRP (by linarith) (by positivity)
      _ = P^3 := by ring
      _ ≤ _ := pow_le_pow_right₀ hP1 (by omega)

theorem inflated_size {j k : ℕ} {P R : ℝ} (hP : 2≤P)
    (hR : 1≤R) (hRP : R≤P) (H M : ℕ→ℝ)
    (hH : ∀ i<j,1≤H i ∧ H i≤P) (hM : ∀ i<j,1≤M i ∧ M i≤P) :
    ∀ i<j,((inflatedHeight j R H i^2*inflatedCoefficient R M i^(2*k) : ℕ):ℝ)
      ≤P^((2*j+3)*(2+2*k)) := by
  intro i hi
  have hb := inflated_polynomial_bounds hP hR hRP H M hH hM i hi
  push_cast
  calc
    _ ≤ (P^(2*j+3))^2*(P^(2*j+3))^(2*k) :=
      mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) hb.1 _)
        (pow_le_pow_left₀ (Nat.cast_nonneg _) hb.2 _) (by positivity) (by positivity)
    _ = _ := by rw [← pow_add,← pow_mul]

theorem inflated_coefficient_volume {j : ℕ} {R : ℝ} (hR : 1≤R)
    (M : ℕ→ℝ) (hM : ∀ i<j,1≤M i) :
    ((coordinateBox (inflatedCoefficient R M) j).card : ℝ)≤
      2^j*(∏ i : Fin j,M i.val*R) := by
  simp only [coordinateBox,Fintype.card_piFinset,Nat.card_Icc,Nat.add_sub_cancel,Nat.cast_prod]
  calc
    _ ≤ ∏ i : Fin j,(2*(M i.val*R)) := Finset.prod_le_prod
      (fun _ _=>Nat.cast_nonneg _) (fun i _=>by
        simpa only [mul_assoc] using (inflatedCoefficient_bounds hR M (hM i.val i.isLt)).2)
    _ = _ := by rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

theorem inflated_diagonal_volume {j : ℕ} {R : ℝ} (hR : 1≤R)
    (H M : ℕ→ℝ) (hH : ∀ i<j,1≤H i) (hM : ∀ i<j,1≤M i) :
    (diagonalProduct (inflatedHeight j R H) (inflatedCoefficient R M) j : ℝ)≤
      (4*(2*R)^j)^j*(∏ i : Fin j,H i.val)*(∏ i : Fin j,M i.val*R) := by
  rw [← SeedCompletionTerminalDivisorBox.coordinate_card_product]
  simp only [coordinateBox,Fintype.card_piFinset,Nat.card_Icc,Nat.add_sub_cancel,
    Nat.cast_mul,Nat.cast_prod,← Finset.prod_mul_distrib]
  calc
    _ ≤ ∏ i : Fin j,((4*(2*R)^j)*H i.val*(M i.val*R)) := by
      apply Finset.prod_le_prod (fun _ _=>by positivity)
      intro i _
      have hb := mul_le_mul (inflatedHeight_bounds (j:=j) hR H (hH i.val i.isLt)).2
        (inflatedCoefficient_bounds hR M (hM i.val i.isLt)).2
        (Nat.cast_nonneg _) (by have hHi := hH i.val i.isLt; positivity)
      convert hb using 1 <;> ring
    _ = _ := by simp only [Finset.prod_mul_distrib,Finset.prod_const,
        Finset.card_univ,Fintype.card_fin,mul_pow]

#print axioms inflated_prefix
#print axioms inflated_polynomial_bounds
#print axioms inflated_diagonal_volume
end Waring.SeedCompletionDivisorEnlargement
