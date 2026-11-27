import Waring.EvenMoments
import Waring.ProductMultiplicity
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Divisor-controlled grouping for the actual auxiliary second moment

Frequency collisions are grouped by the shift tuple. Cauchy is applied only
to the shift tuples that actually occur at each nonzero frequency. Divisibility
of every shift by that frequency bounds their number by a divisor power.
-/

noncomputable section
open scoped BigOperators
namespace Waring.AuxiliaryL2Grouping

def collisionPairs {ι : Type*} (A : Finset ι) (f : ι → ℤ) : Finset (ι × ι) :=
  (A ×ˢ A).filter (fun p => f p.1=f p.2)

def classFiber {ι κ : Type*} [DecidableEq κ] (A : Finset ι) (key : ι → κ) (h : κ) : Finset ι :=
  A.filter (fun x => key x=h)

/-- Exact decomposition of frequency collisions into squared fiber sizes. -/
theorem collision_card_eq_sum {ι : Type*} (A : Finset ι) (f : ι → ℤ)
    (N : Finset ℤ) (hN : ∀ x ∈ A, f x ∈ N) :
    (collisionPairs A f).card = ∑ n ∈ N, ((A.filter (fun x => f x=n)).card)^2 := by
  classical
  have hmap : (collisionPairs A f).toSet.MapsTo (fun p => f p.1) N := by
    intro p hp
    exact hN p.1 (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  apply Finset.sum_congr rfl
  intro n hn
  have heq : (collisionPairs A f).filter (fun p => f p.1=n) =
      (A.filter (fun x => f x=n)) ×ˢ (A.filter (fun x => f x=n)) := by
    ext p
    simp only [collisionPairs,Finset.mem_filter,Finset.mem_product]
    constructor
    · rintro ⟨⟨⟨hx,hy⟩,heq⟩,hn⟩
      exact ⟨⟨hx,hn⟩,hy,heq.symm.trans hn⟩
    · rintro ⟨⟨hx,hxn⟩,hy,hyn⟩
      exact ⟨⟨⟨hx,hy⟩,hxn.trans hyn.symm⟩,hxn⟩
  rw [heq,Finset.card_product,pow_two]

/-- Finite Cauchy grouping by the actual keys present at each frequency. -/
theorem collision_card_le_classes {ι κ : Type*} [DecidableEq κ] (A : Finset ι) (f : ι → ℤ)
    (key : ι → κ) (H : Finset κ) (hH : ∀ x ∈ A, key x ∈ H)
    {D : ℝ} (hD : 0 ≤ D)
    (hmult : ∀ n ∈ A.image f,
      (((A.filter (fun x => f x=n)).image key).card : ℝ) ≤ D) :
    ((collisionPairs A f).card : ℝ) ≤
      D*∑ h ∈ H, ((collisionPairs (classFiber A key h) f).card : ℝ) := by
  classical
  let N := A.image f
  have hmap : ∀ x ∈ A, f x ∈ N := fun x hx => Finset.mem_image_of_mem f hx
  rw [collision_card_eq_sum A f N hmap,Nat.cast_sum]
  simp only [Nat.cast_pow]
  have hclass (h : κ) :
      ((collisionPairs (classFiber A key h) f).card : ℝ) =
      ∑ n ∈ N, (((classFiber A key h).filter (fun x => f x=n)).card : ℝ)^2 := by
    have hm : ∀ x ∈ classFiber A key h, f x ∈ N := by
      intro x hx
      exact hmap x (Finset.mem_filter.mp hx).1
    exact_mod_cast collision_card_eq_sum (classFiber A key h) f N hm
  simp_rw [hclass]
  rw [Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  let F := A.filter (fun x => f x=n)
  let K := F.image key
  have hc : (F.card : ℝ) = ∑ h ∈ K, ((F.filter (fun x => key x=h)).card : ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_image key F
  have heq (h : κ) : F.filter (fun x => key x=h) =
      (classFiber A key h).filter (fun x => f x=n) := by
    ext x
    simp only [F,classFiber,Finset.mem_filter]
    tauto
  have hKH : K ⊆ H := by
    intro h hh
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hh
    exact hH x (Finset.mem_filter.mp hx).1
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq K (fun _ => (1 : ℝ))
    (fun h => (((classFiber A key h).filter (fun x => f x=n)).card : ℝ))
  simp only [one_mul,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one] at hcs
  calc
    (((A.filter (fun x => f x=n)).card)^2 : ℝ) = (F.card : ℝ)^2 := by norm_cast
    _ = (∑ h ∈ K, (((classFiber A key h).filter (fun x => f x=n)).card : ℝ))^2 := by
      rw [hc]; simp_rw [heq]
    _ ≤ (K.card : ℝ)*∑ h ∈ K, (((classFiber A key h).filter (fun x => f x=n)).card : ℝ)^2 := hcs
    _ ≤ D*∑ h ∈ H, (((classFiber A key h).filter (fun x => f x=n)).card : ℝ)^2 := by
      exact mul_le_mul (hmult n hn)
        (Finset.sum_le_sum_of_subset_of_nonneg hKH (fun _ _ _ => sq_nonneg _))
        (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) hD

/-- Exact second moment followed by the finite grouping inequality. -/
theorem secondMoment_le_classes {ι κ : Type*} [DecidableEq κ] (A : Finset ι) (f : ι → ℤ)
    (key : ι → κ) (H : Finset κ) (hH : ∀ x ∈ A, key x ∈ H)
    {D : ℝ} (hD : 0 ≤ D)
    (hmult : ∀ n ∈ A.image f,
      (((A.filter (fun x => f x=n)).image key).card : ℝ) ≤ D) :
    (∫ α in (0 : ℝ)..1, ‖∑ x ∈ A, fourier (f x) (α : AddCircle (1 : ℝ))‖^2) ≤
      D*∑ h ∈ H, ((collisionPairs (classFiber A key h) f).card : ℝ) := by
  rw [interval_integral_sq_norm_eq_collision_count]
  exact collision_card_le_classes A f key H hH hD hmult

/-- Divisor powers have an actual uniform subpower bound. -/
theorem divisor_power_le_rpow (r : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n → (n.divisors.card : ℝ)^r ≤ C*(n : ℝ)^ε := by
  let δ : ℝ := ε/((r : ℝ)+1)
  have hr : (0 : ℝ) < (r : ℝ)+1 := by positivity
  have hδ : 0 < δ := div_pos hε hr
  have hδr : δ*(r : ℝ) ≤ ε := by
    have hid : δ*((r : ℝ)+1)=ε := div_mul_cancel₀ ε hr.ne'
    nlinarith
  obtain ⟨D,hD,hdiv⟩ := DivisorBound.divisor_count_le_rpow hδ
  refine ⟨D^r,by positivity,?_⟩
  intro n hn
  calc
    _ ≤ (D*(n : ℝ)^δ)^r := pow_le_pow_left₀ (by positivity) (hdiv n hn) r
    _ = D^r*(n : ℝ)^(δ*(r : ℝ)) := by rw [mul_pow,← Real.rpow_mul_natCast (by positivity)]
    _ ≤ D^r*(n : ℝ)^ε := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) hδr) (by positivity)

/-- Shift divisibility by a nonzero polynomial-size frequency supplies the
P^epsilon multiplicity in the second moment, with no assumed divisor bound. -/
theorem frequency_key_multiplicity (r : ℕ) {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P → ∀ (ι : Type*) (A : Finset ι)
      (f : ι → ℤ) (key : ι → Fin r → ℕ),
      (∀ x ∈ A, f x ≠ 0 ∧ ((f x).natAbs : ℝ) ≤ P^B) →
      (∀ x ∈ A, ∀ i, (key x i : ℤ) ∣ f x) →
      ∀ n ∈ A.image f,
        (((A.filter (fun x => f x=n)).image key).card : ℝ) ≤ C*P^ε := by
  let δ : ℝ := ε/(B+1)
  have hB1 : 0 < B+1 := by linarith
  have hδ : 0 < δ := div_pos hε hB1
  have hBδ : B*δ ≤ ε := by
    have hid : δ*(B+1)=ε := div_mul_cancel₀ ε hB1.ne'
    nlinarith
  obtain ⟨C,hC,hdiv⟩ := divisor_power_le_rpow r hδ
  refine ⟨C,hC,?_⟩
  intro P hP ι A f key hsize hdvd n hn
  classical
  obtain ⟨x,hx,hxn⟩ := Finset.mem_image.mp hn
  have hn0 : n ≠ 0 := hxn ▸ (hsize x hx).1
  have hnP : (n.natAbs : ℝ) ≤ P^B := hxn ▸ (hsize x hx).2
  have hsub : (A.filter (fun x => f x=n)).image key ⊆
      Fintype.piFinset (fun _ : Fin r => n.natAbs.divisors) := by
    intro h hh
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hh
    apply Fintype.mem_piFinset.mpr
    intro i
    apply Nat.mem_divisors.mpr
    refine ⟨?_,Int.natAbs_ne_zero.mpr hn0⟩
    have hd := hdvd y (Finset.mem_filter.mp hy).1 i
    rw [(Finset.mem_filter.mp hy).2] at hd
    exact Int.natCast_dvd.mp hd
  have hcard := Finset.card_le_card hsub
  simp only [Fintype.card_piFinset,Finset.prod_const,Finset.card_univ,Fintype.card_fin] at hcard
  calc
    _ ≤ (n.natAbs.divisors.card : ℝ)^r := by exact_mod_cast hcard
    _ ≤ C*(n.natAbs : ℝ)^δ := hdiv _ (Int.natAbs_pos.mpr hn0)
    _ ≤ C*(P^B)^δ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) hnP hδ.le) hC.le
    _ = C*P^(B*δ) := by rw [← Real.rpow_mul (zero_le_one.trans hP)]
    _ ≤ C*P^ε := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hP hBδ) hC.le

#print axioms collision_card_le_classes
#print axioms secondMoment_le_classes
#print axioms frequency_key_multiplicity
end Waring.AuxiliaryL2Grouping
