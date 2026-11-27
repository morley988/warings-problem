import WaringLinear.GramAbsorption
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring

/-! # Removing arbitrary bounded weights in the bilinear monomial sum -/

noncomputable section
open scoped BigOperators ComplexConjugate
namespace WaringLinear

private theorem weighted_cauchy {ι : Type*} [Fintype ι] (a b : ι → ℂ)
    (ha : ∀i, ‖a i‖≤1) :
    ‖∑ i,a i*b i‖^2 ≤ (Fintype.card ι:ℝ)*∑ i,‖b i‖^2 := by
  have hh : ‖∑ i,a i*b i‖ ≤ ∑ i,‖b i‖ := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i _
    rw [norm_mul]
    simpa using mul_le_mul_of_nonneg_right (ha i) (norm_nonneg (b i))
  exact (pow_le_pow_left₀ (norm_nonneg _) hh 2).trans
    (by simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => ‖b i‖))

private theorem complex_square_expansion {ι : Type*} [Fintype ι] (a : ι → ℂ) :
    ((‖∑ i,a i‖^2:ℝ):ℂ) = ∑ i, ∑ j, a i*conj (a j) := by
  rw [Complex.ofReal_pow,←Complex.mul_conj']
  simp [Finset.sum_mul,Finset.mul_sum]
  exact Finset.sum_comm

/-- Two Cauchy inequalities eliminate both coefficient sequences. -/
theorem bilinear_box_cauchy {X Y : Type*} [Fintype X] [Fintype Y]
    (a : X → ℂ) (b : Y → ℂ) (K : X → Y → ℂ)
    (ha : ∀i,‖a i‖≤1) (hb : ∀j,‖b j‖≤1) :
    ‖∑ i,a i*(∑ j,b j*K i j)‖^4 ≤
    (Fintype.card X:ℝ)^2*(Fintype.card Y:ℝ)^2*
      ∑ z : Y×Y, ‖∑ i,K i z.1*conj (K i z.2)‖^2 := by
  classical
  let T := ∑ i,a i*(∑ j,b j*K i j)
  let E := ∑ i,‖∑ j,b j*K i j‖^2
  let H (z:Y×Y) := ∑ i,K i z.1*conj (K i z.2)
  let B (z:Y×Y) := b z.1*conj (b z.2)
  have epos : 0≤E := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have ecast : (E:ℂ)=∑ z,B z*H z := by
    simp only [E,Complex.ofReal_sum,complex_square_expansion,map_mul,H,B,
      Fintype.sum_prod_type,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro z _
    ring
  have h0 : ‖T‖^2 ≤ (Fintype.card X:ℝ)*E := weighted_cauchy _ _ ha
  have h1 := weighted_cauchy B H (fun z => by
    dsimp [B]
    rw [norm_mul,RCLike.norm_conj]
    exact (mul_le_mul (hb _) (hb _) (norm_nonneg _) zero_le_one).trans (by norm_num))
  rw [←ecast,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg epos,Fintype.card_prod,
    Nat.cast_mul] at h1
  have h2 := pow_le_pow_left₀ (sq_nonneg ‖T‖) h0 2
  rw [mul_pow] at h2
  change ‖T‖^4 ≤ _ 
  calc
    _ = (‖T‖^2)^2 := by ring
    _ ≤ _ := h2
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left h1 (sq_nonneg (Fintype.card X:ℝ))
      simpa only [pow_two,mul_assoc,H] using hh

/-- The four phases combine to the product of the two power differences. -/
theorem bilinear_monomial_difference {R : Type*} [CommRing R]
    (a x y t u : R) (k : ℕ) :
    a*(x*t)^k - a*(x*u)^k - a*(y*t)^k + a*(y*u)^k =
      a*(x^k-y^k)*(t^k-u^k) := by simp only [mul_pow]; ring

#print axioms bilinear_box_cauchy
#print axioms bilinear_monomial_difference
end WaringLinear
