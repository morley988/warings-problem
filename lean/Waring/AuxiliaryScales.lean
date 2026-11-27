import Waring.AuxiliaryCounting
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Passing from real scales to actual integer coefficient boxes

Strict prefix-exponent margins imply the required inequalities for natural
floor cutoffs once P is sufficiently large. Both the polynomial size premise
and the diagonal-product exponent are proved from the displayed real scales.
-/

noncomputable section
open scoped BigOperators
open Filter
namespace Waring.AuxiliaryScales
open AuxiliaryCounting

def floorScale (P a : ℝ) : ℕ := ⌊P^a⌋₊

private theorem half_le_floor {x : ℝ} (hx : 2 ≤ x) : x/2 ≤ (⌊x⌋₊ : ℝ) := by
  have h := Nat.lt_floor_add_one x
  linarith

theorem prod_floorScale_le (P : ℝ) (hP : 0 < P) (a : ℕ → ℝ) (r : ℕ) :
    ((∏ i ∈ Finset.range r, floorScale P (a i) : ℕ) : ℝ) ≤
      P^(∑ i ∈ Finset.range r, a i) := by
  rw [Nat.cast_prod,Real.rpow_sum_of_pos hP]
  exact Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _)
    (fun i _ => Nat.floor_le (Real.rpow_nonneg hP.le _))

/-- A concrete sufficient threshold for one actual integer prefix inequality. -/
theorem floor_prefix_le {P : ℝ} (hP : 0 < P) (a b : ℕ → ℝ) (i : ℕ)
    (ha : 2 ≤ P^(a i)) (hb : 2 ≤ P^(b i))
    (hgap : 4 ≤ P^(a i+b i-∑ j ∈ Finset.range i, b j)) :
    (∏ j ∈ Finset.range i, floorScale P (b j)) ≤
      floorScale P (a i)*floorScale P (b i) := by
  have hprod := prod_floorScale_le P hP b i
  have hfloor : (P^(a i)/2)*(P^(b i)/2) ≤
      (floorScale P (a i) : ℝ)*(floorScale P (b i) : ℝ) :=
    mul_le_mul (half_le_floor ha) (half_le_floor hb) (by positivity) (by positivity)
  have hexp : 4*P^(∑ j ∈ Finset.range i, b j) ≤ P^(a i+b i) := by
    calc
      _ ≤ P^(a i+b i-∑ j ∈ Finset.range i, b j)*P^(∑ j ∈ Finset.range i, b j) :=
        mul_le_mul_of_nonneg_right hgap (by positivity)
      _ = P^(a i+b i) := by rw [← Real.rpow_add hP]; congr 1; ring
  rw [Real.rpow_add hP] at hexp
  have htotal : ((∏ j ∈ Finset.range i, floorScale P (b j) : ℕ) : ℝ) ≤
      ((floorScale P (a i)*floorScale P (b i) : ℕ) : ℝ) := by
    rw [Nat.cast_mul]
    nlinarith
  exact_mod_cast htotal

/-- Every strict real exponent margin produces the corresponding floor-cutoff
prefix inequality eventually, with a single common lower threshold. -/
theorem eventually_floor_prefix_le (a b : ℕ → ℝ) (r : ℕ)
    (ha : ∀ i < r, 0 < a i) (hb : ∀ i < r, 0 < b i)
    (hmargin : ∀ i < r, (∑ j ∈ Finset.range i, b j) < a i+b i) :
    ∀ᶠ P : ℝ in atTop, ∀ i < r,
      (∏ j ∈ Finset.range i, floorScale P (b j)) ≤
        floorScale P (a i)*floorScale P (b i) := by
  have heach : ∀ i ∈ Finset.range r, ∀ᶠ P : ℝ in atTop,
      (∏ j ∈ Finset.range i, floorScale P (b j)) ≤
        floorScale P (a i)*floorScale P (b i) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    filter_upwards [eventually_gt_atTop (0 : ℝ),
      (tendsto_rpow_atTop (ha i hi')).eventually (eventually_ge_atTop 2),
      (tendsto_rpow_atTop (hb i hi')).eventually (eventually_ge_atTop 2),
      (tendsto_rpow_atTop (sub_pos.mpr (hmargin i hi'))).eventually (eventually_ge_atTop 4)]
      with P hP haP hbP hgapP
    exact floor_prefix_le hP a b i haP hbP hgapP
  simpa only [Finset.mem_range] using (Finset.eventually_all (Finset.range r)).mpr heach

/-- Polynomial size of every block follows from its actual floor cutoffs. -/
theorem floor_block_size_le {P B a b : ℝ} (hP : 1 ≤ P) (k : ℕ)
    (hexp : 2*a+(k : ℝ)*b ≤ B) :
    (((floorScale P a)^2*(floorScale P b)^k : ℕ) : ℝ) ≤ P^B := by
  have hP0 := zero_le_one.trans hP
  calc
    _ = (floorScale P a : ℝ)^2*(floorScale P b : ℝ)^k := by push_cast; rfl
    _ ≤ (P^a)^2*(P^b)^k := mul_le_mul
      (pow_le_pow_left₀ (by positivity) (Nat.floor_le (Real.rpow_nonneg hP0 _)) 2)
      (pow_le_pow_left₀ (by positivity) (Nat.floor_le (Real.rpow_nonneg hP0 _)) k)
      (by positivity) (by positivity)
    _ = P^(2*a+(k : ℝ)*b) := by
      rw [← Real.rpow_mul_natCast hP0,← Real.rpow_mul_natCast hP0,
        ← Real.rpow_add (lt_of_lt_of_le zero_lt_one hP)]
      congr 1
      push_cast
      ring
    _ ≤ P^B := Real.rpow_le_rpow_of_exponent_le hP hexp

theorem diagonal_floorScale_le (P : ℝ) (hP : 0 < P) (a b : ℕ → ℝ) (r : ℕ) :
    (diagonalProduct (fun i => floorScale P (a i)) (fun i => floorScale P (b i)) r : ℝ) ≤
      P^(∑ i ∈ Finset.range r, (a i+b i)) := by
  rw [diagonalProduct,Nat.cast_prod,Real.rpow_sum_of_pos hP]
  apply Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _)
  intro i hi
  rw [Nat.cast_mul,Real.rpow_add hP]
  exact mul_le_mul (Nat.floor_le (Real.rpow_nonneg hP.le _))
    (Nat.floor_le (Real.rpow_nonneg hP.le _)) (by positivity) (by positivity)

/-- The actual auxiliary count in real-power coefficient scales, with no
integer-box or prefix inequality left as an assumption. -/
theorem auxiliary_zeroCount_real_scales (k r : ℕ) (hk : 2 ≤ k)
    (a b : ℕ → ℝ) {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε)
    (ha : ∀ i < r, 0 < a i) (hb : ∀ i < r, 0 < b i)
    (hmargin : ∀ i < r, (∑ j ∈ Finset.range i, b j) < a i+b i)
    (hsize : ∀ i < r, 2*a i+(k : ℝ)*b i ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∃ P₀ : ℝ, 1 ≤ P₀ ∧ ∀ P : ℝ, P₀ ≤ P →
      (zeroCount k (prefixFamily (fun i => floorScale P (a i))
        (fun i => floorScale P (b i)) r) : ℝ) ≤
      C*P^((∑ i ∈ Finset.range r, (a i+b i))+ε) := by
  obtain ⟨C,hC,hcount⟩ := auxiliary_zeroCount_le_polynomial r hB hε
  obtain ⟨P₀,hP₀⟩ := eventually_atTop.mp (eventually_floor_prefix_le a b r ha hb hmargin)
  refine ⟨C,hC,max 1 P₀,le_max_left _ _,?_⟩
  intro P hP
  have hP1 : 1 ≤ P := (le_max_left _ _).trans hP
  have hpos : 0 < P := lt_of_lt_of_le zero_lt_one hP1
  have hN := hcount P hP1 k hk (fun i => floorScale P (a i)) (fun i => floorScale P (b i))
    (fun i hi => floor_block_size_le hP1 k (hsize i hi)) (hP₀ P ((le_max_right _ _).trans hP))
  calc
    _ ≤ C*P^ε*(diagonalProduct (fun i => floorScale P (a i))
        (fun i => floorScale P (b i)) r : ℝ) := hN
    _ ≤ C*P^ε*P^(∑ i ∈ Finset.range r, (a i+b i)) :=
      mul_le_mul_of_nonneg_left (diagonal_floorScale_le P hpos a b r) (by positivity)
    _ = C*P^((∑ i ∈ Finset.range r, (a i+b i))+ε) := by
      rw [mul_assoc,← Real.rpow_add hpos,add_comm ε]

#print axioms eventually_floor_prefix_le
#print axioms auxiliary_zeroCount_real_scales
end Waring.AuxiliaryScales
