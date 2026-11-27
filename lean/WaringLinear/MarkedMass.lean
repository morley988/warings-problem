import WaringLinear.MarkedRoots
import WaringLinear.PrimeWindowBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Order.Interval.Finset.Nat

/-! Cardinality and reciprocal mass of positive marked integers with a free cofactor. -/
noncomputable section
open Finset Filter
open scoped Classical BigOperators
namespace WaringLinear.MarkedMass

variable {ι : Type*} [Fintype ι]

/-- Exactly one choice in each window and an integer cofactor in the full available range. -/
def data (P : ℝ) (W : ι → Finset ℕ) : Finset ((ι → ℕ) × ℕ) :=
  (Fintype.piFinset W).biUnion fun a =>
    (Icc 1 ⌊P / ((∏ i, a i : ℕ) : ℝ)⌋₊).image (Prod.mk a)

/-- The set of actual distinct roots, independent of multiplicities in a presentation. -/
def roots (P : ℝ) (W : ι → Finset ℕ) : Finset ℕ :=
  (data P W).image fun t => t.2 * ∏ i, t.1 i

private theorem mem_data {P : ℝ} {W : ι → Finset ℕ} {a : ι → ℕ} {y : ℕ} :
    (a,y) ∈ data P W ↔ a ∈ Fintype.piFinset W ∧ y ∈ Icc 1 ⌊P/((∏ i,a i : ℕ):ℝ)⌋₊ := by
  simp [data, and_left_comm, and_assoc, and_comm]

/-- Membership in the marked root set includes the exact cofactor cutoff. -/
theorem mem_roots {P : ℝ} {W : ι → Finset ℕ} {n : ℕ} :
    n ∈ roots P W ↔ ∃ (a : ι → ℕ) (y : ℕ), (∀ i, a i ∈ W i) ∧ 1 ≤ y ∧
      y ≤ ⌊P / ((∏ i,a i : ℕ):ℝ)⌋₊ ∧ y * (∏ i,a i) = n := by
  constructor
  · intro h
    obtain ⟨⟨a,y⟩,ha,rfl⟩ := mem_image.mp h
    obtain ⟨ha,hy⟩ := mem_data.mp ha
    exact ⟨a,y,Fintype.mem_piFinset.mp ha,(mem_Icc.mp hy).1,(mem_Icc.mp hy).2,rfl⟩
  · rintro ⟨a,y,ha,hy,hmax,rfl⟩
    exact mem_image.mpr ⟨(a,y),mem_data.mpr ⟨Fintype.mem_piFinset.mpr ha,mem_Icc.mpr ⟨hy,hmax⟩⟩,rfl⟩

/-- The reciprocal mass factors over the marked prime intervals. -/
theorem mass_factor (W : ι → Finset ℕ) :
    ∑ a ∈ Fintype.piFinset W, (((∏ i, a i : ℕ) : ℝ))⁻¹ =
    ∏ i, ∑ p ∈ W i, (p : ℝ)⁻¹ := by
  rw [prod_univ_sum]
  simp

private theorem product_pos (W : ι → Finset ℕ) {a : ι → ℕ}
    (hprime : ∀ i, ∀ p ∈ W i, Nat.Prime p) (ha : a ∈ Fintype.piFinset W) :
    (0 : ℝ) < ((∏ i, a i : ℕ) : ℝ) := by
  exact_mod_cast (Finset.prod_pos fun i _ => (hprime _ _ (Fintype.mem_piFinset.mp ha i)).pos)

/-- Exact cofactor count for the full marked root support. -/
theorem card_roots (P : ℝ) (W : ι → Finset ℕ)
    (hprime : ∀ i, ∀ p ∈ W i, Nat.Prime p)
    (hsep : ∀ i j, ∀ p ∈ W i, p ∈ W j → i = j)
    (hsmall : ∀ a ∈ Fintype.piFinset W, ∀ i, ∀ p ∈ W i,
      P / ((∏ j, a j : ℕ) : ℝ) < p) :
    (roots P W).card = ∑ a ∈ Fintype.piFinset W, ⌊P/((∏ i,a i : ℕ):ℝ)⌋₊ := by
  have hinj : Set.InjOn (fun t : (ι → ℕ) × ℕ => t.2 * ∏ i, t.1 i) (data P W) := by
    rintro ⟨a,y⟩ ha ⟨b,z⟩ hb he
    obtain ⟨ha,hy⟩ := mem_data.mp ha
    obtain ⟨hb,hz⟩ := mem_data.mp hb
    obtain ⟨hzpos,hzle⟩ := mem_Icc.mp hz
    have hzr : (z : ℝ) ≤ P / ((∏ j,b j : ℕ):ℝ) := by
      have hfloorpos : 0 < ⌊P / ((∏ j,b j : ℕ):ℝ)⌋₊ := by omega
      exact (le_trans (by exact_mod_cast hzle) (Nat.floor_le (Nat.floor_pos.mp hfloorpos |>.trans' zero_le_one)))
    obtain ⟨hab,hyz⟩ := WaringLinear.marked_product_unique a b y z
      (fun i => hprime _ _ (Fintype.mem_piFinset.mp ha i))
      (fun j => hprime _ _ (Fintype.mem_piFinset.mp hb j))
      (fun i hdiv => by
        have hh := hzr.trans_lt (hsmall b hb i (a i) (Fintype.mem_piFinset.mp ha i))
        exact (not_le_of_gt hh) (by exact_mod_cast Nat.le_of_dvd hzpos hdiv))
      (fun i j hij => hsep j i _ (Fintype.mem_piFinset.mp hb j)
        (hij ▸ Fintype.mem_piFinset.mp ha i)) he
    exact Prod.ext hab hyz
  rw [roots, Finset.card_image_iff.mpr hinj, data, card_biUnion]
  · apply sum_congr rfl
    intro a _
    rw [card_image_of_injective _ (Prod.mk_right_injective _)]
    simp
  · intro a _ b _ hab
    apply Finset.disjoint_left.mpr
    rintro _ h1 h2
    obtain ⟨y,_,rfl⟩ := mem_image.mp h1
    obtain ⟨z,_,he⟩ := mem_image.mp h2
    exact hab (congrArg Prod.fst he.symm)

/-- Between half and all of the full expected reciprocal-weight mass is realized by
distinct positive roots whenever every marked product is at most the root scale. -/
theorem card_roots_bounds (P : ℝ) (W : ι → Finset ℕ)
    (hprime : ∀ i, ∀ p ∈ W i, Nat.Prime p)
    (hsep : ∀ i j, ∀ p ∈ W i, p ∈ W j → i = j)
    (hlarge : ∀ a ∈ Fintype.piFinset W, ((∏ j, a j : ℕ) : ℝ) ≤ P)
    (hsmall : ∀ a ∈ Fintype.piFinset W, ∀ i, ∀ p ∈ W i,
      P / ((∏ j, a j : ℕ) : ℝ) < p) :
    P * (∏ i, ∑ p ∈ W i, (p : ℝ)⁻¹) / 2 ≤ ((roots P W).card : ℝ) ∧
    ((roots P W).card : ℝ) ≤ P * (∏ i, ∑ p ∈ W i, (p : ℝ)⁻¹) := by
  rw [card_roots P W hprime hsep hsmall, ← mass_factor, mul_sum, Nat.cast_sum]
  have hq (a) (ha : a ∈ Fintype.piFinset W) :
      1 ≤ P * (((∏ i, a i : ℕ) : ℝ))⁻¹ := by
    rw [← div_eq_mul_inv]
    exact (one_le_div (product_pos W hprime ha)).mpr (hlarge _ ha)
  constructor
  · rw [div_le_iff₀ (by norm_num : (0:ℝ)<2),sum_mul]
    apply sum_le_sum
    intro a ha
    have hh := Nat.lt_floor_add_one (P * (((∏ j,a j : ℕ):ℝ))⁻¹)
    have hz : 1 ≤ ⌊P * (((∏ j,a j : ℕ):ℝ))⁻¹⌋₊ := Nat.le_floor (by simpa using hq a ha)
    rw [div_eq_mul_inv]
    have hz' : (1:ℝ) ≤ ⌊P * (((∏ j,a j : ℕ):ℝ))⁻¹⌋₊ := by exact_mod_cast hz
    linarith
  · apply sum_le_sum
    intro a ha
    rw [div_eq_mul_inv]
    exact Nat.floor_le ((hq a ha).trans' zero_le_one)


/-- The natural prime interval with real endpoints used in the moment argument. -/
def primeWindow (P v γ : ℝ) : Finset ℕ :=
  (Ioc ⌊P ^ v⌋₊ ⌊P ^ (γ * v)⌋₊).filter Nat.Prime

private theorem in_window {P v γ : ℝ} (hP : 0 < P) {p : ℕ} (hp : p ∈ primeWindow P v γ) :
    p.Prime ∧ P^v < p ∧ (p:ℝ) ≤ P^(γ*v) := by
  obtain ⟨ht,hp⟩ := mem_filter.mp hp
  obtain ⟨ha,hb⟩ := mem_Ioc.mp ht
  exact ⟨hp, Nat.lt_of_floor_lt ha, (Nat.le_floor_iff (Real.rpow_nonneg hP.le _)).mp hb⟩

/-- For disjoint exponent windows, the cardinality estimates need no further
arithmetic assumptions on the individual marked products. -/
theorem power_card_bounds (P γ : ℝ) (v : ι → ℝ) (hP : 1 < P)
    (hsep : ∀ i j, i ≠ j → γ*v i ≤ v j ∨ γ*v j ≤ v i)
    (hupper : γ * (∑ i, v i) ≤ 1) (hbottom : ∀ i, 1 - (∑ j, v j) ≤ v i) :
    let W := fun i => primeWindow P (v i) γ
    P * (∏ i, ∑ p ∈ W i, (p : ℝ)⁻¹) / 2 ≤ ((roots P W).card : ℝ) ∧
    ((roots P W).card : ℝ) ≤ P * (∏ i, ∑ p ∈ W i, (p : ℝ)⁻¹) := by
  intro W
  have hp0 : 0 < P := by linarith
  have hprime : ∀ i, ∀ p ∈ W i, Nat.Prime p := fun i p hp => (in_window hp0 hp).1
  apply card_roots_bounds P W hprime
  · intro i j p hi hj
    by_contra h
    have h1 := (in_window hp0 hi).2
    have h2 := (in_window hp0 hj).2
    rcases hsep i j h with hij | hji
    · exact ((h1.2.trans (Real.rpow_le_rpow_of_exponent_le hP.le hij)).not_gt h2.1)
    · exact ((h2.2.trans (Real.rpow_le_rpow_of_exponent_le hP.le hji)).not_gt h1.1)
  · intro a ha
    rw [Nat.cast_prod]
    calc
      (∏ i, (a i:ℝ)) ≤ ∏ i, P ^ (γ*v i) := by
        apply prod_le_prod (fun i _ => Nat.cast_nonneg _)
        exact fun i _ => (in_window hp0 (Fintype.mem_piFinset.mp ha i)).2.2
      _ = P ^ (γ * ∑ i, v i) := by rw [mul_sum, Real.rpow_sum_of_pos hp0]
      _ ≤ P := by simpa using Real.rpow_le_rpow_of_exponent_le hP.le hupper
  · intro a ha i p hip
    have hden : P ^ (∑ j, v j) ≤ ((∏ j, a j : ℕ) : ℝ) := by
      rw [Nat.cast_prod, Real.rpow_sum_of_pos hp0]
      exact prod_le_prod (fun j _ => Real.rpow_nonneg hp0.le _) (fun j _ =>
        (in_window hp0 (Fintype.mem_piFinset.mp ha j)).2.1.le)
    calc
      P / _ ≤ P / P ^ (∑ j, v j) := div_le_div_of_nonneg_left hp0.le (Real.rpow_pos_of_pos hp0 _) hden
      _ = P ^ (1 - ∑ j, v j) := by rw [Real.rpow_sub hp0, Real.rpow_one]
      _ ≤ P ^ v i := Real.rpow_le_rpow_of_exponent_le hP.le (hbottom i)
      _ < p := (in_window hp0 hip).2.1

/-- Positive lower density for the actual set of positive roots, as soon as each
fixed prime interval has positive lower reciprocal mass. The finite product
makes the dependence of the density on the choice of windows explicit. -/
theorem eventually_positive_proportion (γ : ℝ) (v c : ι → ℝ)
    (hc : ∀ i, 0 < c i)
    (hsep : ∀ i j, i ≠ j → γ*v i ≤ v j ∨ γ*v j ≤ v i)
    (hupper : γ * (∑ i, v i) ≤ 1) (hbottom : ∀ i, 1 - (∑ j, v j) ≤ v i)
    (hmass : ∀ i, ∀ᶠ P : ℝ in Filter.atTop,
      c i ≤ ∑ p ∈ primeWindow P (v i) γ, (p:ℝ)⁻¹) :
    0 < (∏ i, c i)/2 ∧ ∀ᶠ P : ℝ in Filter.atTop,
      (∏ i, c i)/2 * P ≤ ((roots P (fun i => primeWindow P (v i) γ)).card : ℝ) := by
  refine ⟨half_pos (prod_pos (fun i _ => hc i)),?_⟩
  filter_upwards [Filter.eventually_gt_atTop (1:ℝ), Filter.eventually_all.mpr hmass] with P hP hM
  have h := (power_card_bounds P γ v hP hsep hupper hbottom).1
  have hprod := prod_le_prod (s:=univ) (fun i _ => (hc i).le) (fun i _ => hM i)
  nlinarith [mul_le_mul_of_nonneg_left hprod (by linarith : 0 ≤ P)]

#print axioms card_roots
#print axioms eventually_positive_proportion


/-- Every element counted by the density bound is a positive integer at most P. -/
theorem roots_subset (P : ℝ) (W : ι → Finset ℕ)
    (hprime : ∀ i, ∀ p ∈ W i, Nat.Prime p) :
    roots P W ⊆ Icc 1 ⌊P⌋₊ := by
  intro n hn
  obtain ⟨⟨a,y⟩,hy,rfl⟩ := mem_image.mp hn
  obtain ⟨ha,hy⟩ := mem_data.mp hy
  obtain ⟨hypos,hymax⟩ := mem_Icc.mp hy
  have hd := product_pos W hprime ha
  have hdn : 0 < ∏ i,a i := by exact_mod_cast hd
  refine mem_Icc.mpr ⟨Nat.mul_pos hypos hdn, Nat.le_floor ?_⟩
  have hf : 0 < ⌊P/((∏ j,a j : ℕ):ℝ)⌋₊ := by omega
  have hq := Nat.floor_le ((Nat.floor_pos.mp hf).trans' zero_le_one)
  have hyr : (y:ℝ) ≤ P / ((∏ i,a i : ℕ):ℝ) := (le_trans (by exact_mod_cast hymax) hq)
  simpa only [Nat.cast_mul] using (le_div_iff₀ hd).mp hyr

/-- The full marked-root support contains a positive proportion of all integers
at the root scale, unconditionally for any admissible finite system of windows. -/
theorem power_window_positive_density (γ : ℝ) (v : ι → ℝ) (hγ : 1 < γ) (hv : ∀ i, 0 < v i)
    (hsep : ∀ i j, i ≠ j → γ*v i ≤ v j ∨ γ*v j ≤ v i)
    (hupper : γ * (∑ i, v i) ≤ 1) (hbottom : ∀ i, 1 - (∑ j, v j) ≤ v i) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ P : ℝ in atTop,
      roots P (fun i => primeWindow P (v i) γ) ⊆ Icc 1 ⌊P⌋₊ ∧
      c*P ≤ ((roots P (fun i => primeWindow P (v i) γ)).card : ℝ) := by
  let c := fun _ : ι => (PrimeWindow.lower/2)*Real.log γ
  have hc (i : ι) : 0 < c i :=
    mul_pos (half_pos PrimeWindow.positive_constants.1) (Real.log_pos hγ)
  have hmass (i : ι) : ∀ᶠ P : ℝ in atTop, c i ≤ ∑ p ∈ primeWindow P (v i) γ, (p:ℝ)⁻¹ :=
    (PrimeWindow.power_window_bounds (v i) γ (hv i) hγ).mono fun _ h => h.1
  obtain ⟨hc₀, hprop⟩ := eventually_positive_proportion γ v c hc hsep hupper hbottom hmass
  refine ⟨_,hc₀,?_⟩
  filter_upwards [hprop] with P h
  exact ⟨roots_subset P _ (fun i p hp => (mem_filter.mp hp).2),h⟩

/-- Reciprocal mass of products from any family of small-width windows is at most one
at all sufficiently large root scales, including a family with no intervals. -/
theorem power_window_reciprocal_le_one (γ : ℝ) (v : ι → ℝ) (hγ : 1 < γ) (hv : ∀ i, 0 < v i)
    (hwidth : 2 * PrimeWindow.upper * Real.log γ ≤ 1) :
    ∀ᶠ P : ℝ in atTop, ∑ a ∈ Fintype.piFinset (fun i => primeWindow P (v i) γ),
      (((∏ i, a i : ℕ):ℝ))⁻¹ ≤ 1 := by
  have hwin : ∀ i, ∀ᶠ P : ℝ in atTop, ∑ p ∈ primeWindow P (v i) γ, (p:ℝ)⁻¹ ≤ 1 :=
    fun i => (PrimeWindow.power_window_bounds (v i) γ (hv i) hγ).mono fun _ h => h.2.trans hwidth
  filter_upwards [Filter.eventually_all.mpr hwin] with P hP
  rw [mass_factor]
  calc
    _ ≤ ∏ _i : ι, (1:ℝ) := by
      apply prod_le_prod (fun i _ => sum_nonneg (fun p _ => by positivity))
      exact fun i _ => hP i
    _ = 1 := by simp

#print axioms power_window_positive_density
#print axioms power_window_reciprocal_le_one

end WaringLinear.MarkedMass


