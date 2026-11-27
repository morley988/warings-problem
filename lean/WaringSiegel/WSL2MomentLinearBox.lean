import WaringSiegel.WSL2MomentCubicWeyl
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Linear character sums on integer-coordinate boxes

The geometric bound includes its resonant case explicitly. Thus division by
zero is never used as an infinite estimate. All characters below are literal
additive characters, including the trace-coordinate character of O_K.
-/

noncomputable section
open scoped BigOperators Classical NumberField

namespace WaringSiegel.WSL2

def characterIntervalBound (N : ℕ) (z : ℂ) : ℝ :=
  if z = 1 then N else min (N : ℝ) (2 / ‖1-z‖)

theorem characterIntervalBound_nonneg (N : ℕ) (z : ℂ) :
    0 ≤ characterIntervalBound N z := by
  unfold characterIntervalBound
  split_ifs <;> positivity

theorem characterIntervalBound_mono {M N : ℕ} (hMN : M ≤ N) (z : ℂ) :
    characterIntervalBound M z ≤ characterIntervalBound N z := by
  unfold characterIntervalBound
  split_ifs
  · exact_mod_cast hMN
  · exact min_le_min (by exact_mod_cast hMN) le_rfl

theorem norm_geom_sum_le_characterIntervalBound (z : ℂ) (hz : ‖z‖ = 1) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, z^n‖ ≤ characterIntervalBound N z := by
  have htrivial : ‖∑ n ∈ Finset.range N, z^n‖ ≤ N := by
    calc
      _ ≤ ∑ n ∈ Finset.range N, ‖z^n‖ := norm_sum_le _ _
      _ = _ := by simp [norm_pow, hz]
  unfold characterIntervalBound
  split_ifs with hres
  · exact htrivial
  · apply le_min htrivial
    have hd : 0 < ‖1-z‖ := norm_pos_iff.mpr (by
      intro he
      exact hres (sub_eq_zero.mp he).symm)
    apply (le_div_iff₀ hd).mpr
    calc
      ‖∑ n ∈ Finset.range N, z^n‖ * ‖1-z‖ =
          ‖(∑ n ∈ Finset.range N, z^n)*(1-z)‖ := (norm_mul _ _).symm
      _ = ‖1-z^N‖ := by rw [geom_sum_mul_neg]
      _ ≤ ‖(1 : ℂ)‖ + ‖z^N‖ := norm_sub_le _ _
      _ = 2 := by norm_num [norm_pow, hz]

theorem norm_addChar_Icc_eq_geom (χ : AddChar ℤ ℂ) (hχ : ∀ n, ‖χ n‖ = 1) (a b : ℤ) :
    ‖∑ n ∈ Finset.Icc a b, χ n‖ =
      ‖∑ n ∈ Finset.range (b+1-a).toNat, (χ 1)^n‖ := by
  have hnat (n : ℕ) : χ (n : ℤ) = (χ 1)^n := by
    simpa using χ.map_nsmul_eq_pow n (1 : ℤ)
  rw [Int.Icc_eq_finset_map, Finset.sum_map]
  change ‖∑ n ∈ Finset.range (b+1-a).toNat, χ (a+(n : ℤ))‖ = _
  simp_rw [χ.map_add_eq_mul, hnat]
  rw [← Finset.mul_sum, norm_mul, hχ a, one_mul]

theorem norm_addChar_Icc_le (χ : AddChar ℤ ℂ) (hχ : ∀ n, ‖χ n‖ = 1) (a b : ℤ) :
    ‖∑ n ∈ Finset.Icc a b, χ n‖ ≤ characterIntervalBound (b+1-a).toNat (χ 1) := by
  rw [norm_addChar_Icc_eq_geom χ hχ]
  exact norm_geom_sum_le_characterIntervalBound _ (hχ 1) _

section CoordinateBoxes
variable {ι : Type*} [Fintype ι]

def coordinateIntervalBox (a b : ι → ℤ) : Finset (ι → ℤ) :=
  Fintype.piFinset (fun i => Finset.Icc (a i) (b i))

def coordinateCharacter (χ : AddChar (ι → ℤ) ℂ) (i : ι) : AddChar ℤ ℂ where
  toFun n := χ (Pi.single i n)
  map_zero_eq_one' := by simp
  map_add_eq_mul' m n := by rw [Pi.single_add, χ.map_add_eq_mul]

theorem addChar_finset_sum {A β : Type*} [AddCommMonoid A]
    (χ : AddChar A ℂ) (S : Finset β) (f : β → A) :
    χ (∑ i ∈ S, f i) = ∏ i ∈ S, χ (f i) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, χ.map_add_eq_mul, ih]

theorem coordinate_character_factorization (χ : AddChar (ι → ℤ) ℂ) (x : ι → ℤ) :
    χ x = ∏ i, coordinateCharacter χ i (x i) := by
  have heq : x = ∑ i, Pi.single i (x i) := by
    funext j
    simp
  nth_rw 1 [heq]
  rw [addChar_finset_sum]
  rfl

theorem sum_addChar_coordinate_box (χ : AddChar (ι → ℤ) ℂ) (a b : ι → ℤ) :
    (∑ x ∈ coordinateIntervalBox a b, χ x) =
      ∏ i, ∑ n ∈ Finset.Icc (a i) (b i), coordinateCharacter χ i n := by
  simp_rw [coordinate_character_factorization χ]
  exact (Finset.prod_univ_sum (fun i => Finset.Icc (a i) (b i))
    (fun i n => coordinateCharacter χ i n)).symm

/-- Product geometric cancellation in an actual integer-coordinate box. -/
theorem norm_addChar_coordinate_box_le (χ : AddChar (ι → ℤ) ℂ)
    (hχ : ∀ x, ‖χ x‖ = 1) (a b : ι → ℤ) :
    ‖∑ x ∈ coordinateIntervalBox a b, χ x‖ ≤
      ∏ i, characterIntervalBound (b i+1-a i).toNat (χ (Pi.single i 1)) := by
  rw [sum_addChar_coordinate_box, norm_prod]
  apply Finset.prod_le_prod
  · intro i hi
    exact norm_nonneg _
  · intro i hi
    exact norm_addChar_Icc_le (coordinateCharacter χ i) (fun n => hχ _) _ _

end CoordinateBoxes

section LatticeBoxes
variable {R ι : Type*} [AddCommGroup R] [Fintype ι]

def coordinateLatticeBox (e : R ≃+ (ι → ℤ)) (a b : ι → ℤ) : Finset R :=
  (coordinateIntervalBox a b).image e.symm

theorem mem_coordinateLatticeBox (e : R ≃+ (ι → ℤ)) (a b : ι → ℤ) (x : R) :
    x ∈ coordinateLatticeBox e a b ↔ ∀ i, a i ≤ e x i ∧ e x i ≤ b i := by
  have heq : x ∈ coordinateLatticeBox e a b ↔ e x ∈ coordinateIntervalBox a b := by
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      simpa only [AddEquiv.apply_symm_apply] using hy
    · intro hx
      exact Finset.mem_image.mpr ⟨e x, hx, e.symm_apply_apply x⟩
  simpa only [coordinateIntervalBox, Fintype.mem_piFinset, Finset.mem_Icc] using heq

def overlapLower (a : ι → ℤ) (h : ι → ℤ) : ι → ℤ := fun i => max (a i) (a i-h i)
def overlapUpper (b : ι → ℤ) (h : ι → ℤ) : ι → ℤ := fun i => min (b i) (b i-h i)

theorem additiveOverlap_coordinateLatticeBox (e : R ≃+ (ι → ℤ)) (a b : ι → ℤ) (h : R) :
    additiveOverlap (coordinateLatticeBox e a b) h =
      coordinateLatticeBox e (overlapLower a (e h)) (overlapUpper b (e h)) := by
  ext x
  simp only [additiveOverlap, Finset.mem_filter, mem_coordinateLatticeBox, map_add,
    Pi.add_apply, overlapLower, overlapUpper]
  constructor
  · rintro ⟨hx, hxh⟩ i
    have hi := hx i
    have hih := hxh i
    omega
  · intro hx
    constructor <;> intro i <;> have hi := hx i <;> omega

/-- Pulling back a coordinate box along an actual additive equivalence preserves
the geometric product estimate, with each basis direction explicit. -/
theorem norm_addChar_lattice_box_le (e : R ≃+ (ι → ℤ)) (χ : AddChar R ℂ)
    (hχ : ∀ x, ‖χ x‖ = 1) (a b : ι → ℤ) :
    ‖∑ x ∈ coordinateLatticeBox e a b, χ x‖ ≤
      ∏ i, characterIntervalBound (b i+1-a i).toNat (χ (e.symm (Pi.single i 1))) := by
  have heq : (∑ x ∈ coordinateLatticeBox e a b, χ x) =
      ∑ y ∈ coordinateIntervalBox a b, χ (e.symm y) := by
    unfold coordinateLatticeBox
    rw [Finset.sum_image]
    exact fun a ha b hb hab => e.symm.injective hab
  rw [heq]
  exact norm_addChar_coordinate_box_le (χ.compAddMonoidHom e.symm.toAddMonoidHom)
    (fun x => hχ _) a b

theorem norm_addChar_doubleOverlap_le (e : R ≃+ (ι → ℤ)) (χ : AddChar R ℂ)
    (hχ : ∀ x, ‖χ x‖ = 1) (a b : ι → ℤ) (h j : R) :
    ‖∑ x ∈ additiveOverlap (additiveOverlap (coordinateLatticeBox e a b) h) j, χ x‖ ≤
      ∏ i, characterIntervalBound (b i+1-a i).toNat (χ (e.symm (Pi.single i 1))) := by
  rw [additiveOverlap_coordinateLatticeBox, additiveOverlap_coordinateLatticeBox]
  apply (norm_addChar_lattice_box_le e χ hχ _ _).trans
  apply Finset.prod_le_prod
  · intro i hi
    exact characterIntervalBound_nonneg _ _
  · intro i hi
    apply characterIntervalBound_mono
    apply Int.toNat_le_toNat
    dsimp [overlapUpper, overlapLower]
    omega

end LatticeBoxes

section RingCharacters
variable {R ι : Type*} [CommRing R] [Fintype ι]

/-- The actual character arising from multiplication and integral lattice coordinates. -/
def linearLatticeCharacter (coord : R →+ (ι → ℤ)) (a : R)
    (θ : ι → AddCircle (1 : ℝ)) : AddChar R ℂ where
  toFun x := latticeCharacter (coord (a*x)) θ
  map_zero_eq_one' := by simp only [mul_zero, map_zero, WaringSiegel.latticeCharacter_zero]
  map_add_eq_mul' x y := by rw [mul_add, map_add, WaringSiegel.latticeCharacter_add]

theorem linearLatticeCharacter_norm (coord : R →+ (ι → ℤ)) (a x : R)
    (θ : ι → AddCircle (1 : ℝ)) : ‖linearLatticeCharacter coord a θ x‖ = 1 :=
  norm_latticeCharacter_eq_one _ _

end RingCharacters
end WaringSiegel.WSL2
