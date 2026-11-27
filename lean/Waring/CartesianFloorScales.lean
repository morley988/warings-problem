import Waring.CartesianProductSampling

/-!
# Exact floor/ceiling scales for Cartesian shift products

Each actual range has length floor(P^e_i). Once every P^e_i is at least two,
the actual product volume lies between 2^(-rank) P^(sum e_i) and P^(sum e_i).
The padded cutoff ceil(P^(sum e_i)) is therefore at most 2^(rank+1) times
that actual volume. Explicit finite thresholds make the statements eventual
without introducing a size-comparison assumption.
-/

noncomputable section
open scoped BigOperators
namespace Waring.CartesianFloorScales
open ProductMultiplicity CartesianProductSampling

def floorBounds {r : ℕ} (P : ℝ) (e : Fin r → ℝ) : Fin r → ℕ := fun i => ⌊P^(e i)⌋₊
def actualVolume {r : ℕ} (P : ℝ) (e : Fin r → ℝ) : ℕ := tupleProduct (floorBounds P e)
def paddedCutoff {r : ℕ} (P : ℝ) (e : Fin r → ℝ) : ℕ := ⌈P^(∑ i, e i)⌉₊
def coordinateThreshold {r : ℕ} (e : Fin r → ℝ) : ℝ := max 1 (∑ i, (2:ℝ)^(1/e i))

theorem half_le_floor {x : ℝ} (hx : 2 ≤ x) : x/2 ≤ (⌊x⌋₊:ℝ) := by
  have hh := Nat.sub_one_lt_floor x
  linarith

theorem ceil_le_twice {x : ℝ} (hx : 1 ≤ x) : (⌈x⌉₊:ℝ) ≤ 2*x := by
  have hh := Nat.ceil_lt_add_one (show 0 ≤ x by linarith)
  linarith

theorem coordinateThreshold_ge_one {r : ℕ} (e : Fin r → ℝ) : 1 ≤ coordinateThreshold e :=
  le_max_left _ _

theorem coordinate_powers_ge_two {r : ℕ} (e : Fin r → ℝ) (he : ∀ i, 0 < e i)
    {P : ℝ} (hP : coordinateThreshold e ≤ P) (i : Fin r) : 2 ≤ P^(e i) := by
  have hsum : (2:ℝ)^(1/e i) ≤ ∑ l, (2:ℝ)^(1/e l) :=
    Finset.single_le_sum (f:=fun l : Fin r => (2:ℝ)^(1/e l))
      (fun l _ => Real.rpow_nonneg (by norm_num) _) (Finset.mem_univ i)
  have hbound : (2:ℝ)^(1/e i) ≤ P := hsum.trans ((le_max_right _ _).trans hP)
  have hh := Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) _)
    hbound (he i).le
  rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),
    div_mul_cancel₀ 1 (he i).ne', Real.rpow_one] at hh
  exact hh

theorem floorBounds_pos {r : ℕ} (e : Fin r → ℝ) {P : ℝ}
    (hpow : ∀ i, 2 ≤ P^(e i)) (i : Fin r) : 0 < floorBounds P e i := by
  have hh := half_le_floor (hpow i)
  have hp : (0:ℝ) < (floorBounds P e i:ℝ) := by dsimp [floorBounds]; linarith [hpow i]
  exact_mod_cast hp

theorem actualVolume_sandwich {r : ℕ} (e : Fin r → ℝ) (he : ∀ i, 0 ≤ e i)
    {P : ℝ} (hP : 0 ≤ P) (hpow : ∀ i, 2 ≤ P^(e i)) :
    P^(∑ i, e i)/(2:ℝ)^r ≤ (actualVolume P e:ℝ) ∧
      (actualVolume P e:ℝ) ≤ P^(∑ i, e i) := by
  have hprod : P^(∑ i, e i) = ∏ i, P^(e i) :=
    Real.rpow_sum_of_nonneg hP (fun i _ => he i)
  have hcast : (actualVolume P e:ℝ) = ∏ i, (⌊P^(e i)⌋₊:ℝ) := by
    simp only [actualVolume, tupleProduct, floorBounds, Nat.cast_prod]
  constructor
  · rw [hcast, hprod]
    have hh := Finset.prod_le_prod
      (fun i (_ : i ∈ (Finset.univ : Finset (Fin r))) =>
        div_nonneg (Real.rpow_nonneg hP _) (by norm_num : (0:ℝ) ≤ 2))
      (fun i _ => half_le_floor (hpow i))
    simpa only [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin] using hh
  · rw [hcast, hprod]
    exact Finset.prod_le_prod (fun i _ => by positivity)
      (fun i _ => Nat.floor_le (Real.rpow_nonneg hP _))

theorem actualVolume_le_paddedCutoff {r : ℕ} (e : Fin r → ℝ) (he : ∀ i, 0 ≤ e i)
    {P : ℝ} (hP : 0 ≤ P) (hpow : ∀ i, 2 ≤ P^(e i)) :
    actualVolume P e ≤ paddedCutoff P e := by
  have hh := (actualVolume_sandwich e he hP hpow).2.trans (Nat.le_ceil (P^(∑ i, e i)))
  exact_mod_cast hh

/-- The exact padding factor used after product grouping. It compares the
ceiling cutoff with the actual product of floors, not with an ideal volume. -/
theorem paddedCutoff_le_actualVolume {r : ℕ} (e : Fin r → ℝ) (he : ∀ i, 0 ≤ e i)
    {P : ℝ} (hP : 1 ≤ P) (hpow : ∀ i, 2 ≤ P^(e i)) :
    (paddedCutoff P e:ℝ) ≤ (2:ℝ)^(r+1)*(actualVolume P e:ℝ) := by
  have hsum : 0 ≤ ∑ i, e i := Finset.sum_nonneg (fun i _ => he i)
  have hceil := ceil_le_twice (Real.one_le_rpow hP hsum)
  have hlow := (actualVolume_sandwich e he (zero_le_one.trans hP) hpow).1
  have hh := (div_le_iff₀ (by positivity : (0:ℝ) < (2:ℝ)^r)).mp hlow
  change (⌈P^(∑ i, e i)⌉₊:ℝ) ≤ _
  calc
    _ ≤ 2*P^(∑ i, e i) := hceil
    _ ≤ 2*((2:ℝ)^r*(actualVolume P e:ℝ)) :=
      mul_le_mul_of_nonneg_left (by simpa only [mul_comm] using hh) (by norm_num)
    _ = _ := by rw [pow_succ]; ring

theorem paddedCutoff_le_twice_power {r : ℕ} (e : Fin r → ℝ) (he : ∀ i, 0 ≤ e i)
    {P : ℝ} (hP : 1 ≤ P) :
    (paddedCutoff P e:ℝ) ≤ 2*P^(∑ i, e i) :=
  ceil_le_twice (Real.one_le_rpow hP (Finset.sum_nonneg (fun i _ => he i)))

/-- All floor/ceiling inequalities hold above one explicit finite threshold. -/
theorem eventual_cartesian_scales {r : ℕ} (e : Fin r → ℝ) (he : ∀ i, 0 < e i) :
    ∃ P₀ : ℝ, 1 ≤ P₀ ∧ ∀ P : ℝ, P₀ ≤ P →
      (∀ i, 0 < floorBounds P e i) ∧
      P^(∑ i, e i)/(2:ℝ)^r ≤ (actualVolume P e:ℝ) ∧
      (actualVolume P e:ℝ) ≤ P^(∑ i, e i) ∧
      actualVolume P e ≤ paddedCutoff P e ∧
      (paddedCutoff P e:ℝ) ≤ (2:ℝ)^(r+1)*(actualVolume P e:ℝ) := by
  refine ⟨coordinateThreshold e, coordinateThreshold_ge_one e, ?_⟩
  intro P hP
  have hP1 := (coordinateThreshold_ge_one e).trans hP
  have hp := coordinate_powers_ge_two e he hP
  have hs := actualVolume_sandwich e (fun i => (he i).le) (zero_le_one.trans hP1) hp
  exact ⟨floorBounds_pos e hp, hs.1, hs.2,
    actualVolume_le_paddedCutoff e (fun i => (he i).le) (zero_le_one.trans hP1) hp,
    paddedCutoff_le_actualVolume e (fun i => (he i).le) hP1 hp⟩

/-- The verified source premise sum(e)>1 implies the actual product of
floors eventually dominates P, as required by the quadratic z2 theorem. -/
theorem eventual_actualVolume_ge_P {r : ℕ} (e : Fin r → ℝ)
    (he : ∀ i, 0 < e i) (hsum : 1 < ∑ i, e i) :
    ∃ P₀ : ℝ, 1 ≤ P₀ ∧ ∀ P : ℝ, P₀ ≤ P → P ≤ (actualVolume P e:ℝ) := by
  let P₀ := max (coordinateThreshold e) (((2:ℝ)^r)^(1/((∑ i, e i)-1)))
  have hP01 : 1 ≤ P₀ := (coordinateThreshold_ge_one e).trans (le_max_left _ _)
  refine ⟨P₀,hP01,?_⟩
  intro P hP
  have hP1 := hP01.trans hP
  have hPp : 0 < P := zero_lt_one.trans_le hP1
  have hE : 0 < (∑ i, e i)-1 := by linarith
  have hroot : ((2:ℝ)^r)^(1/((∑ i, e i)-1)) ≤ P := (le_max_right _ _).trans hP
  have hh := Real.rpow_le_rpow (Real.rpow_nonneg (by positivity : (0:ℝ) ≤ (2:ℝ)^r) _)
    hroot hE.le
  rw [← Real.rpow_mul (by positivity : (0:ℝ) ≤ (2:ℝ)^r),
    div_mul_cancel₀ 1 hE.ne', Real.rpow_one] at hh
  have hm := mul_le_mul_of_nonneg_left hh hPp.le
  have heq : P*P^((∑ i, e i)-1) = P^(∑ i, e i) := by
    calc
      _ = P^(1:ℝ)*P^((∑ i, e i)-1) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hPp]; congr 1; ring
  rw [heq] at hm
  have hlow : P ≤ P^(∑ i, e i)/(2:ℝ)^r :=
    (le_div_iff₀ (by positivity)).mpr hm
  exact hlow.trans (actualVolume_sandwich e (fun i => (he i).le) hPp.le
    (coordinate_powers_ge_two e he ((le_max_left _ _).trans hP))).1

/-- Appending r ordinary shifts of bound N gives exactly N^r times the
original h-product volume. -/
theorem tupleProduct_append_constant {j r : ℕ} (bounds : Fin j → ℕ) (N : ℕ) :
    tupleProduct (Fin.append bounds (fun _ : Fin r => N)) = tupleProduct bounds*N^r := by
  simp only [tupleProduct, Fin.prod_univ_add, Fin.append_left, Fin.append_right,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]

#print axioms eventual_cartesian_scales
#print axioms eventual_actualVolume_ge_P
#print axioms paddedCutoff_le_actualVolume

end Waring.CartesianFloorScales
