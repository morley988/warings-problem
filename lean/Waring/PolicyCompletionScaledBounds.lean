import Waring.CartesianFloorScales
import Waring.FixedCoefficientPhase

/-!
# Fixed dilations of the literal Cartesian floor boxes

The source iteration uses floor(K P^e) in every coordinate, with a fixed
K at least one. The product of these actual integer lengths and its padded
cutoff have the same exponents as the undilated box. All constants and
rounding losses are kept explicitly.
-/

noncomputable section
open scoped BigOperators
namespace Waring.PolicyCompletionScaledBounds
open ProductMultiplicity CartesianProductSampling CartesianFloorScales

def scaledBounds {r : ℕ} (K P : ℝ) (e : Fin r → ℝ) : Fin r → ℕ :=
  fun i => ⌊K*P^(e i)⌋₊

def scaledVolume {r : ℕ} (K P : ℝ) (e : Fin r → ℝ) : ℕ :=
  tupleProduct (scaledBounds K P e)

def scaledCutoff {r : ℕ} (K P : ℝ) (e : Fin r → ℝ) : ℕ :=
  ⌈K^r*P^(∑ i, e i)⌉₊

theorem scaled_coordinate_powers {r : ℕ} (K : ℝ) (hK : 1 ≤ K)
    (e : Fin r → ℝ) (he : ∀ i, 0 < e i) {P : ℝ}
    (hP : coordinateThreshold e ≤ P) (i : Fin r) : 2 ≤ K*P^(e i) := by
  have hp := coordinate_powers_ge_two e he hP i
  exact hp.trans (le_mul_of_one_le_left (by linarith) hK)

theorem scaled_bounds_pos {r : ℕ} {K P : ℝ} (e : Fin r → ℝ)
    (hpow : ∀ i, 2 ≤ K*P^(e i)) (i : Fin r) : 0 < scaledBounds K P e i := by
  exact Nat.floor_pos.mpr (by linarith [hpow i])

theorem scaled_power_product {r : ℕ} {K P : ℝ} (e : Fin r → ℝ)
    (he : ∀ i, 0 ≤ e i) (hP : 0 ≤ P) :
    (∏ i, K*P^(e i))=K^r*P^(∑ i, e i) := by
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  rw [Real.rpow_sum_of_nonneg hP (fun i _ => he i)]

theorem scaled_volume_sandwich {r : ℕ} {K P : ℝ} (hK : 0 ≤ K)
    (e : Fin r → ℝ) (he : ∀ i, 0 ≤ e i) (hP : 0 ≤ P)
    (hpow : ∀ i, 2 ≤ K*P^(e i)) :
    K^r*P^(∑ i, e i)/(2 : ℝ)^r ≤ (scaledVolume K P e : ℝ) ∧
      (scaledVolume K P e : ℝ) ≤ K^r*P^(∑ i, e i) := by
  have hcast : (scaledVolume K P e : ℝ)=∏ i, (⌊K*P^(e i)⌋₊ : ℝ) := by
    simp only [scaledVolume,tupleProduct,scaledBounds,Nat.cast_prod]
  have hprod := scaled_power_product (K := K) e he hP
  constructor
  · rw [hcast,← hprod]
    have hh := Finset.prod_le_prod
      (fun i (_ : i ∈ (Finset.univ : Finset (Fin r))) =>
        div_nonneg (mul_nonneg hK (Real.rpow_nonneg hP _)) (by norm_num : (0 : ℝ) ≤ 2))
      (fun i _ => half_le_floor (hpow i))
    simpa only [Finset.prod_div_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin] using hh
  · rw [hcast,← hprod]
    exact Finset.prod_le_prod (fun i _ => by positivity)
      (fun i _ => Nat.floor_le (mul_nonneg hK (Real.rpow_nonneg hP _)))

theorem scaled_volume_le_cutoff {r : ℕ} {K P : ℝ} (hK : 0 ≤ K)
    (e : Fin r → ℝ) (he : ∀ i, 0 ≤ e i) (hP : 0 ≤ P)
    (hpow : ∀ i, 2 ≤ K*P^(e i)) : scaledVolume K P e ≤ scaledCutoff K P e := by
  have hh := (scaled_volume_sandwich hK e he hP hpow).2.trans
    (Nat.le_ceil (K^r*P^(∑ i, e i)))
  exact_mod_cast hh

theorem scaled_cutoff_le_twice_power {r : ℕ} {K P : ℝ} (hK : 1 ≤ K)
    (e : Fin r → ℝ) (he : ∀ i, 0 ≤ e i) (hP : 1 ≤ P) :
    (scaledCutoff K P e : ℝ) ≤ 2*(K^r*P^(∑ i, e i)) := by
  exact ceil_le_twice (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hK)
    (Real.one_le_rpow hP (Finset.sum_nonneg (fun i _ => he i))))

theorem scaled_cutoff_le_volume {r : ℕ} {K P : ℝ} (hK : 1 ≤ K)
    (e : Fin r → ℝ) (he : ∀ i, 0 ≤ e i) (hP : 1 ≤ P)
    (hpow : ∀ i, 2 ≤ K*P^(e i)) :
    (scaledCutoff K P e : ℝ) ≤ (2 : ℝ)^(r+1)*(scaledVolume K P e : ℝ) := by
  have hlow := (scaled_volume_sandwich (zero_le_one.trans hK) e he
    (zero_le_one.trans hP) hpow).1
  have hh := (div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ)^r)).mp hlow
  calc
    _ ≤ 2*(K^r*P^(∑ i, e i)) := scaled_cutoff_le_twice_power hK e he hP
    _ ≤ 2*((2 : ℝ)^r*(scaledVolume K P e : ℝ)) :=
      mul_le_mul_of_nonneg_left (by simpa only [mul_comm] using hh) (by norm_num)
    _ = _ := by rw [pow_succ]; ring

theorem scaled_cutoff_le_power {r : ℕ} {K P : ℝ} (hK : 1 ≤ K)
    (e : Fin r → ℝ) (he : ∀ i, 0 ≤ e i) (hP : 1 ≤ P)
    (hconstant : 2*K^r ≤ P) :
    (scaledCutoff K P e : ℝ) ≤ P^((∑ i, e i)+1) := by
  have hPp : 0 < P := zero_lt_one.trans_le hP
  calc
    _ ≤ 2*(K^r*P^(∑ i, e i)) := scaled_cutoff_le_twice_power hK e he hP
    _ = (2*K^r)*P^(∑ i, e i) := by ring
    _ ≤ P*P^(∑ i, e i) := mul_le_mul_of_nonneg_right hconstant
      (Real.rpow_nonneg hPp.le _)
    _ = _ := by
      nth_rw 1 [← Real.rpow_one P]
      rw [← Real.rpow_add hPp]
      congr 1
      ring

theorem scaled_bounds_cons_one {r : ℕ} (K P : ℝ) (e : Fin r → ℝ) :
    scaledBounds K P (Fin.cons 1 e)=Fin.cons ⌊K*P⌋₊ (scaledBounds K P e) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [scaledBounds,Fin.cons_zero,Real.rpow_one]
  · simp only [scaledBounds,Fin.cons_succ]

theorem eventual_scaled_scales {r : ℕ} (K : ℝ) (hK : 1 ≤ K)
    (e : Fin r → ℝ) (he : ∀ i, 0 < e i) :
    ∃ P₀ : ℝ, 2 ≤ P₀ ∧ ∀ P : ℝ, P₀ ≤ P →
      (∀ i, 0 < scaledBounds K P e i) ∧
      K^r*P^(∑ i, e i)/(2 : ℝ)^r ≤ (scaledVolume K P e : ℝ) ∧
      (scaledVolume K P e : ℝ) ≤ K^r*P^(∑ i, e i) ∧
      scaledVolume K P e ≤ scaledCutoff K P e ∧
      (scaledCutoff K P e : ℝ) ≤ (2 : ℝ)^(r+1)*(scaledVolume K P e : ℝ) ∧
      (scaledCutoff K P e : ℝ) ≤ P^((∑ i, e i)+1) := by
  let P₀ := max (max 2 (coordinateThreshold e)) (2*K^r)
  refine ⟨P₀,(le_max_left 2 _).trans (le_max_left _ _),?_⟩
  intro P hP
  have hP2 : 2 ≤ P := ((le_max_left 2 _).trans (le_max_left _ _)).trans hP
  have hP1 : 1 ≤ P := by linarith
  have hPe : coordinateThreshold e ≤ P :=
    ((le_max_right 2 _).trans (le_max_left _ _)).trans hP
  have hp := scaled_coordinate_powers K hK e he hPe
  have hs := scaled_volume_sandwich (zero_le_one.trans hK) e
    (fun i => (he i).le) (zero_le_one.trans hP1) hp
  exact ⟨scaled_bounds_pos e hp,hs.1,hs.2,
    scaled_volume_le_cutoff (zero_le_one.trans hK) e (fun i => (he i).le)
      (zero_le_one.trans hP1) hp,
    scaled_cutoff_le_volume hK e (fun i => (he i).le) hP1 hp,
    scaled_cutoff_le_power hK e (fun i => (he i).le) hP1 ((le_max_right _ _).trans hP)⟩

#print axioms eventual_scaled_scales
#print axioms scaled_bounds_cons_one
end Waring.PolicyCompletionScaledBounds
