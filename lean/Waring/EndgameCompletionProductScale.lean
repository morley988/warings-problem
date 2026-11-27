import Waring.EndgameCompletionProductErrors

/-! # Integer product-box scales for every sufficiently large target -/

noncomputable section
open Filter
open scoped Topology
namespace Waring.EndgameCompletion

def floorPowerRoot (d n : ℕ) : ℕ := ⌊(n : ℝ)^(1/(d : ℝ))⌋₊

theorem realPowerRoot_pow (d n : ℕ) (hd : 0<d) :
    ((n : ℝ)^(1/(d : ℝ)))^d=(n : ℝ) := by
  have hdR : (d : ℝ)≠0 := by exact_mod_cast hd.ne'
  rw [← Real.rpow_mul_natCast (Nat.cast_nonneg _),one_div_mul_cancel hdR,Real.rpow_one]

theorem floorPowerRoot_pos (d n : ℕ) (hd : 0<d) (hn : 1≤n) : 1≤floorPowerRoot d n := by
  have hnR : (1 : ℝ)≤n := by exact_mod_cast hn
  apply (Nat.le_floor_iff (Real.rpow_nonneg (Nat.cast_nonneg _) _)).mpr
  simpa only [Nat.cast_one] using Real.one_le_rpow hnR (by positivity : (0 : ℝ)≤1/(d : ℝ))

theorem floorPowerRoot_pow_le (d n : ℕ) (hd : 0<d) :
    (floorPowerRoot d n : ℝ)^d≤n := by
  calc
    _ ≤ ((n : ℝ)^(1/(d : ℝ)))^d := pow_le_pow_left₀ (Nat.cast_nonneg _)
      (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg _) _)) d
    _ = _ := realPowerRoot_pow d n hd

theorem floorPowerRoot_tendsto (d : ℕ) (hd : 0<d) :
    Tendsto (floorPowerRoot d) atTop atTop := by
  have ht : Tendsto (fun n : ℕ=>(n : ℝ)^(1/(d : ℝ))) atTop atTop :=
    (tendsto_rpow_atTop (by positivity : (0 : ℝ)<1/(d : ℝ))).comp tendsto_natCast_atTop_atTop
  exact tendsto_nat_floor_atTop.comp ht

theorem floorPowerRoot_ratio_tendsto (d : ℕ) (hd : 0<d) :
    Tendsto (fun n : ℕ=>(n : ℝ)/(floorPowerRoot d n : ℝ)^d) atTop (𝓝 1) := by
  have ht : Tendsto (fun n : ℕ=>(n : ℝ)^(1/(d : ℝ))) atTop atTop :=
    (tendsto_rpow_atTop (by positivity : (0 : ℝ)<1/(d : ℝ))).comp tendsto_natCast_atTop_atTop
  have hr := tendsto_nat_floor_div_atTop.comp ht
  have hi := (hr.inv₀ (by norm_num : (1 : ℝ)≠0)).pow d
  have he (n : ℕ) : (((floorPowerRoot d n : ℝ)/(n : ℝ)^(1/(d : ℝ)))⁻¹)^d=
      (n : ℝ)/(floorPowerRoot d n : ℝ)^d := by
    rw [inv_div,div_pow,realPowerRoot_pow d n hd]
  have hi' : Tendsto (fun n : ℕ=>
      (((floorPowerRoot d n : ℝ)/(n : ℝ)^(1/(d : ℝ)))⁻¹)^d) atTop (𝓝 1) := by
    simpa only [Function.comp_apply,inv_one,one_pow,floorPowerRoot] using hi
  simpa only [he] using hi'

def productScaleM (k L n : ℕ) : ℕ := floorPowerRoot (k*L) n

def productScaleP (k L n : ℕ) : ℝ := (productScaleM k L n : ℝ)^L

def productScaleTheta (k L n : ℕ) : ℝ := (n : ℝ)/(productScaleP k L n)^k

theorem productScaleM_pos (k L n : ℕ) (hk : 0<k) (hL : 0<L) (hn : 1≤n) :
    1≤productScaleM k L n := floorPowerRoot_pos (k*L) n (Nat.mul_pos hk hL) hn

theorem productScaleM_tendsto (k L : ℕ) (hk : 0<k) (hL : 0<L) :
    Tendsto (productScaleM k L) atTop atTop :=
  floorPowerRoot_tendsto (k*L) (Nat.mul_pos hk hL)

theorem productScaleP_tendsto (k L : ℕ) (hk : 0<k) (hL : 0<L) :
    Tendsto (productScaleP k L) atTop atTop := by
  have ht : Tendsto (fun n : ℕ=>(productScaleM k L n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (productScaleM_tendsto k L hk hL)
  exact (tendsto_pow_atTop hL.ne').comp ht

theorem productScaleTheta_tendsto (k L : ℕ) (hk : 0<k) (hL : 0<L) :
    Tendsto (productScaleTheta k L) atTop (𝓝 1) := by
  have ht := floorPowerRoot_ratio_tendsto (k*L) (Nat.mul_pos hk hL)
  change Tendsto (fun n : ℕ=>(n : ℝ)/((productScaleM k L n : ℝ)^L)^k) atTop (𝓝 1)
  simpa only [productScaleM,← pow_mul,Nat.mul_comm L k] using ht

theorem productScaleTheta_ge_one (k L n : ℕ) (hk : 0<k) (hL : 0<L) (hn : 1≤n) :
    1≤productScaleTheta k L n := by
  have hM : (0 : ℝ)<productScaleM k L n := by exact_mod_cast productScaleM_pos k L n hk hL hn
  apply (one_le_div (pow_pos (pow_pos hM L) k)).mpr
  simpa only [productScaleP,productScaleM,← pow_mul,Nat.mul_comm L k] using
    floorPowerRoot_pow_le (k*L) n (Nat.mul_pos hk hL)

theorem productScaleTheta_eventually_interval (k L : ℕ) (hk : 0<k) (hL : 0<L)
    {η : ℝ} (hη : 0<η) :
    ∀ᶠ n in atTop,1≤productScaleM k L n ∧ productScaleTheta k L n∈Set.Icc 1 (1+η) := by
  have ht := (productScaleTheta_tendsto k L hk hL).eventually_lt_const (by linarith : (1 : ℝ)<1+η)
  filter_upwards [eventually_ge_atTop 1,ht] with n hn hθ
  exact ⟨productScaleM_pos k L n hk hL hn,productScaleTheta_ge_one k L n hk hL hn,hθ.le⟩

theorem exists_product_rank {η : ℝ} (hη : 0<η) :
    ∃ L : ℕ,1≤L ∧ 1≤(L : ℝ)*η := by
  obtain ⟨L,hL⟩ := exists_nat_gt (1/η)
  refine ⟨L+1,by omega,?_⟩
  have hh := (div_lt_iff₀ hη).mp hL
  push_cast
  nlinarith

#print axioms productScaleTheta_tendsto
#print axioms productScaleTheta_eventually_interval
end Waring.EndgameCompletion
