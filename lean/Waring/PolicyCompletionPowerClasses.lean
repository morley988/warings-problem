import Waring.PolicyCompletionLinearRootSampling

/-!
# The weighted power-divisor classes in the basic coefficient estimate

The final source variable has weight j^(-2). If u divides j^d then the
valuation ceiling root of u divides j. Summing reciprocal squares over
that exact class supplies the exponent 2/d, which is 1/k when d=2k.
-/

noncomputable section
open scoped BigOperators Classical
namespace Waring.PolicyCompletionPowerClasses
open CubicDivisorClasses

theorem reciprocal_square_le_telescope {x : ℝ} (hx : 1≤x) :
    1/x^2≤2/x-2/(x+1) := by
  have hxp : 0<x := zero_lt_one.trans_le hx
  have hx1 : 0<x+1 := by linarith
  have hid : 2/x-2/(x+1)=2/(x*(x+1)) := by field_simp; ring
  rw [hid]
  apply (div_le_div_iff₀ (pow_pos hxp _) (mul_pos hxp hx1)).mpr
  have hh := mul_le_mul_of_nonneg_left hx hxp.le
  nlinarith

theorem finite_reciprocal_squares (N : ℕ) :
    (∑n∈Finset.range N,1/((n : ℝ)+1)^2)≤2 := by
  have hmain : ∀N : ℕ,(∑n∈Finset.range N,1/((n : ℝ)+1)^2)≤2-2/((N : ℝ)+1) := by
    intro N
    induction N with
    | zero => norm_num
    | succ N ih =>
      rw [Finset.sum_range_succ]
      have ht := reciprocal_square_le_telescope (x := (N : ℝ)+1)
        (by have := Nat.cast_nonneg (α := ℝ) N; linarith)
      push_cast
      nlinarith
  exact (hmain N).trans (sub_le_self _ (by positivity))

def powerBase (d u : ℕ) : ℕ := Nat.ceilRoot d u

theorem powerBase_pos {d u : ℕ} (hd : 0<d) (hu : 0<u) : 0<powerBase d u :=
  Nat.pos_of_ne_zero (Nat.ceilRoot_ne_zero.mpr ⟨hd.ne',hu.ne'⟩)

theorem powerBase_dvd_iff {d : ℕ} (hd : 0<d) (u h : ℕ) :
    powerBase d u∣h ↔ u∣h^d := (Nat.dvd_pow_iff_ceilRoot_dvd hd.ne').symm

theorem le_powerBase_pow {d u : ℕ} (hd : 0<d) (hu : 0<u) :
    u≤powerBase d u^d :=
  Nat.le_of_dvd (pow_pos (powerBase_pos hd hu) _) (Nat.dvd_ceilRoot_pow hd.ne')

def powerClass (N d u : ℕ) : ℝ :=
  ∑h∈(Finset.Icc 1 N).filter (fun h=>u∣h^d),1/(h : ℝ)^2

theorem powerClass_bound {d u : ℕ} (hd : 0<d) (hu : 0<u) (N : ℕ) :
    powerClass N d u≤2/(powerBase d u : ℝ)^2 := by
  let b := powerBase d u
  have hb := powerBase_pos hd hu
  have hfilter : (Finset.Icc 1 N).filter (fun h=>u∣h^d)=
      (Finset.Icc 1 N).filter (fun h=>b∣h) := by
    ext h
    simp only [Finset.mem_filter,powerBase_dvd_iff hd,b]
  have hinj : Set.InjOn (fun n=>b*(n+1)) (Finset.range (N/b)) := by
    intro n hn m hm hnm
    have hh := Nat.eq_of_mul_eq_mul_left hb hnm
    omega
  unfold powerClass
  rw [hfilter,positive_multiples_eq_image N b hb,Finset.sum_image hinj]
  calc
    _ = (1/(b : ℝ)^2)*∑n∈Finset.range (N/b),1/((n : ℝ)+1)^2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      push_cast
      rw [mul_pow,← one_div_mul_one_div]
    _ ≤ (1/(b : ℝ)^2)*2 :=
      mul_le_mul_of_nonneg_left (finite_reciprocal_squares _) (by positivity)
    _ = _ := by dsimp [b]; ring

/-- The exact gain 2/d in a denominator class. The hypothesis d>=6 is
precisely what makes 2/d no larger than the cube-root exponent. -/
theorem power_divisor_weight_le {d : ℕ} (hd : 6≤d) {u b L : ℝ}
    (hu : 0<u) (hb : 0<b) (hub : u≤b^d) (huL : u≤L) :
    u^(1/3 : ℝ)/(b^2*L^(1/3 : ℝ))≤1/L^(2/(d : ℝ)) := by
  have hdR : (0 : ℝ)<d := by exact_mod_cast (show 0<d by omega)
  have hL : 0<L := hu.trans_le huL
  have hbeta : 0<2/(d : ℝ) := by positivity
  have hgap : 0≤(1/3 : ℝ)-2/(d : ℝ) := by
    have h6 : (6 : ℝ)≤d := by exact_mod_cast hd
    have hh : 2/(d : ℝ)≤(1/3 : ℝ) := (div_le_iff₀ hdR).mpr (by linarith)
    linarith
  have hubeta : u^(2/(d : ℝ))≤b^2 := by
    calc
      _ ≤ (b^d)^(2/(d : ℝ)) := Real.rpow_le_rpow hu.le hub hbeta.le
      _ = b^2 := by
        rw [← Real.rpow_natCast_mul hb.le]
        have he : (d : ℝ)*(2/(d : ℝ))=2 := by field_simp
        rw [he,Real.rpow_two]
  have hpow : u^(1/3 : ℝ)≤b^2*L^((1/3 : ℝ)-2/(d : ℝ)) := by
    calc
      _ = u^(2/(d : ℝ))*u^((1/3 : ℝ)-2/(d : ℝ)) := by
        rw [← Real.rpow_add hu]
        congr 1
        ring
      _ ≤ _ := mul_le_mul hubeta (Real.rpow_le_rpow hu.le huL hgap)
        (Real.rpow_nonneg hu.le _) (sq_nonneg b)
  have hLa : 0<L^(1/3 : ℝ) := Real.rpow_pos_of_pos hL _
  have hLb : 0<L^(2/(d : ℝ)) := Real.rpow_pos_of_pos hL _
  calc
    _ ≤ (b^2*L^((1/3 : ℝ)-2/(d : ℝ)))/(b^2*L^(1/3 : ℝ)) :=
      div_le_div_of_nonneg_right hpow (by positivity)
    _ = 1/L^(2/(d : ℝ)) := by
      rw [Real.rpow_sub hL]
      field_simp

theorem weighted_powerClass_bound {d u : ℕ} (hd : 6≤d) (hu : 0<u)
    (N : ℕ) {L : ℝ} (huL : (u : ℝ)≤L) :
    (∑j∈(Finset.Icc 1 N).filter (fun j=>u∣j^d),
      (u : ℝ)^(1/3 : ℝ)/((j : ℝ)^2*L^(1/3 : ℝ)))≤2/L^(2/(d : ℝ)) := by
  have hdp : 0<d := by omega
  have hb : (0 : ℝ)<powerBase d u := by exact_mod_cast powerBase_pos hdp hu
  have huR : (0 : ℝ)<u := by exact_mod_cast hu
  have hL : 0<L := huR.trans_le huL
  have hconstant : 0≤(u : ℝ)^(1/3 : ℝ)/L^(1/3 : ℝ) := by positivity
  calc
    _ = ((u : ℝ)^(1/3 : ℝ)/L^(1/3 : ℝ))*powerClass N d u := by
      unfold powerClass
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    _ ≤ ((u : ℝ)^(1/3 : ℝ)/L^(1/3 : ℝ))*(2/(powerBase d u : ℝ)^2) :=
      mul_le_mul_of_nonneg_left (powerClass_bound hdp hu N) hconstant
    _ = 2*((u : ℝ)^(1/3 : ℝ)/((powerBase d u : ℝ)^2*L^(1/3 : ℝ))) := by
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    _ ≤ 2*(1/L^(2/(d : ℝ))) := mul_le_mul_of_nonneg_left
      (power_divisor_weight_le hd huR hb (by exact_mod_cast le_powerBase_pow hdp hu) huL)
      (by norm_num)
    _ = _ := by ring

#print axioms powerClass_bound
#print axioms weighted_powerClass_bound
end Waring.PolicyCompletionPowerClasses
