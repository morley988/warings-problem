import Waring.PolicyCompletionBasicLoss
import Waring.FloorCoefficientResources

/-!
# Source cap inequalities imply the literal integer sampling ranges

The floor in H, ceilings in J and the coefficient block, and every fixed
constant are retained. The auxiliary cutoff is P^(b-delta). This file
proves the numerical prerequisites of the finite basic theorem from the
four cap inequalities, with explicit epsilon slack.
-/

noncomputable section
open scoped BigOperators Classical
namespace Waring.PolicyCompletionBasicRanges
open RationalHeight PolicyCompletionBasicLinear CartesianFloorScales

def sourceH (P h : ℝ) : ℕ := ⌊P^h⌋₊
def sourceJ (P j : ℝ) : ℕ := ⌈P^j⌉₊
def sourceN (P phi R : ℝ) : ℕ := ⌈P^phi*R⌉₊
def sourceV (P h j : ℝ) : ℝ := (sourceH P h : ℝ)^3*sourceJ P j
def boxExponent (h j phi : ℝ) : ℝ := 3*h+j+phi+4
def sourceConstant (d c : ℕ) : ℝ := 64*((d : ℝ)+1)*(2 : ℝ)^d+16+8*c

structure FloorRanges (d c : ℕ) (P R h j phi b δ : ℝ) : Prop where
  h_pos : 0<sourceH P h
  j_pos : 0<sourceJ P j
  n_pos : 0<sourceN P phi R
  n_lower : P^phi≤(sourceN P phi R : ℝ)
  n_upper : (sourceN P phi R : ℝ)≤2*P^phi*R
  n_scale : (sourceN P phi R : ℝ)≤P^(boxExponent h j phi)
  h_scale : (sourceH P h : ℝ)≤P^(boxExponent h j phi)
  v_scale : sourceV P h j≤P^(boxExponent h j phi)
  cubic : 16*(sourceH P h : ℝ)^3*P^(b-δ)≤sourceJ P j
  binomial : 2*(P^(b-δ))^3*Real.sqrt ((sourceV P h j)*
    ((d : ℝ)*(sourceN P phi R : ℝ)^(d-1)))/(sourceV P h j)<1
  power : 2*(P^(b-δ))^d<Real.sqrt ((sourceV P h j)*(P^phi)^d)
  conductor : P^(3*h+j+(d : ℝ)*phi)≤8*((sourceV P h j)*(P^phi)^d)
  phase_constant : 8*(c : ℝ)≤P^δ

theorem floor_ranges {d c : ℕ} (hd : 6≤d)
    {P R h j phi b δ η : ℝ} (hP : 2≤P) (hh : 0<h) (hj : 0≤j)
    (hphi : 0<phi) (hb : 0<b) (hδ : 0<δ) (hδb : δ≤b/2)
    (hη : 0<η) (hη1 : η≤1) (hηδ : ((d : ℝ)+1)*η≤δ)
    (hR : 1≤R) (hRup : R≤P^η) (hHpow : 2≤P^h)
    (hconstant : sourceConstant d c≤P^δ)
    (hcapPhi : b≤phi) (hcapCubic : 3*h+b≤j)
    (hcapPower : 2*(d : ℝ)*b≤3*h+j+(d : ℝ)*phi)
    (hcapBinomial : 6*b+((d-1 : ℕ) : ℝ)*phi≤3*h+j) :
    FloorRanges d c P R h j phi b δ := by
  have hP1 : 1≤P := by linarith
  have hPp : 0<P := by linarith
  have hdpos : 0<d := by omega
  have hdR : (1 : ℝ)≤d := by exact_mod_cast hdpos
  have hy : 0<b-δ := by linarith
  have hM : 1≤P^phi := Real.one_le_rpow hP1 hphi.le
  have hMp : 0<P^phi := Real.rpow_pos_of_pos hPp _
  have hRpos : 0<R := zero_lt_one.trans_le hR
  have hJpow : 1≤P^j := Real.one_le_rpow hP1 hj
  have hNbase : 1≤P^phi*R := one_le_mul_of_one_le_of_one_le hM hR
  have hHpos : 0<sourceH P h := Nat.floor_pos.mpr (by linarith)
  have hJpos : 0<sourceJ P j := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hPp _)
  have hNpos : 0<sourceN P phi R := Nat.ceil_pos.mpr (mul_pos hMp hRpos)
  have hHupper : (sourceH P h : ℝ)≤P^h := Nat.floor_le (Real.rpow_nonneg hPp.le _)
  have hHlower : P^h≤2*(sourceH P h : ℝ) := by
    have hh' := half_le_floor hHpow
    change P^h≤2*(⌊P^h⌋₊ : ℝ)
    linarith
  have hJlower : P^j≤(sourceJ P j : ℝ) := Nat.le_ceil _
  have hJupper : (sourceJ P j : ℝ)≤2*P^j := ceil_le_twice hJpow
  have hNlower : P^phi≤(sourceN P phi R : ℝ) :=
    (le_mul_of_one_le_right hMp.le hR).trans (Nat.le_ceil _)
  have hNupper : (sourceN P phi R : ℝ)≤2*P^phi*R := by
    simpa only [mul_assoc] using ceil_le_twice hNbase
  have hNpower : (sourceN P phi R : ℝ)≤2*P^(phi+η) := by
    calc
      _ ≤ 2*P^phi*R := hNupper
      _ ≤ 2*P^phi*P^η := mul_le_mul_of_nonneg_left hRup (by positivity)
      _ = _ := by rw [Real.rpow_add hPp]; ring
  let v := 3*h+j
  let q := v+(d : ℝ)*phi
  have hv : 0≤v := by dsimp [v]; linarith
  have hVpos : 0<sourceV P h j := by dsimp [sourceV]; positivity
  have hidV : (P^h)^3*P^j=P^v := by
    rw [← Real.rpow_mul_natCast hPp.le,← Real.rpow_add hPp]
    congr 1
    dsimp [v]
    norm_num
    ring
  have hVlower : P^v≤8*sourceV P h j := by
    calc
      _ = (P^h)^3*P^j := hidV.symm
      _ ≤ (2*(sourceH P h : ℝ))^3*(sourceJ P j : ℝ) := by gcongr
      _ = _ := by dsimp [sourceV]; ring
  have hVupper : sourceV P h j≤2*P^v := by
    calc
      _ ≤ (P^h)^3*(2*P^j) := by dsimp [sourceV]; gcongr
      _ = 2*P^v := by rw [← hidV]; ring
  have hconductor : P^q≤8*((sourceV P h j)*(P^phi)^d) := by
    calc
      _ = P^v*(P^phi)^d := by
        rw [← Real.rpow_mul_natCast hPp.le,← Real.rpow_add hPp]
        congr 1
        dsimp [q]
        ring
      _ ≤ (8*sourceV P h j)*(P^phi)^d := mul_le_mul_of_nonneg_right hVlower (by positivity)
      _ = _ := by ring
  have h16 : (16 : ℝ)≤P^δ := by
    apply le_trans _ hconstant
    dsimp [sourceConstant]
    have hm : 0≤64*((d : ℝ)+1)*(2 : ℝ)^d := by positivity
    have hc0 : (0 : ℝ)≤c := by positivity
    linarith
  have hc : 8*(c : ℝ)≤P^δ := by
    apply le_trans _ hconstant
    dsimp [sourceConstant]
    have hm : 0≤64*((d : ℝ)+1)*(2 : ℝ)^d := by positivity
    linarith
  have h32 : (32 : ℝ)<P^δ := by
    apply lt_of_lt_of_le _ hconstant
    have hp : (1 : ℝ)≤(2 : ℝ)^d := one_le_pow₀ (by norm_num)
    have hh' : 64≤64*((d : ℝ)+1)*(2 : ℝ)^d := by nlinarith
    dsimp [sourceConstant]
    have hc0 : (0 : ℝ)≤c := by positivity
    linarith
  have hbinConstant : 32*(d : ℝ)*(2 : ℝ)^(d-1)<P^δ := by
    apply lt_of_lt_of_le _ hconstant
    have hpow2 : (2 : ℝ)^(d-1)≤(2 : ℝ)^d := pow_le_pow_right₀ (by norm_num) (by omega)
    have hpow2p : 0<(2 : ℝ)^d := by positivity
    calc
      _ ≤ 32*(d : ℝ)*(2 : ℝ)^d := mul_le_mul_of_nonneg_left hpow2 (by positivity)
      _ < 64*((d : ℝ)+1)*(2 : ℝ)^d := by
        apply mul_lt_mul_of_pos_right _ hpow2p
        linarith
      _ ≤ sourceConstant d c := by
        dsimp [sourceConstant]
        have hc0 : (0 : ℝ)≤c := by positivity
        linarith
  have hηdim : ((d-1 : ℕ) : ℝ)*η≤δ := by
    have hle : ((d-1 : ℕ) : ℝ)≤(d : ℝ)+1 := by exact_mod_cast (show d-1≤d+1 by omega)
    exact (mul_le_mul_of_nonneg_right hle hη.le).trans hηδ
  have hbinExp : 6*(b-δ)+((d-1 : ℕ) : ℝ)*(phi+η)≤v-δ := by
    dsimp [v]
    nlinarith only [hcapBinomial,hηdim,hδ]
  have hbinSq : 4*((P^(b-δ))^3)^2*((d : ℝ)*(sourceN P phi R : ℝ)^(d-1))<sourceV P h j := by
    have hbound : 4*((P^(b-δ))^3)^2*((d : ℝ)*(sourceN P phi R : ℝ)^(d-1))≤
        (4*(d : ℝ)*(2 : ℝ)^(d-1))*P^(v-δ) := by
      calc
        _ = 4*(d : ℝ)*(P^(b-δ))^6*(sourceN P phi R : ℝ)^(d-1) := by ring
        _ ≤ 4*(d : ℝ)*(P^(b-δ))^6*(2*P^(phi+η))^(d-1) := by gcongr
        _ = (4*(d : ℝ)*(2 : ℝ)^(d-1))*P^(6*(b-δ)+((d-1 : ℕ) : ℝ)*(phi+η)) := by
          rw [mul_pow,← Real.rpow_mul_natCast hPp.le,← Real.rpow_mul_natCast hPp.le]
          norm_num only [Nat.cast_ofNat]
          rw [show 4*(d : ℝ)*P^((b-δ)*6)*((2 : ℝ)^(d-1)*P^((phi+η)*((d-1 : ℕ) : ℝ)))=
            (4*(d : ℝ)*(2 : ℝ)^(d-1))*(P^((b-δ)*6)*P^((phi+η)*((d-1 : ℕ) : ℝ))) by ring]
          rw [← Real.rpow_add hPp]
          congr 2
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hP1 hbinExp) (by positivity)
    have hlast : 8*((4*(d : ℝ)*(2 : ℝ)^(d-1))*P^(v-δ))<8*sourceV P h j := by
      calc
        _ = (32*(d : ℝ)*(2 : ℝ)^(d-1))*P^(v-δ) := by ring
        _ < P^δ*P^(v-δ) := mul_lt_mul_of_pos_right hbinConstant (Real.rpow_pos_of_pos hPp _)
        _ = P^v := by rw [← Real.rpow_add hPp]; congr 1; ring
        _ ≤ _ := hVlower
    nlinarith only [hbound,hlast]
  have hbinomial : 2*(P^(b-δ))^3*Real.sqrt ((sourceV P h j)*
      ((d : ℝ)*(sourceN P phi R : ℝ)^(d-1)))/(sourceV P h j)<1 :=
    (separation_iff_square hVpos (by positivity) (by positivity)).mpr hbinSq
  have hpowerExp : (b-δ)*((2*d : ℕ) : ℝ)≤q-δ := by
    have hδmult : δ≤2*(d : ℝ)*δ := by
      have hle : (1 : ℝ)≤2*d := by linarith
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hle hδ.le
    dsimp [q,v]
    push_cast
    nlinarith only [hcapPower,hδmult]
  have hpowerSq : 4*(P^(b-δ))^(2*d)<(sourceV P h j)*(P^phi)^d := by
    have hh : 8*(4*(P^(b-δ))^(2*d))<8*((sourceV P h j)*(P^phi)^d) := by
      calc
        _ = 32*P^((b-δ)*((2*d : ℕ) : ℝ)) := by rw [← Real.rpow_mul_natCast hPp.le]; ring
        _ ≤ 32*P^(q-δ) := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hP1 hpowerExp) (by norm_num)
        _ < P^δ*P^(q-δ) := mul_lt_mul_of_pos_right h32 (Real.rpow_pos_of_pos hPp _)
        _ = P^q := by rw [← Real.rpow_add hPp]; congr 1; ring
        _ ≤ _ := hconductor
    nlinarith only [hh]
  have hpower : 2*(P^(b-δ))^d<Real.sqrt ((sourceV P h j)*(P^phi)^d) := by
    apply (sq_lt_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt (by positivity : 0≤(sourceV P h j)*(P^phi)^d),mul_pow,← pow_mul]
    norm_num only [Nat.reducePow]
    simpa only [Nat.mul_comm] using hpowerSq
  have hcubic : 16*(sourceH P h : ℝ)^3*P^(b-δ)≤sourceJ P j := by
    calc
      _ ≤ 16*(P^h)^3*P^(b-δ) := by gcongr
      _ = 16*P^(3*h+b-δ) := by
        rw [← Real.rpow_mul_natCast hPp.le,mul_assoc,← Real.rpow_add hPp]
        congr 2
        norm_num
        ring
      _ ≤ P^δ*P^(3*h+b-δ) := mul_le_mul_of_nonneg_right h16 (Real.rpow_nonneg hPp.le _)
      _ = P^(3*h+b) := by rw [← Real.rpow_add hPp]; congr 1; ring
      _ ≤ P^j := Real.rpow_le_rpow_of_exponent_le hP1 hcapCubic
      _ ≤ _ := hJlower
  have hNscale : (sourceN P phi R : ℝ)≤P^(boxExponent h j phi) := by
    calc
      _ ≤ 2*P^(phi+η) := hNpower
      _ ≤ P*P^(phi+η) := mul_le_mul_of_nonneg_right hP (Real.rpow_nonneg hPp.le _)
      _ = P^(phi+η+1) := by
        nth_rw 1 [← Real.rpow_one P]
        rw [← Real.rpow_add hPp]
        congr 1
        ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hP1 (by dsimp [boxExponent]; linarith)
  have hHscale : (sourceH P h : ℝ)≤P^(boxExponent h j phi) := hHupper.trans
    (Real.rpow_le_rpow_of_exponent_le hP1 (by dsimp [boxExponent]; linarith))
  have hVscale : sourceV P h j≤P^(boxExponent h j phi) := by
    calc
      _ ≤ 2*P^v := hVupper
      _ ≤ P*P^v := mul_le_mul_of_nonneg_right hP (Real.rpow_nonneg hPp.le _)
      _ = P^(v+1) := by
        nth_rw 1 [← Real.rpow_one P]
        rw [← Real.rpow_add hPp]
        congr 1
        ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hP1 (by dsimp [boxExponent,v]; linarith)
  exact ⟨hHpos,hJpos,hNpos,hNlower,hNupper,hNscale,hHscale,hVscale,hcubic,hbinomial,hpower,hconductor,hc⟩

#print axioms floor_ranges
end Waring.PolicyCompletionBasicRanges
