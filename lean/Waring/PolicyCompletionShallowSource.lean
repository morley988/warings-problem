import Waring.PolicyCompletionShallowEstimate
import Waring.PolicyCompletionBasicRanges

/-!
# The shallow coefficient resource on the actual floor ranges

The source estimate is specialized to the literal integer cutoffs. Its
only numerical cap, besides b ≤ phi, is the source error-term inequality.
All ceilings, the fixed phase multiplier, and the smoothness loss are
absorbed uniformly in the arbitrarily small power of P.
-/

noncomputable section
open scoped BigOperators Classical
namespace Waring.PolicyCompletionShallowSource
open RationalHeight NormalizedCoefficient CartesianFloorScales
open PolicyCompletionBasicMoment PolicyCompletionBasicRanges
open PolicyCompletionShallowEstimate

set_option maxHeartbeats 1000000 in
theorem normalized_shallow_floor_cutoffs {k c : ℕ} (hk : 3≤k) (hc : 0<c)
    {h j phi b ε : ℝ} (hh : 0<h) (hj : 0≤j) (hphi : 0<phi) (hb : 0<b) (hε : 0<ε)
    (hcapPhi : b≤phi)
    (hcapError : 2*h+((2*k-2 : ℕ) : ℝ)*phi+b≤j) :
    ∃η C P₀ : ℝ,0<η ∧ 0<C ∧ 2≤P₀ ∧
      ∀P : ℝ,P₀≤P→∀R : ℝ,1≤R→R≤P^η→∀A : Finset ℕ,
      (∀m∈A,P^phi<(m : ℝ) ∧ (m : ℝ)≤P^phi*R)→∀(α : ℝ) (σ : ℕ→ℝ),
      P^((k : ℝ)*b)≤height (P^(3*h+j+((2*k : ℕ) : ℝ)*phi)) α→
      normalizedSampledCoefficient A (2*k) 1 P phi (sourceH P h) (sourceJ P j) ((c : ℝ)*α) σ≤
        C*P^(ε-b) := by
  let d : ℕ := 2*k
  have hd : 6≤d := by dsimp [d]; omega
  have hdR : (0 : ℝ)<d := by exact_mod_cast (show 0<d by omega)
  have hkR : (1 : ℝ)≤k := by exact_mod_cast (show 1≤k by omega)
  have hkRp : (0 : ℝ)<k := by linarith
  have hdm : ((d-2 : ℕ) : ℝ)=(d : ℝ)-2 := by rw [Nat.cast_sub (by omega)]; norm_num
  let δ := min (b/2) (ε/8)
  have hδ : 0<δ := lt_min (half_pos hb) (by positivity)
  have hδε : δ≤ε/8 := min_le_right _ _
  let η := min 1 (δ/((d : ℝ)+1))
  have hη : 0<η := lt_min zero_lt_one (by positivity)
  have hη1 : η≤1 := min_le_left _ _
  have hηδ : ((d : ℝ)+1)*η≤δ := by
    have hh' := (le_div_iff₀ (show 0<(d : ℝ)+1 by positivity)).mp
      (min_le_right 1 (δ/((d : ℝ)+1)))
    simpa only [mul_comm] using hh'
  have hηle : η≤δ := (min_le_right _ _).trans (div_le_self hδ.le (by linarith))
  have hdη : (d : ℝ)*η≤δ := by nlinarith only [hηδ,hη]
  let B := 3*h+(d : ℝ)*(phi+2)+h+phi+2
  have hB : 0≤B := by dsimp [B]; positivity
  obtain ⟨Cm,hCm,hbound⟩ := shallow_moment_uniform hk hB (half_pos hε)
  let P₀ := max 2 (max ((2 : ℝ)^(1/h)) ((8*(c : ℝ))^(1/δ)))
  refine ⟨η,(6+(2 : ℝ)^d)*Cm,P₀,hη,by positivity,le_max_left _ _,?_⟩
  intro P hP₀ R hR hRup A hA α σ hheight
  have hP2 : 2≤P := (le_max_left _ _).trans hP₀
  have hP1 : 1≤P := by linarith
  have hPp : 0<P := by linarith
  have hHpow : 2≤P^h := fixed_constant_rpow_bound (by norm_num) hh
    ((le_max_left _ _).trans ((le_max_right _ _).trans hP₀))
  have hcR : (0 : ℝ)<c := by exact_mod_cast hc
  have hconstant : 8*(c : ℝ)≤P^δ := fixed_constant_rpow_bound (by positivity) hδ
    ((le_max_right _ _).trans ((le_max_right _ _).trans hP₀))
  have hM : 1≤P^phi := Real.one_le_rpow hP1 hphi.le
  have hMp : 0<P^phi := Real.rpow_pos_of_pos hPp _
  have hJpow : 1≤P^j := Real.one_le_rpow hP1 hj
  have hHpos : 0<sourceH P h := Nat.floor_pos.mpr (by linarith)
  have hJpos : 0<sourceJ P j := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hPp _)
  have hNpos : 0<sourceN P phi R := Nat.ceil_pos.mpr (mul_pos hMp (zero_lt_one.trans_le hR))
  have hHupper : (sourceH P h : ℝ)≤P^h := Nat.floor_le (Real.rpow_nonneg hPp.le _)
  have hHlower : P^h≤2*(sourceH P h : ℝ) := by
    have ht := half_le_floor hHpow
    change P^h≤2*(⌊P^h⌋₊ : ℝ)
    linarith
  have hJlower : P^j≤(sourceJ P j : ℝ) := Nat.le_ceil _
  have hNlower : P^phi≤(sourceN P phi R : ℝ) :=
    (le_mul_of_one_le_right hMp.le hR).trans (Nat.le_ceil _)
  have hNupper : (sourceN P phi R : ℝ)≤2*P^phi*R := by
    simpa only [mul_assoc] using ceil_le_twice (one_le_mul_of_one_le_of_one_le hM hR)
  have hNpower : (sourceN P phi R : ℝ)≤2*P^(phi+η) := by
    calc
      _ ≤ 2*P^phi*R := hNupper
      _ ≤ 2*P^phi*P^η := mul_le_mul_of_nonneg_left hRup (by positivity)
      _ = _ := by rw [Real.rpow_add hPp]; ring
  have hNscale0 : (sourceN P phi R : ℝ)≤P^(phi+2) := by
    calc
      _ ≤ 2*P^(phi+η) := hNpower
      _ ≤ P*P^(phi+η) := mul_le_mul_of_nonneg_right hP2 (Real.rpow_nonneg hPp.le _)
      _ = P^(phi+η+1) := by
        nth_rw 1 [← Real.rpow_one P]
        rw [← Real.rpow_add hPp]
        congr 1
        ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hP1 (by linarith)
  have hNscale : (sourceN P phi R : ℝ)≤P^B := hNscale0.trans
    (Real.rpow_le_rpow_of_exponent_le hP1 (by
      have ht : 0≤(d : ℝ)*(phi+2) := by positivity
      dsimp [B]
      linarith))
  have hHscale : (sourceH P h : ℝ)≤P^B := hHupper.trans
    (Real.rpow_le_rpow_of_exponent_le hP1 (by
      have ht : 0≤(d : ℝ)*(phi+2) := by positivity
      dsimp [B]
      linarith))
  have hTscale : (((sourceH P h)^3*(sourceN P phi R)^(2*k) : ℕ) : ℝ)≤P^B := by
    push_cast
    calc
      _ ≤ (P^h)^3*(P^(phi+2))^d := by dsimp [d]; gcongr
      _ = P^(3*h+(d : ℝ)*(phi+2)) := by
        rw [← Real.rpow_mul_natCast hPp.le,← Real.rpow_mul_natCast hPp.le,← Real.rpow_add hPp]
        congr 1
        norm_num
        ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hP1 (by dsimp [B]; linarith)
  have hAN : A⊆Finset.Icc 1 (sourceN P phi R) := by
    intro m hm
    have hb' := hA m hm
    apply Finset.mem_Icc.mpr
    constructor
    · exact_mod_cast hM.trans hb'.1.le
    · exact_mod_cast hb'.2.trans (Nat.le_ceil (P^phi*R))
  have hconductor : P^(3*h+j+(d : ℝ)*phi)≤8*(sourceV P h j*(P^phi)^d) := by
    calc
      _ = (P^h)^3*P^j*(P^phi)^d := by
        rw [← Real.rpow_mul_natCast hPp.le,← Real.rpow_mul_natCast hPp.le,
          ← Real.rpow_add hPp,← Real.rpow_add hPp]
        congr 1
        norm_num
        ring
      _ ≤ (2*(sourceH P h : ℝ))^3*(sourceJ P j : ℝ)*(P^phi)^d := by gcongr
      _ = _ := by dsimp [sourceV]; ring
  have hW : 0<sourceV P h j*(P^phi)^d := by dsimp [sourceV]; positivity
  have hphase := common_height_phase_shift hPp hW (by norm_num : (1 : ℝ)≤8)
    hconductor c hc hconstant hheight
  have ha : (0 : ℝ)<1/(k : ℝ) := by positivity
  have ha1 : 1/(k : ℝ)≤1 := (div_le_one hkRp).mpr hkR
  have hpowerLower : P^(b-δ)≤
      (height (sourceV P h j*(P^phi)^d) ((c : ℝ)*α))^(1/(k : ℝ)) := by
    have hp := Real.rpow_le_rpow (Real.rpow_nonneg hPp.le _) hphase ha.le
    rw [← Real.rpow_mul hPp.le] at hp
    apply (Real.rpow_le_rpow_of_exponent_le hP1 ?_).trans hp
    have hid : ((k : ℝ)*b-δ)*(1/(k : ℝ))=b-δ*(1/(k : ℝ)) := by field_simp <;> ring
    rw [hid]
    have ht := mul_le_mul_of_nonneg_left ha1 hδ.le
    linarith
  have hrecip : 1/(height (sourceV P h j*(P^phi)^d) ((c : ℝ)*α))^(1/(k : ℝ))≤P^(δ-b) := by
    have hi : 1/P^(b-δ)=P^(δ-b) := by
      rw [show δ-b=-(b-δ) by ring,Real.rpow_neg hPp.le,one_div]
    rw [← hi]
    exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos hPp _) hpowerLower
  have hmoment := hbound P hP2 A (sourceH P h) (sourceN P phi R) (sourceJ P j)
    hHpos hNpos hAN (P^phi) hMp.le hNlower (fun m hm=>(hA m hm).1)
    hNscale hHscale hTscale ((c : ℝ)*α) σ
  let K := (sourceH P h : ℝ)*sourceJ P j*(P^phi)^2
  have hK : 0<K := by dsimp [K]; positivity
  have hfirst : (sourceJ P j : ℝ)*sourceH P h*(sourceN P phi R : ℝ)^2 /
      (height ((sourceH P h : ℝ)^3*sourceJ P j*(P^phi)^(2*k)) ((c : ℝ)*α))^(1/(k : ℝ))≤
      4*K*P^(ε/2-b) := by
    calc
      _ = ((sourceJ P j : ℝ)*sourceH P h*(sourceN P phi R : ℝ)^2)*
        (1/(height (sourceV P h j*(P^phi)^d) ((c : ℝ)*α))^(1/(k : ℝ))) := by
        dsimp [sourceV,d]
        ring
      _ ≤ ((sourceJ P j : ℝ)*sourceH P h*(2*P^(phi+η))^2)*P^(δ-b) := by
        exact mul_le_mul (by gcongr) hrecip
          (one_div_nonneg.mpr (Real.rpow_nonneg (height_pos _ _).le _)) (by positivity)
      _ = 4*K*P^(2*η+δ-b) := by
        have hp : (P^η)^2*P^(δ-b)=P^(2*η+δ-b) := by
          rw [← Real.rpow_mul_natCast hPp.le,← Real.rpow_add hPp]
          congr 1
          norm_num
          ring
        dsimp [K]
        rw [Real.rpow_add hPp,mul_pow,mul_pow,← hp]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hP1 (by linarith)) (by positivity)
  have hsecond : (sourceJ P j : ℝ)*sourceH P h*sourceN P phi R≤2*K*P^(ε/2-b) := by
    have hexp : phi+η≤2*phi+(ε/2-b) := by linarith
    calc
      _ ≤ (sourceJ P j : ℝ)*sourceH P h*(2*P^(phi+η)) := by gcongr
      _ ≤ (sourceJ P j : ℝ)*sourceH P h*(2*P^(2*phi+(ε/2-b))) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hP1 hexp) (by norm_num))
          (by positivity)
      _ = _ := by
        dsimp [K]
        rw [Real.rpow_add hPp,show 2*phi=phi*(2 : ℕ) by norm_num;ring,
          Real.rpow_mul_natCast hPp.le]
        ring
  have hcapError' : 2*h+((d : ℝ)-2)*phi+b≤j := by
    simpa only [d,← hdm] using hcapError
  have hthird : (sourceH P h : ℝ)^3*(sourceN P phi R : ℝ)^(2*k)≤
      (2 : ℝ)^d*K*P^(ε/2-b) := by
    have hexp : 2*h+(phi+η)*(d : ℝ)≤j+2*phi+(ε/2-b) := by
      nlinarith only [hcapError',hdη,hδε,hε]
    calc
      _ = (sourceH P h : ℝ)*(sourceH P h : ℝ)^2*(sourceN P phi R : ℝ)^d := by
        dsimp [d]
        ring
      _ ≤ (sourceH P h : ℝ)*(P^h)^2*(2*P^(phi+η))^d := by gcongr
      _ = (2 : ℝ)^d*(sourceH P h : ℝ)*P^(2*h+(phi+η)*(d : ℝ)) := by
        rw [mul_pow,← Real.rpow_mul_natCast hPp.le,← Real.rpow_mul_natCast hPp.le]
        norm_num only [Nat.cast_ofNat]
        rw [Real.rpow_add hPp]
        ring
      _ ≤ (2 : ℝ)^d*(sourceH P h : ℝ)*P^(j+2*phi+(ε/2-b)) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hP1 hexp) (by positivity)
      _ = (2 : ℝ)^d*(sourceH P h : ℝ)*P^j*(P^phi)^2*P^(ε/2-b) := by
        rw [Real.rpow_add hPp,Real.rpow_add hPp,
          show 2*phi=phi*(2 : ℕ) by norm_num;ring,Real.rpow_mul_natCast hPp.le]
        ring
      _ ≤ (2 : ℝ)^d*(sourceH P h : ℝ)*sourceJ P j*(P^phi)^2*P^(ε/2-b) := by gcongr
      _ = _ := by dsimp [K]; ring
  have hM2 : (P^phi)^2=P^(2*phi) := by
    rw [← Real.rpow_mul_natCast hPp.le]
    congr 1
    norm_num
    ring
  change basicMoment A (2*k) (sourceH P h) (sourceJ P j) ((c : ℝ)*α) σ /
    ((sourceH P h : ℝ)*sourceJ P j*P^(2*phi))≤((6+(2 : ℝ)^d)*Cm)*P^(ε-b)
  apply (div_le_iff₀ (by positivity : 0<(sourceH P h : ℝ)*sourceJ P j*P^(2*phi))).mpr
  calc
    _ ≤ Cm*P^(ε/2)*
        ((sourceJ P j : ℝ)*sourceH P h*(sourceN P phi R : ℝ)^2 /
          (height ((sourceH P h : ℝ)^3*sourceJ P j*(P^phi)^(2*k)) ((c : ℝ)*α))^(1/(k : ℝ))+
          (sourceJ P j : ℝ)*sourceH P h*sourceN P phi R+
          (sourceH P h : ℝ)^3*(sourceN P phi R : ℝ)^(2*k)) := hmoment
    _ ≤ Cm*P^(ε/2)*(4*K*P^(ε/2-b)+2*K*P^(ε/2-b)+(2 : ℝ)^d*K*P^(ε/2-b)) :=
      mul_le_mul_of_nonneg_left (add_le_add (add_le_add hfirst hsecond) hthird) (by positivity)
    _ = ((6+(2 : ℝ)^d)*Cm)*P^(ε-b)*((sourceH P h : ℝ)*sourceJ P j*P^(2*phi)) := by
      rw [show ε-b=ε/2+(ε/2-b) by ring,Real.rpow_add hPp]
      dsimp [K]
      rw [hM2]
      ring

#print axioms normalized_shallow_floor_cutoffs
end Waring.PolicyCompletionShallowSource
