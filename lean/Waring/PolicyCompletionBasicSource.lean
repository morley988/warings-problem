import Waring.PolicyCompletionBasicRanges

/-!
# The genuine basic coefficient resource with literal floor cutoffs

All analytic steps and all rounding/size conditions are proved. The four
source caps and the original-conductor height condition imply the stated
uniform saving for the actual normalized coefficient second moment.
-/

noncomputable section
open scoped BigOperators Classical
namespace Waring.PolicyCompletionBasicSource
open RationalHeight NormalizedCoefficient PolicyCompletionBasicMoment
open PolicyCompletionBasicLoss PolicyCompletionBasicRanges

theorem normalized_basic_floor_cutoffs {d c : ℕ} (hd : 6≤d) (hc : 0<c)
    {h j phi b ε : ℝ} (hh : 0<h) (hj : 0≤j) (hphi : 0<phi) (hb : 0<b) (hε : 0<ε)
    (hcapPhi : b≤phi) (hcapCubic : 3*h+b≤j)
    (hcapPower : 2*(d : ℝ)*b≤3*h+j+(d : ℝ)*phi)
    (hcapBinomial : 6*b+((d-1 : ℕ) : ℝ)*phi≤3*h+j) :
    ∃η C P₀ : ℝ,0<η ∧ 0<C ∧ 2≤P₀ ∧
      ∀P : ℝ,P₀≤P→∀R : ℝ,1≤R→R≤P^η→∀A : Finset ℕ,
      (∀m∈A,P^phi<(m : ℝ) ∧ (m : ℝ)≤P^phi*R)→∀(α : ℝ) (σ : ℕ→ℝ),
      P^((d : ℝ)*b/2)≤height (P^(3*h+j+(d : ℝ)*phi)) α→
      normalizedSampledCoefficient A d 1 P phi (sourceH P h) (sourceJ P j) ((c : ℝ)*α) σ≤
        C*P^(ε-b) := by
  let δ := min (b/2) (ε/8)
  have hδ : 0<δ := lt_min (half_pos hb) (by positivity)
  have hδb : δ≤b/2 := min_le_left _ _
  have hδε : δ≤ε/8 := min_le_right _ _
  have hdR : (0 : ℝ)<d := by exact_mod_cast (show 0<d by omega)
  have hdR1 : (1 : ℝ)≤d := by exact_mod_cast (show 1≤d by omega)
  let η := min 1 (δ/((d : ℝ)+1))
  have hη : 0<η := lt_min zero_lt_one (by positivity)
  have hη1 : η≤1 := min_le_left _ _
  have hηδ : ((d : ℝ)+1)*η≤δ := by
    have hh' := (le_div_iff₀ (show 0<(d : ℝ)+1 by positivity)).mp (min_le_right 1 (δ/((d : ℝ)+1)))
    simpa only [mul_comm] using hh'
  have hηle : η≤δ := (min_le_right _ _).trans (div_le_self hδ.le (by linarith))
  have hB : 0≤boxExponent h j phi := by dsimp [boxExponent]; linarith
  obtain ⟨Cm,hCm,hbound⟩ := basic_moment_uniform_loss hd hB (half_pos hε)
  let P₀ := max 2 (max ((2 : ℝ)^(1/h)) ((sourceConstant d c)^(1/δ)))
  have hConstant : 0<sourceConstant d c := by dsimp [sourceConstant]; positivity
  refine ⟨η,8*Cm,P₀,hη,by positivity,le_max_left _ _,?_⟩
  intro P hP₀ R hR hRup A hA α σ hheight
  have hP2 : 2≤P := (le_max_left _ _).trans hP₀
  have hP1 : 1≤P := by linarith
  have hPp : 0<P := by linarith
  have hHpow : 2≤P^h := fixed_constant_rpow_bound (by norm_num) hh
    ((le_max_left _ _).trans ((le_max_right _ _).trans hP₀))
  have hconst : sourceConstant d c≤P^δ := fixed_constant_rpow_bound hConstant hδ
    ((le_max_right _ _).trans ((le_max_right _ _).trans hP₀))
  have hs := floor_ranges hd hP2 hh hj hphi hb hδ hδb hη hη1 hηδ hR hRup hHpow hconst
    hcapPhi hcapCubic hcapPower hcapBinomial
  have hHpos := hs.h_pos
  have hJpos := hs.j_pos
  have hNpos := hs.n_pos
  have hM : 1≤P^phi := Real.one_le_rpow hP1 hphi.le
  have hMp : 0<P^phi := Real.rpow_pos_of_pos hPp _
  have hy : 0<b-δ := by linarith
  have hY : 1≤P^(b-δ) := Real.one_le_rpow hP1 hy.le
  have hYM : P^(b-δ)≤P^phi := Real.rpow_le_rpow_of_exponent_le hP1 (by linarith)
  have hAN : A⊆Finset.Icc 1 (sourceN P phi R) := by
    intro m hm
    have hb' := hA m hm
    apply Finset.mem_Icc.mpr
    constructor
    · have hh' : (1 : ℝ)≤m := hM.trans hb'.1.le
      exact_mod_cast hh'
    · have hh' : (m : ℝ)≤sourceN P phi R := hb'.2.trans (Nat.le_ceil _)
      exact_mod_cast hh'
  have hW : 0<(sourceV P h j)*(P^phi)^d := by dsimp [sourceV]; positivity
  have hphase := common_height_phase_shift hPp hW (by norm_num : (1 : ℝ)≤8)
    hs.conductor c hc hs.phase_constant hheight
  have ha : (0 : ℝ)<2/(d : ℝ) := by positivity
  have ha1 : 2/(d : ℝ)≤1 := (div_le_one hdR).mpr (by exact_mod_cast (show 2≤d by omega))
  have hpowerLower : P^(b-δ)≤
      (height ((sourceV P h j)*(P^phi)^d) ((c : ℝ)*α))^(2/(d : ℝ)) := by
    have hp := Real.rpow_le_rpow (Real.rpow_nonneg hPp.le _) hphase ha.le
    rw [← Real.rpow_mul hPp.le] at hp
    apply (Real.rpow_le_rpow_of_exponent_le hP1 ?_).trans hp
    have hid : ((d : ℝ)*b/2-δ)*(2/(d : ℝ))=b-δ*(2/(d : ℝ)) := by
      field_simp <;> ring
    rw [hid]
    have hδa := mul_le_mul_of_nonneg_left ha1 hδ.le
    linarith
  have hinv : 1/P^(b-δ)=P^(δ-b) := by
    rw [show δ-b=-(b-δ) by ring,Real.rpow_neg hPp.le,one_div]
  have hrecip : 1/(height ((sourceV P h j)*(P^phi)^d) ((c : ℝ)*α))^(2/(d : ℝ))≤P^(δ-b) := by
    rw [← hinv]
    exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos hPp _) hpowerLower
  have hE : 1/P^(b-δ)+1/(height ((sourceV P h j)*(P^phi)^d) ((c : ℝ)*α))^(2/(d : ℝ))≤2*P^(δ-b) := by
    rw [hinv]
    linarith
  have hmoment := hbound P hP2 A (sourceN P phi R) (sourceH P h) (sourceJ P j)
    (P^phi) (P^(b-δ)) ((c : ℝ)*α) σ hNpos hHpos hJpos hAN hM hs.n_lower hY hYM
    (fun m hm=>(hA m hm).1) hs.n_scale hs.h_scale hs.v_scale hs.cubic hs.binomial hs.power
  have hN2 : (sourceN P phi R : ℝ)^2≤4*(P^phi)^2*(P^η)^2 := by
    calc
      _ ≤ (2*P^phi*R)^2 := pow_le_pow_left₀ (by positivity) hs.n_upper _
      _ ≤ (2*P^phi*P^η)^2 := by gcongr
      _ = _ := by ring
  have hPowers : P^(ε/2)*(P^η)^2*P^(δ-b)=P^(ε/2+2*η+δ-b) := by
    rw [← Real.rpow_mul_natCast hPp.le,← Real.rpow_add hPp,← Real.rpow_add hPp]
    congr 1
    norm_num
    ring
  have hslack : ε/2+2*η+δ-b≤ε-b := by linarith
  have hM2 : (P^phi)^2=P^(2*phi) := by
    rw [← Real.rpow_mul_natCast hPp.le]
    congr 1
    norm_num
    ring
  change basicMoment A d (sourceH P h) (sourceJ P j) ((c : ℝ)*α) σ /
    ((sourceH P h : ℝ)*sourceJ P j*P^(2*phi))≤(8*Cm)*P^(ε-b)
  apply (div_le_iff₀ (by positivity : 0<(sourceH P h : ℝ)*sourceJ P j*P^(2*phi))).mpr
  calc
    _ ≤ Cm*P^(ε/2)*(sourceJ P j : ℝ)*sourceH P h*(sourceN P phi R : ℝ)^2*
        (1/P^(b-δ)+1/(height ((sourceV P h j)*(P^phi)^d) ((c : ℝ)*α))^(2/(d : ℝ))) := hmoment
    _ ≤ Cm*P^(ε/2)*(sourceJ P j : ℝ)*sourceH P h*(4*(P^phi)^2*(P^η)^2)*(2*P^(δ-b)) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hN2 (by positivity)) hE
        (add_nonneg (one_div_pos.mpr (Real.rpow_pos_of_pos hPp _)).le
          (one_div_pos.mpr (Real.rpow_pos_of_pos (height_pos _ _) _)).le) (by positivity)
    _ = (8*Cm*(sourceH P h : ℝ)*sourceJ P j*P^(2*phi))*P^(ε/2+2*η+δ-b) := by
      rw [← hPowers,← hM2]
      ring
    _ ≤ (8*Cm*(sourceH P h : ℝ)*sourceJ P j*P^(2*phi))*P^(ε-b) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hP1 hslack) (by positivity)
    _ = _ := by ring

#print axioms normalized_basic_floor_cutoffs
end Waring.PolicyCompletionBasicSource
