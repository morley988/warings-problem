import Waring.PolicyCompletionQuadraticBox

/-!
# Both actual quadratic fourth resources on floor boxes

The completion interval is exactly [-2 floor(P),2 floor(P)]. Its fixed
length enlargement and the ceiling in the product cutoff cost only fixed
constants. Both original concave saving formulas are retained unchanged.
-/

noncomputable section
open scoped BigOperators
namespace Waring.PolicyCompletionFourthBox
open RationalHeight NormalizedQuadratic CartesianProductSampling
open CartesianResourceMoments CartesianFloorScales ProductMultiplicity
open CartesianPolynomialBounds

theorem fourth_shape_refined_twice {P H L ell h : ℝ}
    (hP : 1≤P) (hH : 0≤H) (hL : 0<L) (hHs : H≤2*P^h) (hLs : P^ell≤L) :
    H*P^2+P^4*min (H/L) (H^2/L^2)≤4*H*P^4*P^(-z4RefinedSaving ell h) := by
  have hPp : 0<P := zero_lt_one.trans_le hP
  have hcap : z4RefinedSaving ell h≤2*ell-h := min_le_right _ _
  have hcap2 : z4RefinedSaving ell h≤2 := min_le_left _ _
  have hden : P^(2*ell)≤L^2 := by
    calc
      _ = (P^ell)^2 := by rw [← Real.rpow_mul_natCast hPp.le]; congr 1; norm_num; ring
      _ ≤ _ := pow_le_pow_left₀ (Real.rpow_nonneg hPp.le _) hLs 2
  have hratio : H/L^2≤2*P^(-(2*ell-h)) := by
    calc
      _ ≤ (2*P^h)/P^(2*ell) := div_le_div₀ (by positivity) hHs (Real.rpow_pos_of_pos hPp _) hden
      _ = _ := by rw [mul_div_assoc,← Real.rpow_sub hPp]; congr 2; ring
  have hmin : min (H/L) (H^2/L^2)≤2*H*P^(-z4RefinedSaving ell h) := by
    calc
      _ ≤ H^2/L^2 := min_le_right _ _
      _ = H*(H/L^2) := by ring
      _ ≤ H*(2*P^(-(2*ell-h))) := mul_le_mul_of_nonneg_left hratio hH
      _ ≤ H*(2*P^(-z4RefinedSaving ell h)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hP (neg_le_neg hcap))
            (by norm_num)) hH
      _ = _ := by ring
  have hfirst : H*P^2≤H*P^4*P^(-z4RefinedSaving ell h) := by
    have hid : P^2=P^4*P^(-2 : ℝ) := by
      rw [Real.rpow_neg hPp.le]
      norm_num only [Real.rpow_ofNat]
      field_simp
    calc
      _ = (H*P^4)*P^(-2 : ℝ) := by rw [hid]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hP (neg_le_neg hcap2)) (by positivity)
  have hsecond := mul_le_mul_of_nonneg_left hmin (show 0≤P^4 by positivity)
  have hnon : 0≤H*P^4*P^(-z4RefinedSaving ell h) := by positivity
  nlinarith only [hfirst,hsecond,hnon]

theorem normalize_fourth_shape {s : Finset ℕ} {a b : ℕ→ℤ} {t : ℕ→ℝ}
    {c : ℕ} {P H α C ε cap X K : ℝ} (hP : 0<P) (hH : 0<H) (hC : 0≤C)
    (hmoment : (∑q∈s,‖∑z∈Finset.Icc (a q) (b q),
      QuadraticModulation.e ((c : ℝ)*((q : ℝ)*α)*(z : ℝ)^2+t q*z)‖^4)≤C*P^ε*X)
    (hshape : X≤K*H*P^4*P^(-cap)) :
    normalizedFourth s a b t c P H α≤(K*C)*P^(ε-cap) := by
  unfold normalizedFourth
  apply (div_le_iff₀ (by positivity : 0<H*P^4)).mpr
  calc
    _ ≤ C*P^ε*X := hmoment
    _ ≤ C*P^ε*(K*H*P^4*P^(-cap)) := mul_le_mul_of_nonneg_left hshape (by positivity)
    _ = (K*C)*(P^ε*P^(-cap))*(H*P^4) := by ring
    _ = _ := by rw [← Real.rpow_add hP,sub_eq_add_neg]

theorem normalized_fourth_fixed_support (B : ℝ) (hB : 0≤B) (c : ℕ) (hc : 0<c)
    {ε : ℝ} (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀P : ℝ,2≤P→∀H : ℝ,1≤H→H≤P^B→
      ∀α ell h : ℝ,H≤2*P^h→P^ell≤height (H*P^2) α→
      ∀s : Finset ℕ,∀a b : ℕ→ℤ,∀t : ℕ→ℝ,
      (∀q∈s,0<q ∧ (q : ℝ)≤H)→(∀q∈s,a q≤b q)→
      (∀q∈s,(((b q+1-a q).toNat : ℕ) : ℝ)≤5*P)→
      normalizedFourth s a b t c P H α≤C*P^(ε-z4Saving ell h) ∧
      normalizedFourth s a b t c P H α≤C*P^(ε-z4RefinedSaving ell h) := by
  obtain ⟨Cs,hCs,hbound⟩ := SampledQuadraticAsymptotic.sampled_fourth_moment_epsilon B hB c hc hε
  let C := 625*Cs*(5 : ℝ)^ε
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨4*C,by positivity,?_⟩
  intro P hP H hH hHB α ell h hHs hLs s a b t hs hab hlength
  have hP1 : 1≤P := by linarith
  have hPp : 0<P := by linarith
  have hHp : 0<H := zero_lt_one.trans_le hH
  have hX : 2≤5*P := by linarith
  have hHX : H≤(5*P)^B := hHB.trans (Real.rpow_le_rpow hPp.le (by linarith) hB)
  have hraw := hbound (5*P) hX H hH hHX α s a b t hs hab hlength
  let L := height (H*(5*P)^2) α
  have hLp : 0<L := height_pos _ _
  have hLL : P^ell≤L := hLs.trans (height_mono_conductor (by positivity) (by gcongr; linarith))
  have hraw' : (∑q∈s,‖∑z∈Finset.Icc (a q) (b q),
      QuadraticModulation.e ((c : ℝ)*((q : ℝ)*α)*(z : ℝ)^2+t q*z)‖^4)≤
      C*P^ε*(H*P^2+P^4*min (H/L) (H^2/L^2)) := by
    apply hraw.trans
    have hscale : H*(5*P)^2+(5*P)^4*min (H/L) (H^2/L^2)≤
        625*(H*P^2+P^4*min (H/L) (H^2/L^2)) := by
      have hn : 0≤H*P^2 := by positivity
      nlinarith only [hn]
    calc
      _ ≤ Cs*(5*P)^ε*(625*(H*P^2+P^4*min (H/L) (H^2/L^2))) :=
        mul_le_mul_of_nonneg_left hscale (by positivity)
      _ = _ := by rw [Real.mul_rpow (by norm_num : (0 : ℝ)≤5) hPp.le]; dsimp [C]; ring
  constructor
  · have hh := normalize_fourth_shape hPp hHp hC.le hraw'
      (fourth_shape_old (h := h) hP1 hHp.le hLp hLL)
    exact hh.trans (mul_le_mul_of_nonneg_right (by linarith : 2*C≤4*C)
      (Real.rpow_nonneg hPp.le _))
  · exact normalize_fourth_shape hPp hHp hC.le hraw'
      (fourth_shape_refined_twice hP1 hHp.le hLp hHs hLL)

theorem quadratic_floor_box_fourth {r : ℕ} (e : Fin r→ℝ) (he : ∀i,0<e i)
    (c : ℕ) (hc : 0<c) {ε : ℝ} (hε : 0<ε) :
    ∃K P₀ : ℝ,0<K ∧ 2≤P₀ ∧ ∀P : ℝ,P₀≤P→∀α ell t : ℝ,
      P^ell≤height (P^((∑i,e i)+2)) α→
      quadraticBoxMoment (floorBounds P e) (centeredSet ⌊P⌋₊) P α t c 4≤
        K*P^(ε-z4Saving ell (∑i,e i)) ∧
      quadraticBoxMoment (floorBounds P e) (centeredSet ⌊P⌋₊) P α t c 4≤
        K*P^(ε-z4RefinedSaving ell (∑i,e i)) := by
  let E := ∑i,e i
  have hE : 0≤E := Finset.sum_nonneg (fun i _=>(he i).le)
  have hB : 0≤E+1 := by linarith
  obtain ⟨C,hC,hsample⟩ := normalized_fourth_fixed_support (E+1) hB c hc (half_pos hε)
  obtain ⟨D,hD,hbox⟩ := quadratic_fourth_box_to_sample r hB (half_pos hε)
  obtain ⟨P₁,hP₁,hscales⟩ := eventual_cartesian_scales e he
  let P₀ := max 2 P₁
  refine ⟨D*(2 : ℝ)^(r+1)*C,P₀,by positivity,le_max_left _ _,?_⟩
  intro P hPP₀ α ell t hheight
  have hP2 : 2≤P := (le_max_left _ _).trans hPP₀
  have hP1 : 1≤P := by linarith
  have hPp : 0<P := by linarith
  have hPP₁ : P₁≤P := (le_max_right _ _).trans hPP₀
  have hs := hscales P hPP₁
  let J := paddedCutoff P e
  have hJlower : 1≤(J : ℝ) := (Real.one_le_rpow hP1 hE).trans (Nat.le_ceil _)
  have hJupper : (J : ℝ)≤2*P^E := paddedCutoff_le_twice_power e (fun i=>(he i).le) hP1
  have hJscale : (J : ℝ)≤P^(E+1) := by
    calc
      _ ≤ 2*P^E := hJupper
      _ ≤ P*P^E := mul_le_mul_of_nonneg_right hP2 (Real.rpow_nonneg hPp.le _)
      _ = _ := by rw [Real.rpow_add hPp,Real.rpow_one]; ring
  have hconduct : P^(E+2)≤(J : ℝ)*P^2 := by
    have hh := mul_le_mul_of_nonneg_right (Nat.le_ceil (P^E)) (sq_nonneg P)
    simpa only [Real.rpow_add hPp,Real.rpow_two,J,paddedCutoff,E] using hh
  have hheight' : P^ell≤height ((J : ℝ)*P^2) α :=
    hheight.trans (height_mono_conductor (by positivity) hconduct)
  let a : ℤ := -(2*(⌊P⌋₊ : ℤ))
  let b : ℤ := 2*(⌊P⌋₊ : ℤ)
  have hab : a≤b := by dsimp [a,b]; omega
  have hlength : (((b+1-a).toNat : ℕ) : ℝ)≤5*P := by
    have hz : 0≤b+1-a := by omega
    have he : ((b+1-a).toNat : ℤ)=b+1-a := Int.toNat_of_nonneg hz
    have heR : (((b+1-a).toNat : ℕ) : ℝ)=((b+1-a : ℤ) : ℝ) := by exact_mod_cast he
    rw [heR]
    dsimp [a,b]
    push_cast
    have hf := Nat.floor_le hPp.le
    linarith
  have hn := hsample P hP2 J hJlower hJscale α ell E hJupper hheight'
    (Finset.Icc 1 J) (fun _=>a) (fun _=>b) (fun _=>t)
    (by intro q hq; rcases Finset.mem_Icc.mp hq with ⟨h1,h2⟩; exact ⟨h1,by exact_mod_cast h2⟩)
    (fun _ _=>hab) (fun _ _=>hlength)
  have hb := hbox P hP1 (floorBounds P e) hs.1 J hs.2.2.2.1 hJscale
    ((2 : ℝ)^(r+1)) hs.2.2.2.2 a b α t c
  have hfinish (cap : ℝ) (hcap : normalizedFourth (Finset.Icc 1 J)
      (fun _=>a) (fun _=>b) (fun _=>t) c P J α≤C*P^(ε/2-cap)) :
      quadraticBoxMoment (floorBounds P e) (centeredSet ⌊P⌋₊) P α t c 4≤
        (D*(2 : ℝ)^(r+1)*C)*P^(ε-cap) := by
    apply hb.trans
    calc
      _ ≤ D*(2 : ℝ)^(r+1)*P^(ε/2)*(C*P^(ε/2-cap)) :=
        mul_le_mul_of_nonneg_left hcap (by positivity)
      _ = _ := by
        have hp : P^(ε/2)*P^(ε/2-cap)=P^(ε-cap) := by
          rw [← Real.rpow_add hPp]
          congr 1
          ring
        calc
          _ = (D*(2 : ℝ)^(r+1)*C)*(P^(ε/2)*P^(ε/2-cap)) := by ring
          _ = _ := by rw [hp]
  exact ⟨hfinish _ hn.1,hfinish _ hn.2⟩

#print axioms normalized_fourth_fixed_support
#print axioms quadratic_floor_box_fourth
end Waring.PolicyCompletionFourthBox
