import Waring.PolicyCompletionScaledFourthSample

noncomputable section
open scoped BigOperators
namespace Waring.PolicyCompletionScaledFourthBox
open RationalHeight NormalizedQuadratic CartesianProductSampling
open CartesianResourceMoments CartesianFloorScales ProductMultiplicity
open CartesianPolynomialBounds PolicyCompletionScaledBounds
open PolicyCompletionScaledFourthSample

theorem quadratic_floor_box_fourth {r : ℕ} (Dscale : ℝ) (hDscale : 1≤Dscale) (e : Fin r→ℝ) (he : ∀i,0<e i)
    (c : ℕ) (hc : 0<c) {ε : ℝ} (hε : 0<ε) :
    ∃K P₀ : ℝ,0<K ∧ 2≤P₀ ∧ ∀P : ℝ,P₀≤P→∀α ell t : ℝ,
      P^ell≤height (P^((∑i,e i)+2)) α→
      quadraticBoxMoment (scaledBounds Dscale P e) (centeredSet ⌊Dscale*P⌋₊) P α t c 4≤
        K*P^(ε-z4Saving ell (∑i,e i)) ∧
      quadraticBoxMoment (scaledBounds Dscale P e) (centeredSet ⌊Dscale*P⌋₊) P α t c 4≤
        K*P^(ε-z4RefinedSaving ell (∑i,e i)) := by
  let E := ∑i,e i
  have hE : 0≤E := Finset.sum_nonneg (fun i _=>(he i).le)
  have hB : 0≤E+1 := by linarith
  obtain ⟨C,hC,hsample⟩ := normalized_fourth_fixed_dilations
    (5*Dscale) (2*Dscale^r) (by linarith)
    (by have hp : (1 : ℝ)≤Dscale^r := one_le_pow₀ hDscale; linarith) (E+1) hB c hc (half_pos hε)
  obtain ⟨D,hD,hbox⟩ := quadratic_fourth_box_to_sample r hB (half_pos hε)
  obtain ⟨P₁,hP₁,hscales⟩ := eventual_scaled_scales Dscale hDscale e he
  let P₀ := max 2 P₁
  refine ⟨D*(2 : ℝ)^(r+1)*C,P₀,by positivity,le_max_left _ _,?_⟩
  intro P hPP₀ α ell t hheight
  have hP2 : 2≤P := (le_max_left _ _).trans hPP₀
  have hP1 : 1≤P := by linarith
  have hPp : 0<P := by linarith
  have hPP₁ : P₁≤P := (le_max_right _ _).trans hPP₀
  have hs := hscales P hPP₁
  let J := scaledCutoff Dscale P e
  have hJbase : P^E≤(J : ℝ) :=
    (le_mul_of_one_le_left (Real.rpow_nonneg hPp.le _) (one_le_pow₀ hDscale)).trans
      (Nat.le_ceil (Dscale^r*P^E))
  have hJlower : 1≤(J : ℝ) := (Real.one_le_rpow hP1 hE).trans hJbase
  have hJupper : (J : ℝ)≤(2*Dscale^r)*P^E := by
    simpa only [mul_assoc] using scaled_cutoff_le_twice_power hDscale e (fun i=>(he i).le) hP1
  have hJscale : (J : ℝ)≤P^(E+1) := hs.2.2.2.2.2
  have hconduct : P^(E+2)≤(J : ℝ)*P^2 := by
    have hh := mul_le_mul_of_nonneg_right hJbase (sq_nonneg P)
    simpa only [Real.rpow_add hPp,Real.rpow_two,J,scaledCutoff,E] using hh
  have hheight' : P^ell≤height ((J : ℝ)*P^2) α :=
    hheight.trans (height_mono_conductor (by positivity) hconduct)
  let a : ℤ := -(2*(⌊Dscale*P⌋₊ : ℤ))
  let b : ℤ := 2*(⌊Dscale*P⌋₊ : ℤ)
  have hab : a≤b := by dsimp [a,b]; omega
  have hlength : (((b+1-a).toNat : ℕ) : ℝ)≤(5*Dscale)*P := by
    have hz : 0≤b+1-a := by omega
    have he : ((b+1-a).toNat : ℤ)=b+1-a := Int.toNat_of_nonneg hz
    have heR : (((b+1-a).toNat : ℕ) : ℝ)=((b+1-a : ℤ) : ℝ) := by exact_mod_cast he
    rw [heR]
    dsimp [a,b]
    push_cast
    have hDsp : 0<Dscale := zero_lt_one.trans_le hDscale
    have hf := Nat.floor_le (mul_nonneg hDsp.le hPp.le)
    have hbase : 1≤Dscale*P := one_le_mul_of_one_le_of_one_le hDscale hP1
    nlinarith only [hf,hbase]
  have hn := hsample P hP2 J hJlower hJscale α ell E hJupper hheight'
    (Finset.Icc 1 J) (fun _=>a) (fun _=>b) (fun _=>t)
    (by intro q hq; rcases Finset.mem_Icc.mp hq with ⟨h1,h2⟩; exact ⟨h1,by exact_mod_cast h2⟩)
    (fun _ _=>hab) (fun _ _=>hlength)
  have hb := hbox P hP1 (scaledBounds Dscale P e) hs.1 J hs.2.2.2.1 hJscale
    ((2 : ℝ)^(r+1)) hs.2.2.2.2.1 a b α t c
  have hfinish (cap : ℝ) (hcap : normalizedFourth (Finset.Icc 1 J)
      (fun _=>a) (fun _=>b) (fun _=>t) c P J α≤C*P^(ε/2-cap)) :
      quadraticBoxMoment (scaledBounds Dscale P e) (centeredSet ⌊Dscale*P⌋₊) P α t c 4≤
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

#print axioms quadratic_floor_box_fourth
end Waring.PolicyCompletionScaledFourthBox
