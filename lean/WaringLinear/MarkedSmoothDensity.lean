import WaringLinear.MarkedSelection

/-! Existence of arbitrarily smooth marked sets of positive lower density. -/
noncomputable section
open Finset Filter
open scoped Classical BigOperators
namespace WaringLinear.MarkedMass

/-- Explicitly admissible, mutually disjoint exponent windows at every smoothness
cutoff. The integer numerators of their exponents are consecutive. -/
theorem exists_small_windows (η : ℝ) (hη : 0 < η) :
    ∃ (N : ℕ) (γ : ℝ) (v : Fin N → ℝ), 1 < γ ∧
      (∀ i,0 < v i) ∧ (∀ i j,i≠j → γ*v i ≤ v j ∨ γ*v j ≤ v i) ∧
      γ*(∑ i,v i) ≤ 1 ∧ (∀ i, 1 - (∑ j,v j) ≤ v i) ∧
      (∀ i, γ*v i ≤ η) ∧ 1-(∑ j,v j) ≤ η ∧ 2*PrimeWindow.upper*Real.log γ ≤ 1 := by
  obtain ⟨N,hN⟩ := exists_nat_gt (4/η)
  have hN' : 0 < (N:ℝ) := (div_pos (by norm_num) hη).trans hN
  have hN1 : 1 ≤ N := by exact_mod_cast (show 0 < N by exact_mod_cast hN')
  have hNη : 4 < η*(N:ℝ) := by simpa [mul_comm] using (div_lt_iff₀ hη).mp hN
  let w (i : Fin N) : ℝ := (N:ℝ) + i.val
  let S := ∑ i,w i
  have hw (i : Fin N) : (N:ℝ) ≤ w i ∧ w i ≤ 2*N := by
    have hi : (i.val:ℝ)<N := by exact_mod_cast i.isLt
    dsimp [w]
    constructor <;> linarith [Nat.cast_nonneg (α:=ℝ) i.val]
  have hS : (N:ℝ)*(N:ℝ) ≤ S := by
    have h := sum_le_sum (s:=univ) (fun i _ => (hw i).1)
    simpa only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,S] using h
  have hS0 : 0 ≤ S := (mul_nonneg hN'.le hN'.le).trans hS
  have hD : 0 < S+1 := by linarith
  let ε := (S+1+2*PrimeWindow.upper)⁻¹
  have hU := PrimeWindow.positive_constants.2
  have hZ : 0 < S+1+2*PrimeWindow.upper := by linarith
  have hε : 0 < ε := inv_pos.mpr hZ
  have hεD : ε*(S+1) ≤ 1 := by
    dsimp [ε]
    rw [inv_mul_le_iff₀ hZ]
    linarith
  have hεU : ε*(2*PrimeWindow.upper) ≤ 1 := by
    dsimp [ε]
    rw [inv_mul_le_iff₀ hZ]
    linarith
  have hε1 : ε ≤ 1 := by nlinarith [mul_nonneg hε.le hS0]
  let γ := 1+ε
  let v := fun i => w i/(S+1)
  have hγ : 1 < γ := by dsimp [γ]; linarith
  have hv (i) : 0 < v i := div_pos (hN'.trans_le (hw i).1) hD
  have hsum : (∑ i,v i) = S/(S+1) := by rw [← Finset.sum_div]
  have hdif : 1 - (∑ i,v i) = 1/(S+1) := by rw [hsum]; field_simp; ring
  have hγw (i : Fin N) : γ*w i ≤ w i+1 := by
    have hi : w i ≤ S := single_le_sum (s:=univ) (fun j _ => hN'.le.trans (hw j).1) (mem_univ i)
    have h := mul_le_mul_of_nonneg_left (show w i ≤ S+1 by linarith) hε.le
    dsimp [γ]; nlinarith
  have hsep (i j : Fin N) (hij : i < j) : γ*v i ≤ v j := by
    have hh : i.val+1≤j.val := hij
    have hh' : (i.val:ℝ)+1≤j.val := by exact_mod_cast hh
    change γ*(w i/(S+1)) ≤ w j/(S+1)
    rw [←mul_div_assoc]
    exact (div_le_div_iff_of_pos_right hD).mpr ((hγw i).trans (by dsimp [w]; linarith))
  have hηS : 4 * N ≤ η * (S+1) := by
    have h1 := mul_le_mul_of_nonneg_right hNη.le hN'.le
    have h2 := mul_le_mul_of_nonneg_left hS hη.le
    nlinarith
  refine ⟨N,γ,v,hγ,hv,?_,?_,?_,?_,?_,?_⟩
  · intro i j h
    rcases lt_or_gt_of_ne h with hij|hji
    exacts [Or.inl (hsep i j hij),Or.inr (hsep j i hji)]
  · rw [hsum,←mul_div_assoc,div_le_iff₀ hD]
    dsimp [γ]; nlinarith
  · intro i
    rw [hdif]
    exact (div_le_div_iff_of_pos_right hD).mpr ((by exact_mod_cast hN1 : (1:ℝ)≤N).trans (hw i).1)
  · intro i
    change γ*(w i/(S+1)) ≤ η
    rw [←mul_div_assoc,div_le_iff₀ hD]
    have h2 : γ≤2 := by dsimp [γ]; linarith
    have hh := mul_le_mul h2 (hw i).2 (hN'.le.trans (hw i).1) (by norm_num : (0:ℝ)≤2)
    linarith
  · rw [hdif,div_le_iff₀ hD]
    have hon : (1:ℝ)≤N := by exact_mod_cast hN1
    linarith
  · have hl := Real.log_le_sub_one_of_pos (zero_lt_one.trans hγ)
    have h := mul_le_mul_of_nonneg_left hl (show 0 ≤ 2*PrimeWindow.upper by positivity)
    dsimp [γ] at *
    nlinarith

/-- For every fixed positive smoothness exponent, a positive proportion of the
integers up to X have every prime factor at most X^η. -/
theorem smooth_positive_density (η : ℝ) (hη : 0<η) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ P : ℝ in atTop,
      c*P ≤ ((Waring.SmoothMoments.smoothNumbers P (P^η)).card : ℝ) := by
  obtain ⟨N,γ,v,hγ,hv,hsep,hu,hb,hm,hc,_⟩ := exists_small_windows η hη
  obtain ⟨c,hc',hprop⟩ := power_window_positive_density γ v hγ hv hsep hu hb
  refine ⟨c,hc',?_⟩
  filter_upwards [hprop, Filter.eventually_gt_atTop (1:ℝ)] with P hp hP
  have hs := child_smooth_at_scale P γ 1 η (fun i : Fin 0 => Fin.elim0 i) v
    (fun i : Fin 0 => Fin.elim0 i) hP hη.le (fun i => Fin.elim0 i) (by simp)
    (fun i => by simpa using hm i) (by simpa using hc)
  simp only [Fin.prod_univ_zero,Nat.cast_one,div_one] at hs
  exact hp.2.trans (by exact_mod_cast Finset.card_le_card hs)

#print axioms exists_small_windows
#print axioms smooth_positive_density
end WaringLinear.MarkedMass
