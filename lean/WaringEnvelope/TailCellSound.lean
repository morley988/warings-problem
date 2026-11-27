import WaringEnvelope.WeylCells

/-! # Soundness of an accepted integer tail-cell certificate

The three guards in `tailCell` are the three real Weyl inequalities,
with denominators cleared. A successful tail covers every real conductor
between its previous endpoint and its modulus.
-/

noncomputable section

namespace WaringEnvelope

private theorem slopes_positive (i : ℕ) : 0 < (slopes i).2 ∧ (slopes i).2 ≤ (slopes i).1 := by
  generalize he : slopes i = v
  unfold slopes at he
  split at he <;> subst v <;> decide

private theorem frac_sub_guard (n d x y z w : ℝ) (hd : 0 < d) (hy : 0 < y)
    (hw : 0 < w) (h : n*y*w+x*d*w ≤ z*d*y) : n/d ≤ z/w-x/y := by
  rw [le_sub_iff_add_le]
  have hrewrite : n/d + x/y = (n*y+x*d)/(d*y) := by
    field_simp
  rw [hrewrite]
  apply (div_le_div_iff₀ (mul_pos hd hy) hw).2
  linarith only [h]

/-- The raw integer certificate implies genuine Weyl coverage at every real
conductor above the preceding certified endpoint. -/
theorem tailCell_sound (K m sig p idx : ℕ) (u : ℝ) (hk : 0 < K)
    (hc : tailCell K m sig p idx = true) (hl : (p : ℝ)/B ≤ u) (hu : u ≤ (m : ℝ)/B) :
    WeylBranch K ((m : ℝ)/(B*K)) u ((sig : ℝ)/T) := by
  obtain ⟨e,f,hef⟩ : ∃ e f, slopes idx = (e,f) := ⟨_,_,(slopes idx).eta.symm⟩
  have hsf := slopes_positive idx
  rw [hef] at hsf
  obtain ⟨hf, hfe⟩ := hsf
  let nn := e*F+f
  let num := sig*e*nn*m^2
  let den := T*f^2*F*B^2
  have hg : F*B ≤ p ∧ e*m+f*B ≤ f*B*K ∧
      num*(e*F+2*f)*f*F*B^2*K + nn*m^2*(e*F+2*f)*den ≤ f^2*F^2*B^2*K*den ∧
      num*e*B*K + e*m*den ≤ (e-f)*B*K*den ∧
      num*f*F*B^2*K + nn*m^2*den ≤ (e-f)*F^2*B^2*K*den := by
    simpa only [tailCell, hef, nn, num, den, Bool.and_eq_true, decide_eq_true_eq,
      and_assoc] using hc
  obtain ⟨hcut,hdg,hA,hB,hC⟩ := hg
  have hBp : (0 : ℝ) < B := by norm_num [B]
  have hTp : (0 : ℝ) < T := by norm_num [T]
  have hFp : (0 : ℝ) < F := by norm_num [F]
  have hfp : 0 < (f : ℝ) := by exact_mod_cast hf
  have hfe' : (f : ℝ) ≤ e := by exact_mod_cast hfe
  have hep : 0 < (e : ℝ) := lt_of_lt_of_le hfp hfe'
  have hkp : 0 < (K : ℝ) := by exact_mod_cast hk
  have hn : (nn : ℝ) = e*F+f := by dsimp [nn]; push_cast; rfl
  have hnum : (num : ℝ) = sig*e*nn*(m:ℝ)^2 := by dsimp [num]; push_cast; rfl
  have hden : (den : ℝ) = T*(f:ℝ)^2*F*(B:ℝ)^2 := by dsimp [den]; push_cast; rfl
  have hdp : (0 : ℝ) < den := by rw [hden]; positivity
  have hcut' : (F : ℝ) ≤ (p : ℝ)/B := (le_div_iff₀ hBp).2 (by exact_mod_cast hcut)
  have hdg' : (e : ℝ)*m+f*B ≤ f*B*K := by exact_mod_cast hdg
  have hdeg : ((e : ℝ)/f)*(m/B)+1 ≤ K := by
    have hrewrite : ((e : ℝ)/f)*(m/B)+1 = (e*m+f*B)/(f*B) := by field_simp
    rw [hrewrite]
    exact (div_le_iff₀ (mul_pos hfp hBp)).2 (by linarith only [hdg'])
  have hA' : (num : ℝ)*(e*F+2*f)*f*F*(B:ℝ)^2*K +
      nn*(m:ℝ)^2*(e*F+2*f)*den ≤ (f:ℝ)^2*(F:ℝ)^2*(B:ℝ)^2*K*den := by
    exact_mod_cast hA
  have hB' : (num : ℝ)*e*B*K + e*m*den ≤ ((e:ℝ)-f)*B*K*den := by
    exact_mod_cast (by simpa only [Nat.cast_sub hfe] using hB)
  have hC' : (num : ℝ)*f*F*(B:ℝ)^2*K + nn*(m:ℝ)^2*den ≤
      ((e:ℝ)-f)*(F:ℝ)^2*(B:ℝ)^2*K*den := by
    exact_mod_cast (by simpa only [Nat.cast_sub hfe] using hC)
  have hcore : (sig:ℝ)/T*(e/f)*(e/f+1/F)*(m/B)^2 = (num:ℝ)/den := by
    rw [hnum,hden,hn]
    field_simp
  have hb : ((e:ℝ)/f+1/F)*(m/B)*(m/(B*K)) =
      nn*(m:ℝ)^2/(f*F*(B:ℝ)^2*K) := by
    rw [hn]
    field_simp
  have hpos : 0 < (f:ℝ)*F*(B:ℝ)^2*K := by positivity
  apply continuous_weyl_tail K ((m:ℝ)/(B*K)) u ((sig:ℝ)/T) F (e/f) (m/B)
    (by norm_num [F]) ((one_le_div hfp).2 hfe') (by positivity) (by positivity)
    (hcut'.trans hl) hu hdeg
  · rw [hcore,hb]
    have hr : 1/((e:ℝ)/f+2/F) = f*F/(e*F+2*f) := by
      field_simp
    rw [hr]
    apply frac_sub_guard _ _ _ _ _ _ hdp hpos (by positivity)
    linarith only [hA']
  · rw [hcore]
    have hr : 1-1/((e:ℝ)/f) = (e-f)/e := by field_simp
    rw [hr]
    apply frac_sub_guard _ _ _ _ _ _ hdp (by positivity) hep
    linarith only [hB']
  · rw [hcore,hb]
    have hr : ((e:ℝ)/f-1)*F = ((e-f)*F)/f := by field_simp
    rw [hr]
    apply frac_sub_guard _ _ _ _ _ _ hdp hpos hfp
    linarith only [mul_le_mul_of_nonneg_right hC' hfp.le]

/-- At the infinite cap M ≤ sqrt(k)/8, a uniform strict margin is
available at every real U in [120,M]. The height in the scalar integral
is 1/(14 M²). -/
theorem infinite_weyl_tail (k : ℕ) (θ u M : ℝ) (hθ₀ : 0 ≤ θ)
    (hθ : θ ≤ M/k) (hl : 120 ≤ u) (hu : u ≤ M) (hcap : 64*M^2 ≤ k) :
    2/(14*M^2) < ((1/7:ℝ)+1/1000)/M^2 ∧
      WeylBranch k θ u (((1/7:ℝ)+1/1000)/M^2) := by
  have hMmin := hl.trans hu
  have hM : 0 < M := by linarith
  have hk : 0 < (k : ℝ) := lt_of_lt_of_le (by positivity : 0 < 64*M^2) hcap
  have hMθ : M*θ ≤ 1/64 := calc
    _ ≤ M*(M/k) := mul_le_mul_of_nonneg_left hθ hM.le
    _ = M^2/k := by ring
    _ ≤ 1/64 := (div_le_iff₀ hk).2 (by linarith only [hcap])
  have hθmin := mul_le_mul_of_nonneg_right hMmin hθ₀
  have hj : (3/2:ℝ)*M+1 ≤ k := by nlinarith [sq_nonneg (M-1)]
  have hW : (((1/7:ℝ)+1/1000)/M^2)*(3/2)*(3/2+1/120)*M^2 =
      ((1/7:ℝ)+1/1000)*(3/2)*(3/2+1/120) := by field_simp
  constructor
  · field_simp
    nlinarith
  · apply continuous_weyl_tail k θ u (((1/7:ℝ)+1/1000)/M^2) 120 (3/2) M
      (by norm_num) (by norm_num) hθ₀ (by positivity) hl hu hj
    · rw [hW]
      linarith only [hMθ]
    · rw [hW]
      linarith only [hMθ,hθmin]
    · rw [hW]
      linarith only [hMθ]

/-- A witness for a certified Weyl cell tolerates smaller radical loss
and saving targets, and any larger maximum polynomial degree. -/
theorem WeylBranch.mono {k k' : ℕ} {θ θ' u σ σ' : ℝ}
    (branch : WeylBranch k θ u σ) (hk : k ≤ k') (ht : θ' ≤ θ) (hs : σ' ≤ σ) :
    WeylBranch k' θ' u σ' := by
  obtain ⟨j,hj,hjk,h₁,h₂,h₃⟩ := branch
  have hloss := mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg (α := ℝ) j)
  have hsave := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg (α := ℝ) (weylWeight j))
  exact ⟨j,hj,hjk.trans hk,by linarith only [h₁,hloss,hsave],
    by linarith only [h₂,ht,hsave],by linarith only [h₃,hloss,hsave]⟩

#print axioms tailCell_sound
#print axioms infinite_weyl_tail
#print axioms WeylBranch.mono

end WaringEnvelope
