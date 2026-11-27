import Waring.PolicyCompletionQuadraticBox

/-!
# Literal z2 averages of the source's completed polynomial factors

The completed quadratic support is [-2N,2N] and the exact normalizer is
4N+1, with N=floor(P). These constants and floors are retained in the
definitions and then discharged using the proved physical-support theorem.
-/

noncomputable section
open scoped BigOperators

namespace Waring.PolicyCompletionQuadraticFactors
open PolicyCompletionQuadraticBox CartesianMomentAdapters CartesianResourceMoments
open CartesianFloorScales CartesianProductSampling FiniteResourceHolder
open CartesianPolynomialBounds ResourceDifferencingCap RationalHeight

theorem quadraticBoxMoment_mono_cap {r : ℕ} (bounds : Fin r → ℕ)
    (S : Finset ℤ) (α t : ℝ) (c q : ℕ) {P cap : ℝ} (hP : 0 < P) (hcap : P ≤ cap) :
    quadraticBoxMoment bounds S cap α t c q ≤
      quadraticBoxMoment bounds S P α t c q := by
  unfold quadraticBoxMoment average
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Finset.sum_le_sum
  intro x hx
  apply pow_le_pow_left₀ (div_nonneg (norm_nonneg _) (hP.le.trans hcap))
  exact div_le_div_of_nonneg_left (norm_nonneg _) hP hcap

theorem floor_centered_support {P : ℝ} (hP : 0 ≤ P) :
    ∀ z ∈ centeredSet ⌊P⌋₊, |(z : ℝ)| ≤ 2*P := by
  intro z hz
  have hzR : -(2*(⌊P⌋₊ : ℝ)) ≤ (z : ℝ) ∧ (z : ℝ) ≤ 2*(⌊P⌋₊ : ℝ) := by
    exact_mod_cast Finset.mem_Icc.mp hz
  have hfloor := Nat.floor_le hP
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem floor_quadratic_cap {P : ℝ} (hP : 2 ≤ P) : P ≤ 4*(⌊P⌋₊ : ℝ)+1 := by
  have hfloor := half_le_floor hP
  linarith

theorem floorBounds_cons_one {j : ℕ} (P : ℝ) (e : Fin j → ℝ) :
    floorBounds P (Fin.cons (α := fun _ => ℝ) 1 e)=Fin.cons ⌊P⌋₊ (floorBounds P e) := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [floorBounds]
  · simp [floorBounds]

/-- The literal first ordinary-difference quadratic factor, with no
sampling, padding, fixed-support, or conductor-comparison premise. -/
theorem firstFactors_z2_on_floor_box {j : ℕ} (e : Fin j → ℝ)
    (he : ∀ i, 0 < e i) (hsum : 0 < ∑ i, e i)
    (rho : ℝ) (hrho : 0 ≤ rho) (A : ℕ) (hA : 0 < A) {ε : ℝ} (hε : 0 < ε) :
    ∃ η K P₀ : ℝ, 0 < η ∧ 0 < K ∧ 2 ≤ P₀ ∧
      ∀ P : ℝ, P₀ ≤ P → ∀ R : ℝ, 1 ≤ R → R ≤ P^η →
      ∀ α t : ℝ, P/R^rho ≤ height (P^((∑ i, e i)+3)) α →
      ∀ (p : ℕ) (C : Fin j → Finset ℝ) (V : Fin j → ℝ),
      average (fun x : realBox (floorBounds P e) ×ˢ Finset.Icc (1 : ℤ) (⌊P⌋₊ : ℤ) =>
        (firstFactors p (A : ℝ) α C ⌊P⌋₊ V t none x.val)^2) ≤ K*P^(ε-1) := by
  have he' : ∀ i : Fin (j+1), (0 : ℝ) < Fin.cons (α := fun _ => ℝ) 1 e i := by
    intro i
    refine Fin.cases (by norm_num) (fun i => he i) i
  have hs' : 1 < ∑ i : Fin (j+1), Fin.cons (α := fun _ => ℝ) 1 e i := by
    simpa only [Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ,lt_add_iff_pos_right] using hsum
  obtain ⟨η,K,P₀,hη,hK,hP₀,hbound⟩ := quadratic_floor_box_second
    (Fin.cons (α := fun _ => ℝ) 1 e) he' hs' rho 2 hrho (by norm_num) (3*A) (by omega) hε
  refine ⟨η,K,P₀,hη,hK,hP₀,?_⟩
  intro P hPP₀ R hR hRup α t hheight p C V
  have hP2 := hP₀.trans hPP₀
  have hPp : 0 < P := by linarith
  have hexp : (∑ i : Fin (j+1), Fin.cons (α := fun _ => ℝ) 1 e i)+2=(∑ i, e i)+3 := by
    simp only [Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ]
    ring
  have hb := hbound P hPP₀ R hR hRup α t (centeredSet ⌊P⌋₊)
    (floor_centered_support hPp.le) (by simpa only [hexp] using hheight)
  rw [floorBounds_cons_one] at hb
  rw [first_quadratic_moment_eq]
  exact (quadraticBoxMoment_mono_cap _ _ α t (3*A) 2 hPp
    (floor_quadratic_cap hP2)).trans hb

/-- The literal zero-ordinary-difference factor at a quadratic terminal. -/
theorem zeroFactors_z2_on_floor_box {j : ℕ} (e : Fin j → ℝ)
    (he : ∀ i, 0 < e i) (hsum : 1 < ∑ i, e i)
    (rho : ℝ) (hrho : 0 ≤ rho) (A : ℕ) (hA : 0 < A) {ε : ℝ} (hε : 0 < ε) :
    ∃ η K P₀ : ℝ, 0 < η ∧ 0 < K ∧ 2 ≤ P₀ ∧
      ∀ P : ℝ, P₀ ≤ P → ∀ R : ℝ, 1 ≤ R → R ≤ P^η →
      ∀ α t : ℝ, P/R^rho ≤ height (P^((∑ i, e i)+2)) α →
      ∀ (p : ℕ) (C : Fin j → Finset ℝ) (V : Fin j → ℝ),
      average (fun x : realBox (floorBounds P e) =>
        (zeroFactors p (A : ℝ) α C ⌊P⌋₊ V t none x.val)^2) ≤ K*P^(ε-1) := by
  obtain ⟨η,K,P₀,hη,hK,hP₀,hbound⟩ := quadratic_floor_box_second
    e he hsum rho 2 hrho (by norm_num) (3*A) (by omega) hε
  refine ⟨η,K,P₀,hη,hK,hP₀,?_⟩
  intro P hPP₀ R hR hRup α t hheight p C V
  have hP2 := hP₀.trans hPP₀
  have hPp : 0 < P := by linarith
  have hb := hbound P hPP₀ R hR hRup α t (centeredSet ⌊P⌋₊)
    (floor_centered_support hPp.le) hheight
  rw [zero_quadratic_moment_eq]
  exact (quadraticBoxMoment_mono_cap _ _ α t (3*A) 2 hPp
    (floor_quadratic_cap hP2)).trans hb

/-- The literal two-ordinary-difference quadratic factor. -/
theorem secondFactors_z2_on_floor_box {j : ℕ} (e : Fin j → ℝ)
    (he : ∀ i, 0 < e i)
    (rho : ℝ) (hrho : 0 ≤ rho) (A : ℕ) (hA : 0 < A) {ε : ℝ} (hε : 0 < ε) :
    ∃ η K P₀ : ℝ, 0 < η ∧ 0 < K ∧ 2 ≤ P₀ ∧
      ∀ P : ℝ, P₀ ≤ P → ∀ R : ℝ, 1 ≤ R → R ≤ P^η →
      ∀ α t : ℝ, P/R^rho ≤ height (P^((∑ i, e i)+4)) α →
      ∀ (p : ℕ) (C : Fin j → Finset ℝ) (V : Fin j → ℝ),
      average (fun x : (realBox (floorBounds P e) ×ˢ Finset.Icc (1 : ℤ) (⌊P⌋₊ : ℤ)) ×ˢ
          Finset.Icc (1 : ℤ) (⌊P⌋₊ : ℤ) =>
        (secondFactors p (A : ℝ) α C ⌊P⌋₊ V t none x.val)^2) ≤ K*P^(ε-1) := by
  have he' : ∀ i : Fin (j+2), (0 : ℝ) < Fin.cons (α := fun _ => ℝ) 1 (Fin.cons (α := fun _ => ℝ) 1 e) i := by
    intro i
    refine Fin.cases (by norm_num) (fun i => ?_) i
    exact Fin.cases (by norm_num) (fun i => he i) i
  have hsum : 0 ≤ ∑ i, e i := Finset.sum_nonneg (fun i _ => (he i).le)
  have hs' : 1 < ∑ i : Fin (j+2), Fin.cons (α := fun _ => ℝ) 1 (Fin.cons (α := fun _ => ℝ) 1 e) i := by
    simp only [Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ]
    linarith
  obtain ⟨η,K,P₀,hη,hK,hP₀,hbound⟩ := quadratic_floor_box_second
    (Fin.cons (α := fun _ => ℝ) 1 (Fin.cons (α := fun _ => ℝ) 1 e)) he' hs' rho 2 hrho (by norm_num) (3*A) (by omega) hε
  refine ⟨η,K,P₀,hη,hK,hP₀,?_⟩
  intro P hPP₀ R hR hRup α t hheight p C V
  have hP2 := hP₀.trans hPP₀
  have hPp : 0 < P := by linarith
  have hexp : (∑ i : Fin (j+2), Fin.cons (α := fun _ => ℝ) 1 (Fin.cons (α := fun _ => ℝ) 1 e) i)+2=(∑ i, e i)+4 := by
    simp only [Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ]
    ring
  have hb := hbound P hPP₀ R hR hRup α t (centeredSet ⌊P⌋₊)
    (floor_centered_support hPp.le) (by simpa only [hexp] using hheight)
  rw [floorBounds_cons_one,floorBounds_cons_one] at hb
  rw [second_quadratic_moment_eq]
  exact (quadraticBoxMoment_mono_cap _ _ α t (3*A) 2 hPp
    (floor_quadratic_cap hP2)).trans hb

#print axioms firstFactors_z2_on_floor_box
#print axioms zeroFactors_z2_on_floor_box
#print axioms secondFactors_z2_on_floor_box
end Waring.PolicyCompletionQuadraticFactors
