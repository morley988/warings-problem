import Waring.SeedCompletionNinthDoubleCount

/-!
# Box-uniform degree-nine second auxiliary second moment

The polynomial size restriction in divisor grouping is discharged on
positive boxes. Both original smooth coefficients remain free.
-/

noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionNinthDoubleBox
open IntegerDifferencePolynomial SeedCompletionNinthDouble SeedCompletionNinthDoubleCount

/-- A fixed polynomial size bound on the actual five-parameter phase. -/
theorem phase_real_le {h m : Pair} {z : ℕ} {P : ℝ} (hP : 1 ≤ P)
    (hh₁ : (h.1 : ℝ) ≤ P) (hh₂ : (h.2 : ℝ) ≤ P)
    (hm₁ : (m.1 : ℝ) ≤ P) (hm₂ : (m.2 : ℝ) ≤ P)
    (hz : (z : ℝ) ≤ P) :
    (doublePhase h m z : ℝ) ≤ 19680*P^63 := by
  have hP0 : 0 ≤ P := zero_le_one.trans hP
  have ha : ((amplitude h m).1 : ℝ) ≤ P^10 := by
    unfold amplitude
    push_cast
    calc
      _ ≤ P*P^9 := by gcongr
      _ = _ := by ring
  have hb : ((amplitude h m).2 : ℝ) ≤ P^10 := by
    unfold amplitude
    push_cast
    calc
      _ ≤ P*P^9 := by gcongr
      _ = _ := by ring
  have hmono : (doublePhase h m z : ℝ) ≤
      96*P*P * (3*P^7 +21*((P^10)^2+(P^10)^2)*P^5 +
        (21*((P^10)^4+(P^10)^4)+70*(P^10)^2*(P^10)^2)*P^3 +
        (3*((P^10)^6+(P^10)^6)+21*((P^10)^4*(P^10)^2+(P^10)^2*(P^10)^4))*P) := by
    unfold doublePhase leadingFactor
    push_cast
    gcongr
  have h7 : P^7 ≤ P^61 := pow_le_pow_right₀ hP (by norm_num)
  have h25 : P^25 ≤ P^61 := pow_le_pow_right₀ hP (by norm_num)
  have h43 : P^43 ≤ P^61 := pow_le_pow_right₀ hP (by norm_num)
  have hin : 3*P^7+42*P^25+112*P^43+48*P^61 ≤ 205*P^61 := by linarith
  calc
    _ ≤ _ := hmono
    _ = 96*P^2*(3*P^7+42*P^25+112*P^43+48*P^61) := by ring
    _ ≤ 96*P^2*(205*P^61) := mul_le_mul_of_nonneg_left hin (by positivity)
    _ = _ := by ring

def actualPhase (x : Index) : ℤ :=
  (powerPolynomial 9 [((x.1.2 : ℤ),(x.2.1.2 : ℤ)),
    ((x.1.1 : ℤ),(x.2.1.1 : ℤ))]).eval (x.2.2 : ℤ)

def actualSum (H B : Finset Pair) (Z : Finset ℕ) (α : ℝ) : ℂ :=
  ∑ x ∈ domain H B Z, fourier (actualPhase x) (α : AddCircle (1 : ℝ))

/-- All arithmetic premises except actual positivity and box membership are
discharged, retaining the precise coefficient/root count. -/
theorem actual_second_on_box {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ P₀ : ℝ, 1 ≤ P₀ ∧ ∀ P : ℝ, P₀ ≤ P →
      ∀ H B : Finset Pair, ∀ Z : Finset ℕ,
      (∀ h ∈ H, 0 < h.1 ∧ 0 < h.2) →
      (∀ m ∈ B, 0 < m.1 ∧ 0 < m.2) →
      (∀ z ∈ Z, 0 < z) →
      (∀ h ∈ H, (h.1 : ℝ) ≤ P ∧ (h.2 : ℝ) ≤ P) →
      (∀ m ∈ B, (m.1 : ℝ) ≤ P ∧ (m.2 : ℝ) ≤ P) →
      (∀ z ∈ Z, (z : ℝ) ≤ P) →
      (∫ α in (0 : ℝ)..1, ‖actualSum H B Z α‖^2) ≤
        C*P^ε*(H.card : ℝ)*(B.card : ℝ)*(7*(B.card : ℝ)+2*(Z.card : ℝ)) := by
  obtain ⟨C,hC,hbound⟩ := SeedCompletionNinthDoubleCount.second_moment
    (L := 64) (by norm_num) hε
  refine ⟨C,hC,19680,by norm_num,?_⟩
  intro P hPP₀ H B Z hH hB hZ hHbox hBbox hZbox
  have hP : 1 ≤ P := (by norm_num : (1 : ℝ) ≤ 19680).trans hPP₀
  have hsum (α : ℝ) : actualSum H B Z α =
      ∑ x ∈ domain H B Z, fourier (indexPhase x) (α : AddCircle (1 : ℝ)) := by
    apply Finset.sum_congr rfl
    intro x hx
    have hm := hB x.2.1 (Finset.mem_product.mp (Finset.mem_product.mp hx).2).1
    exact congrArg (fun n => fourier n (α : AddCircle (1 : ℝ)))
      (doublePhase_eq_powerPolynomial x.1 x.2.1 x.2.2 hm.1 hm.2).symm
  simp_rw [hsum]
  apply hbound P hP H B Z hH hZ
  intro x hx
  have hh := hHbox x.1 (Finset.mem_product.mp hx).1
  have hm := hBbox x.2.1 (Finset.mem_product.mp (Finset.mem_product.mp hx).2).1
  have hz := hZbox x.2.2 (Finset.mem_product.mp (Finset.mem_product.mp hx).2).2
  simp only [indexPhase,Int.natAbs_natCast,Real.rpow_natCast]
  calc
    _ ≤ 19680*P^63 := phase_real_le hP hh.1 hh.2 hm.1 hm.2 hz
    _ ≤ P*P^63 := mul_le_mul_of_nonneg_right hPP₀ (by positivity)
    _ = P^64 := by ring
    _ = P^(64 : ℝ) := by norm_num

/-- Fixed dilation of every source box affects only the uniform constant. -/
theorem actual_second_scaled (L : ℝ) (hL : 1 ≤ L) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ P₀ : ℝ, 1 ≤ P₀ ∧ ∀ P : ℝ, P₀ ≤ P →
      ∀ H B : Finset Pair, ∀ Z : Finset ℕ,
      (∀ h ∈ H, 0 < h.1 ∧ 0 < h.2) →
      (∀ m ∈ B, 0 < m.1 ∧ 0 < m.2) →
      (∀ z ∈ Z, 0 < z) →
      (∀ h ∈ H, (h.1 : ℝ) ≤ L*P ∧ (h.2 : ℝ) ≤ L*P) →
      (∀ m ∈ B, (m.1 : ℝ) ≤ L*P ∧ (m.2 : ℝ) ≤ L*P) →
      (∀ z ∈ Z, (z : ℝ) ≤ L*P) →
      (∫ α in (0 : ℝ)..1, ‖actualSum H B Z α‖^2) ≤
        C*P^ε*(H.card : ℝ)*(B.card : ℝ)*(7*(B.card : ℝ)+2*(Z.card : ℝ)) := by
  obtain ⟨C,hC,P₀,hP₀,hbound⟩ := actual_second_on_box hε
  refine ⟨C*L^ε,mul_pos hC (Real.rpow_pos_of_pos (zero_lt_one.trans_le hL) _),P₀,hP₀,?_⟩
  intro P hP H B Z hH hB hZ hHbox hBbox hZbox
  have hP0 : 0 ≤ P := zero_le_one.trans (hP₀.trans hP)
  have hPL : P₀ ≤ L*P := hP.trans (le_mul_of_one_le_left hP0 hL)
  convert hbound (L*P) hPL H B Z hH hB hZ hHbox hBbox hZbox using 1
  rw [Real.mul_rpow (zero_le_one.trans hL) hP0]
  ring

/-- The source diagonal size once the coefficient family has size at most P
and the center family has size at most a fixed multiple of P. -/
theorem actual_second_diagonal_size (L : ℝ) (hL : 1 ≤ L) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ P₀ : ℝ, 1 ≤ P₀ ∧ ∀ P : ℝ, P₀ ≤ P →
      ∀ H B : Finset Pair, ∀ Z : Finset ℕ,
      (∀ h ∈ H, 0 < h.1 ∧ 0 < h.2) →
      (∀ m ∈ B, 0 < m.1 ∧ 0 < m.2) →
      (∀ z ∈ Z, 0 < z) →
      (∀ h ∈ H, (h.1 : ℝ) ≤ L*P ∧ (h.2 : ℝ) ≤ L*P) →
      (∀ m ∈ B, (m.1 : ℝ) ≤ L*P ∧ (m.2 : ℝ) ≤ L*P) →
      (∀ z ∈ Z, (z : ℝ) ≤ L*P) →
      (B.card : ℝ) ≤ P → (Z.card : ℝ) ≤ L*P →
      (∫ α in (0 : ℝ)..1, ‖actualSum H B Z α‖^2) ≤
        C*P^(1+ε)*(H.card : ℝ)*(B.card : ℝ) := by
  obtain ⟨C,hC,P₀,hP₀,hbound⟩ := actual_second_scaled L hL hε
  refine ⟨C*(7+2*L),mul_pos hC (by linarith),P₀,hP₀,?_⟩
  intro P hP H B Z hH hB hZ hHbox hBbox hZbox hBcard hZcard
  have hPpos : 0 < P := zero_lt_one.trans_le (hP₀.trans hP)
  calc
    _ ≤ C*P^ε*(H.card : ℝ)*(B.card : ℝ)*(7*(B.card : ℝ)+2*(Z.card : ℝ)) :=
      hbound P hP H B Z hH hB hZ hHbox hBbox hZbox
    _ ≤ C*P^ε*(H.card : ℝ)*(B.card : ℝ)*(7*P+2*(L*P)) := by gcongr
    _ = _ := by rw [Real.rpow_add hPpos,Real.rpow_one]; ring

#print axioms actual_second_on_box
#print axioms actual_second_diagonal_size
end Waring.SeedCompletionNinthDoubleBox
