import Waring.SeedCompletionEvenFourth

/-! # Literal first auxiliary fourth moment in degrees eight, sixteen, eighteen -/

noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionEvenFourth
open IntegerDifferencePolynomial SeedCompletionBackwardMoments SeedCompletionFirstWeyl
open PolicyCompletionHolder UnseparatedDifferencing FirstDifferenceSecond CoefficientPower SmoothMoments
open SeedCompletionNinthFourthBounds (centers centers_pos centers_width centers_card sum_natural_centers)

/-- All number-theoretic inputs to this actual fourth moment are proved. -/
theorem family_first_fourth_bound (d : ℕ) (hd : supportedHalfDegree d)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ P₀ : ℝ, 1 ≤ P₀ ∧ ∀ P : ℝ, P₀ ≤ P →
      ∀ (H B : Finset ℕ) (N : ℕ),(N : ℝ) ≤ 2*P →
      (∀ h ∈ H,0 < h ∧ (h : ℝ) ≤ 2*P) →
      (∀ m ∈ B,0 < m ∧ (m : ℝ) ≤ 2*P) →
      (B.card : ℝ) ≤ P^(1/3 : ℝ) →
      (∫ α in (0 : ℝ)..1, ‖familyFirstSum (2*d) (H ×ˢ B) N α‖^4) ≤
        C*P^(2+ε)*((H ×ˢ B).card : ℝ)^3 := by
  obtain ⟨C1,hC1,P1,hP1,hfirst⟩ := family_first_second_bound d hd hε
  obtain ⟨C2,hC2,P2,hP2,hdiff⟩ := family_difference_second_bound d hd hε
  refine ⟨8*C1+4*C2,by positivity,max P1 P2,hP1.trans (le_max_left _ _),?_⟩
  intro P hPP H B N hN hH hB hBc
  have hP : 1 ≤ P := hP1.trans ((le_max_left _ _).trans hPP)
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  let A := H ×ˢ B
  have hpos : ∀ b ∈ A,0 < b.1 ∧ 0 < b.2 := by
    intro b hb
    exact ⟨(hH b.1 (Finset.mem_product.mp hb).1).1,
      (hB b.2 (Finset.mem_product.mp hb).2).1⟩
  have hbox : ∀ b ∈ A,(b.1 : ℝ) ≤ 2*P ∧ (b.2 : ℝ) ≤ 2*P := by
    intro b hb
    exact ⟨(hH b.1 (Finset.mem_product.mp hb).1).2,
      (hB b.2 (Finset.mem_product.mp hb).2).2⟩
  have H1 := hfirst P ((le_max_left _ _).trans hPP) A N hN hpos hbox
  have H2 := hdiff P ((le_max_right _ _).trans hPP) H B N hN hH hB hBc
  have H2' : (∫ α in (0 : ℝ)..1, ‖familyDifferenceSum (2*d) A N α‖^2) ≤
      C2*P^(2+ε)*(A.card : ℝ) := by
    exact H2.trans_eq (by simp only [A,Finset.card_product,Nat.cast_mul]; ring)
  have HF := PolicyCompletionFourthMoment.fourier_family_fourth_moment_bound A
    (fun _ => centers N) (firstPhase (2*d)) N (fun b hb => (centers_card N).le)
    (fun b hb => centers_width N)
  change (∫ α in (0 : ℝ)..1, ‖familyFirstSum (2*d) A N α‖^4) ≤
    2*(N : ℝ)*(A.card : ℝ)^2*(∫ α in (0 : ℝ)..1, ‖familyFirstSum (2*d) A N α‖^2)+
    4*(A.card : ℝ)^2*(∫ α in (0 : ℝ)..1, ‖familyDifferenceSum (2*d) A N α‖^2) at HF
  calc
    _ ≤ _ := HF
    _ ≤ 2*(N : ℝ)*(A.card : ℝ)^2*(C1*P^ε*(A.card : ℝ)*N)+
        4*(A.card : ℝ)^2*(C2*P^(2+ε)*(A.card : ℝ)) :=
      add_le_add (mul_le_mul_of_nonneg_left H1 (by positivity))
        (mul_le_mul_of_nonneg_left H2' (by positivity))
    _ = 2*C1*P^ε*(N : ℝ)^2*(A.card : ℝ)^3+
        4*C2*P^(2+ε)*(A.card : ℝ)^3 := by ring
    _ ≤ 2*C1*P^ε*(2*P)^2*(A.card : ℝ)^3+
        4*C2*P^(2+ε)*(A.card : ℝ)^3 := by gcongr
    _ = _ := by rw [Real.rpow_add hPpos,Real.rpow_two]; ring

theorem sourceFirstSum_eq_family (d : ℕ) (P H Q R M α : ℝ) :
    sourceFirstSum d P H Q R M α =
      familyFirstSum (2*d) (Finset.Icc 1 ⌊H⌋₊ ×ˢ coefficientBlock Q R M) ⌊2*P⌋₊ α := by
  unfold sourceFirstSum sourceFirstDomain familyFirstSum familySum firstPhase
  simp only [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro m hm
  exact sum_natural_centers ⌊2*P⌋₊
    (fun z => fourier ((powerPolynomial (2*d) [((h : ℤ),(m : ℤ))]).eval z)
      (α : AddCircle (1 : ℝ)))

/-- The sharp literal source F1 fourth moment. The extra coefficient cap is
satisfied uniformly at every first-stage scale M=P^φ with φ≤1/k and small R. -/
theorem source_even_first_fourth_moment (d : ℕ) (hd : supportedHalfDegree d)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ P₀ : ℝ, 1 ≤ P₀ ∧ ∀ P : ℝ, P₀ ≤ P →
      ∀ H Q R M : ℝ,1 ≤ H → H ≤ 2*P → 1 ≤ M → 1 ≤ R →
      M*R ≤ P^(1/3 : ℝ) → R ≤ P^(ε/6) →
      (∫ α in (0 : ℝ)..1, ‖sourceFirstSum d P H Q R M α‖^4) ≤
        C*P^(2+ε)*M^3*H^3 := by
  obtain ⟨C,hC,P₀,hP₀,hbound⟩ := family_first_fourth_bound d hd
    (show 0 < ε/2 by positivity)
  refine ⟨C,hC,P₀,hP₀,?_⟩
  intro P hPP₀ H Q R M hH hHP hM hR hMR hRP
  have hP : 1 ≤ P := hP₀.trans hPP₀
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hpow : P^(1/3 : ℝ) ≤ P := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hP
      (show (1/3 : ℝ) ≤ 1 by norm_num)
  have hposH : ∀ h ∈ Finset.Icc 1 ⌊H⌋₊,0 < h ∧ (h : ℝ) ≤ 2*P := by
    intro h hh
    exact ⟨(Finset.mem_Icc.mp hh).1,
      ((Nat.cast_le.mpr (Finset.mem_Icc.mp hh).2).trans (Nat.floor_le hH0)).trans hHP⟩
  have hposB : ∀ m ∈ coefficientBlock Q R M,0 < m ∧ (m : ℝ) ≤ 2*P := by
    intro m hm
    refine ⟨(mem_smoothNumbers.mp (Finset.mem_filter.mp hm).1).1.1,?_⟩
    exact ((Finset.mem_filter.mp hm).2.2).trans (hMR.trans (hpow.trans (by linarith)))
  have hc : ((coefficientBlock Q R M).card : ℝ) ≤ M*R := by
    calc
      _ ≤ ((smoothNumbers (M*R) R).card : ℝ) := by
        exact_mod_cast Finset.card_le_card (coefficientBlock_subset Q R M)
      _ ≤ (⌊M*R⌋₊ : ℝ) := by exact_mod_cast smoothNumbers_card_le (M*R) R
      _ ≤ M*R := Nat.floor_le (mul_nonneg hM0 hR0)
  let A := Finset.Icc 1 ⌊H⌋₊ ×ˢ coefficientBlock Q R M
  have hAcard : (A.card : ℝ) ≤ H*M*R := by
    simp only [A,Finset.card_product,Nat.card_Icc,Nat.add_sub_cancel,Nat.cast_mul]
    exact (mul_le_mul (Nat.floor_le hH0) hc (Nat.cast_nonneg _) hH0).trans_eq (by ring)
  have hb := hbound P hPP₀ (Finset.Icc 1 ⌊H⌋₊) (coefficientBlock Q R M) ⌊2*P⌋₊
    (Nat.floor_le (by positivity)) hposH hposB (hc.trans hMR)
  have hRpow : R^3 ≤ P^(ε/2) := by
    calc
      _ ≤ (P^(ε/6))^3 := pow_le_pow_left₀ hR0 hRP 3
      _ = P^(ε/2) := by
        rw [← Real.rpow_mul_natCast hPpos.le]
        congr 1
        norm_num
        ring
  simp_rw [sourceFirstSum_eq_family]
  calc
    _ ≤ C*P^(2+ε/2)*(A.card : ℝ)^3 := hb
    _ ≤ C*P^(2+ε/2)*(H*M*R)^3 := by gcongr
    _ = C*P^(2+ε/2)*H^3*M^3*R^3 := by ring
    _ ≤ C*P^(2+ε/2)*H^3*M^3*P^(ε/2) := by gcongr
    _ = C*P^(2+ε)*M^3*H^3 := by
      have hp : P^(2+ε/2)*P^(ε/2)=P^(2+ε) := by
        rw [← Real.rpow_add hPpos]
        congr 1
        ring
      calc
        _ = C*(P^(2+ε/2)*P^(ε/2))*M^3*H^3 := by ring
        _ = _ := by rw [hp]

#print axioms family_first_fourth_bound
#print axioms source_even_first_fourth_moment
end Waring.SeedCompletionEvenFourth
