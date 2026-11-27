import Waring.SeedCompletionNinthFourth

/-!
# The sharp degree-nine first auxiliary fourth moment

Both second moments in the actual Weyl step are supplied by the proved
number-theoretic fiber bounds. The final estimate has the source powers
P^(2+epsilon) (#height/coefficient labels)^3.
-/

noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionNinthFourthBounds
open SeedCompletionNinthFourth IntegerDifferencePolynomial SeedCompletionBackwardMoments
open PolicyCompletionHolder UnseparatedDifferencing

def centers (N : ℕ) : Finset ℤ := Finset.Icc 1 (N : ℤ)

def familyFirstSum (B : Finset Label) (N : ℕ) (α : ℝ) : ℂ :=
  familySum B (fun _ => centers N)
    (fun b z => fourier (firstPhase b z) (α : AddCircle (1 : ℝ)))

def familyDifferenceSum (B : Finset Label) (N : ℕ) (α : ℝ) : ℂ :=
  firstDifference B (fun _ => centers N)
    (fun b z => fourier (firstPhase b z) (α : AddCircle (1 : ℝ))) N

theorem centers_pos {N : ℕ} {z : ℤ} (hz : z ∈ centers N) : 1 ≤ z :=
  (Finset.mem_Icc.mp hz).1

theorem centers_width (N : ℕ) : ∀ z ∈ centers N, ∀ w ∈ centers N, z-w ≤ (N : ℤ) := by
  intro z hz w hw
  have hz := Finset.mem_Icc.mp hz
  have hw := Finset.mem_Icc.mp hw
  omega

@[simp] theorem centers_card (N : ℕ) : (centers N).card=N := by
  simp [centers,Int.card_Icc]

theorem secondMoment_congr {ι : Type*} (A : Finset ι) (f g : ι → ℤ)
    (hfg : ∀ x ∈ A, f x=g x) : secondMoment A f=secondMoment A g := by
  unfold secondMoment
  congr 1
  funext α
  have hs : (∑ x ∈ A, fourier (f x) (α : AddCircle (1 : ℝ))) =
      ∑ x ∈ A, fourier (g x) (α : AddCircle (1 : ℝ)) := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [hfg x hx]
  rw [hs]

def firstCode (p : Label × ℤ) : SeedCompletionNinthFirst.Index :=
  (p.1.1,p.1.2,p.2.toNat)

theorem firstCode_injOn (B : Finset Label) (N : ℕ) :
    Set.InjOn firstCode ((B ×ˢ centers N : Finset (Label × ℤ)) : Set (Label × ℤ)) := by
  intro x hx y hy heq
  have hxz := centers_pos (Finset.mem_product.mp hx).2
  have hyz := centers_pos (Finset.mem_product.mp hy).2
  have hh : x.1.1=y.1.1 := congrArg (fun p : SeedCompletionNinthFirst.Index => p.1) heq
  have hm : x.1.2=y.1.2 := congrArg (fun p : SeedCompletionNinthFirst.Index => p.2.1) heq
  have hz : x.2.toNat=y.2.toNat := congrArg (fun p : SeedCompletionNinthFirst.Index => p.2.2) heq
  exact Prod.ext (Prod.ext hh hm) (by omega)

theorem familyFirst_second_eq_image (B : Finset Label) (N : ℕ) :
    (∫ α in (0 : ℝ)..1, ‖familyFirstSum B N α‖^2) =
      secondMoment ((B ×ˢ centers N).image firstCode)
        (fun p => (powerPolynomial 9 [((p.1 : ℤ),(p.2.1 : ℤ))]).eval (p.2.2 : ℤ)) := by
  rw [secondMoment_image _ _ (firstCode_injOn B N)]
  have heq := secondMoment_congr (B ×ˢ centers N)
    (fun p => (powerPolynomial 9 [(((firstCode p).1 : ℤ),((firstCode p).2.1 : ℤ))]).eval
      ((firstCode p).2.2 : ℤ))
    (fun p => firstPhase p.1 p.2) (by
      intro p hp
      have hz := centers_pos (Finset.mem_product.mp hp).2
      simp only [firstCode,Int.toNat_of_nonneg (by omega : 0 ≤ p.2),firstPhase])
  rw [heq]
  simp only [secondMoment,Finset.sum_product,familyFirstSum,familySum]

theorem familyDifference_second_eq (B : Finset Label) (N : ℕ) :
    (∫ α in (0 : ℝ)..1, ‖familyDifferenceSum B N α‖^2) =
      secondMoment (positiveDifferenceDomain B (centers N)) positiveDifferencePhase := by
  unfold familyDifferenceSum
  simp_rw [firstDifference_eq_frequencySum B (centers N) N (centers_width N)]
  rfl

theorem positiveDifferenceDomain_card_le (B : Finset Label) (N : ℕ) :
    (positiveDifferenceDomain B (centers N)).card ≤ B.card*N^2 := by
  rw [positiveDifferenceDomain,Finset.card_product]
  apply Nat.mul_le_mul_left
  calc
    (positivePairs (centers N)).card ≤ (centers N ×ˢ centers N).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = N^2 := by simp [pow_two]

/-- The actual first sum on a Cartesian label/center domain. -/
theorem family_first_second_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ P₀ : ℝ, 1 ≤ P₀ ∧ ∀ P : ℝ, P₀ ≤ P →
      ∀ (B : Finset Label) (N : ℕ), (N : ℝ) ≤ 2*P →
      (∀ b ∈ B, 0 < b.1 ∧ 0 < b.2) →
      (∀ b ∈ B, (b.1 : ℝ) ≤ 2*P ∧ (b.2 : ℝ) ≤ 2*P) →
      (∫ α in (0 : ℝ)..1, ‖familyFirstSum B N α‖^2) ≤
        C*P^ε*(B.card : ℝ)*N := by
  obtain ⟨C,hC,P₀,hP₀,hbound⟩ := SeedCompletionNinthFirst.actual_ninth_first_second_scaled
    2 (by norm_num) hε
  refine ⟨C,hC,P₀,hP₀,?_⟩
  intro P hPP₀ B N hN hpos hbox
  let A := (B ×ˢ centers N).image firstCode
  have hApos : ∀ x ∈ A, 0 < x.1 ∧ 0 < x.2.1 ∧ 0 < x.2.2 := by
    intro x hx
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
    have hb := hpos p.1 (Finset.mem_product.mp hp).1
    have hz := centers_pos (Finset.mem_product.mp hp).2
    exact ⟨hb.1,hb.2,by change 0 < p.2.toNat; omega⟩
  have hAbox : ∀ x ∈ A,
      (x.1 : ℝ) ≤ 2*P ∧ (x.2.1 : ℝ) ≤ 2*P ∧ (x.2.2 : ℝ) ≤ 2*P := by
    intro x hx
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
    have hb := hbox p.1 (Finset.mem_product.mp hp).1
    have hz := Finset.mem_Icc.mp (Finset.mem_product.mp hp).2
    refine ⟨hb.1,hb.2,?_⟩
    have hzn : p.2.toNat ≤ N := by omega
    exact (Nat.cast_le.mpr hzn).trans hN
  rw [familyFirst_second_eq_image]
  have hb := hbound P hPP₀ A hApos hAbox
  have hc : A.card=B.card*N := by
    rw [Finset.card_image_of_injOn (firstCode_injOn B N),Finset.card_product,centers_card]
  change secondMoment A _ ≤ _ at hb
  rw [hc,Nat.cast_mul] at hb
  exact hb.trans_eq (by ring)

/-- The actual differenced sum uses the genuine degree-nine second phase. -/
theorem family_difference_second_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ P₀ : ℝ, 1 ≤ P₀ ∧ ∀ P : ℝ, P₀ ≤ P →
      ∀ (B : Finset Label) (N : ℕ), (N : ℝ) ≤ 2*P →
      (∀ b ∈ B, 0 < b.1 ∧ 0 < b.2) →
      (∀ b ∈ B, (b.1 : ℝ) ≤ 2*P ∧ (b.2 : ℝ) ≤ 2*P) →
      (∫ α in (0 : ℝ)..1, ‖familyDifferenceSum B N α‖^2) ≤
        C*P^ε*(B.card : ℝ)*(N : ℝ)^2 := by
  obtain ⟨C,hC,P₀,hP₀,hbound⟩ := SeedCompletionNinthSecond.actual_second_difference_second_on_box hε
  refine ⟨C*(4 : ℝ)^ε,by positivity,P₀,hP₀,?_⟩
  intro P hPP₀ B N hN hpos hbox
  have hP : 1 ≤ P := hP₀.trans hPP₀
  have hP0 : 0 ≤ P := zero_le_one.trans hP
  have hPP : P₀ ≤ 4*P := hPP₀.trans (by linarith)
  let D := positiveDifferenceDomain B (centers N)
  let A := D.image differenceCode
  have hApos : ∀ x ∈ A, 0 < x.1 ∧ 0 < x.2.1 ∧ 0 < x.2.2.1 ∧ 0 < x.2.2.2 := by
    intro x hx
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
    have hb := hpos p.1 (Finset.mem_product.mp hp).1
    have hpz := Finset.mem_filter.mp (Finset.mem_product.mp hp).2
    have hz := centers_pos (Finset.mem_product.mp hpz.1).1
    have hz' := centers_pos (Finset.mem_product.mp hpz.1).2
    exact ⟨by change 0 < 2*p.1.1; omega,hb.2,
      by change 0 < (p.2.1-p.2.2).toNat; omega,
      by change 0 < (p.2.1+p.2.2).toNat; omega⟩
  have hAbox : ∀ x ∈ A, (x.1 : ℝ) ≤ 4*P ∧ (x.2.1 : ℝ) ≤ 4*P ∧
      (x.2.2.1 : ℝ) ≤ 4*P ∧ (x.2.2.2 : ℝ) ≤ 4*P := by
    intro x hx
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
    have hb := hbox p.1 (Finset.mem_product.mp hp).1
    have hpz := Finset.mem_filter.mp (Finset.mem_product.mp hp).2
    have hz := Finset.mem_Icc.mp (Finset.mem_product.mp hpz.1).1
    have hz' := Finset.mem_Icc.mp (Finset.mem_product.mp hpz.1).2
    have hdN : (p.2.1-p.2.2).toNat ≤ N := by omega
    have hsN : (p.2.1+p.2.2).toNat ≤ 2*N := by omega
    refine ⟨?_,by change (p.1.2 : ℝ) ≤ 4*P; linarith [hb.2],?_,?_⟩
    · change ((2*p.1.1 : ℕ) : ℝ) ≤ 4*P
      push_cast
      linarith [hb.1]
    · exact (Nat.cast_le.mpr hdN).trans (by linarith)
    · have hs : ((p.2.1+p.2.2).toNat : ℝ) ≤ 2*(N : ℝ) := by exact_mod_cast hsN
      exact hs.trans (by linarith)
  have hb := hbound (4*P) hPP A hApos hAbox
  change secondMoment A _ ≤ _ at hb
  have hcard : A.card=D.card := Finset.card_image_of_injOn
    (differenceCode_injOn B (centers N) (fun z hz => centers_pos hz))
  rw [hcard] at hb
  rw [familyDifference_second_eq,positive_difference_second_eq B (centers N)
    (fun b hb => (hpos b hb).2) (fun z hz => centers_pos hz)]
  calc
    _ ≤ C*(4*P)^ε*(D.card : ℝ) := hb
    _ ≤ C*(4*P)^ε*((B.card : ℝ)*(N : ℝ)^2) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast positiveDifferenceDomain_card_le B N)
        (by positivity)
    _ = _ := by rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hP0]; ring

/-- The sharp fourth moment with all arithmetic inputs proved. -/
theorem family_first_fourth_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ P₀ : ℝ, 1 ≤ P₀ ∧ ∀ P : ℝ, P₀ ≤ P →
      ∀ (B : Finset Label) (N : ℕ), (N : ℝ) ≤ 2*P →
      (∀ b ∈ B, 0 < b.1 ∧ 0 < b.2) →
      (∀ b ∈ B, (b.1 : ℝ) ≤ 2*P ∧ (b.2 : ℝ) ≤ 2*P) →
      (∫ α in (0 : ℝ)..1, ‖familyFirstSum B N α‖^4) ≤
        C*P^(2+ε)*(B.card : ℝ)^3 := by
  obtain ⟨C1,hC1,P1,hP1,hfirst⟩ := family_first_second_bound hε
  obtain ⟨C2,hC2,P2,hP2,hdiff⟩ := family_difference_second_bound hε
  refine ⟨4*(2*C1+4*C2),by positivity,max P1 P2,hP1.trans (le_max_left _ _),?_⟩
  intro P hPP B N hN hpos hbox
  have hP : 1 ≤ P := hP1.trans ((le_max_left _ _).trans hPP)
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have H1 := hfirst P ((le_max_left _ _).trans hPP) B N hN hpos hbox
  have H2 := hdiff P ((le_max_right _ _).trans hPP) B N hN hpos hbox
  have H := PolicyCompletionFourthMoment.fourier_family_fourth_moment_bound B
    (fun _ => centers N) firstPhase N (fun b hb => (centers_card N).le)
    (fun b hb => centers_width N)
  change (∫ α in (0 : ℝ)..1, ‖familyFirstSum B N α‖^4) ≤
    2*(N : ℝ)*(B.card : ℝ)^2*(∫ α in (0 : ℝ)..1, ‖familyFirstSum B N α‖^2)+
    4*(B.card : ℝ)^2*(∫ α in (0 : ℝ)..1, ‖familyDifferenceSum B N α‖^2) at H
  calc
    _ ≤ _ := H
    _ ≤ 2*(N : ℝ)*(B.card : ℝ)^2*(C1*P^ε*(B.card : ℝ)*N)+
        4*(B.card : ℝ)^2*(C2*P^ε*(B.card : ℝ)*(N : ℝ)^2) :=
      add_le_add (mul_le_mul_of_nonneg_left H1 (by positivity))
        (mul_le_mul_of_nonneg_left H2 (by positivity))
    _ = (2*C1+4*C2)*P^ε*(N : ℝ)^2*(B.card : ℝ)^3 := by ring
    _ ≤ (2*C1+4*C2)*P^ε*(2*P)^2*(B.card : ℝ)^3 := by gcongr
    _ = _ := by
      rw [Real.rpow_add hPpos,Real.rpow_two]
      ring

/-- Natural and integer positive center intervals have exactly the same sum. -/
theorem sum_natural_centers (N : ℕ) (f : ℤ → ℂ) :
    (∑ z ∈ Finset.Icc 1 N, f (z : ℤ)) = ∑ z ∈ centers N, f z := by
  apply Finset.sum_bij (fun (z : ℕ) (hz : z ∈ Finset.Icc 1 N) => (z : ℤ))
  · intro z hz
    exact Finset.mem_Icc.mpr ⟨by exact_mod_cast (Finset.mem_Icc.mp hz).1,
      by exact_mod_cast (Finset.mem_Icc.mp hz).2⟩
  · intro x hx y hy heq
    exact_mod_cast heq
  · intro z hz
    have hz := Finset.mem_Icc.mp hz
    refine ⟨z.toNat,Finset.mem_Icc.mpr ⟨by omega,by omega⟩,?_⟩
    exact Int.toNat_of_nonneg (by omega)
  · intro z hz
    rfl

open CoefficientPower SmoothMoments FirstDifferenceSecond SeedCompletionNinthFirst

/-- The Cartesian family is exactly the source sum, without enlargement. -/
theorem sourceNinthFirstSum_eq_family (P H Q R M α : ℝ) :
    sourceNinthFirstSum P H Q R M α =
      familyFirstSum (Finset.Icc 1 ⌊H⌋₊ ×ˢ coefficientBlock Q R M) ⌊2*P⌋₊ α := by
  unfold sourceNinthFirstSum sourceFirstDomain familyFirstSum familySum firstPhase
  simp only [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro m hm
  exact sum_natural_centers ⌊2*P⌋₊
    (fun z => fourier ((powerPolynomial 9 [((h : ℤ),(m : ℤ))]).eval z)
      (α : AddCircle (1 : ℝ)))

/-- The literal source fourth moment in degree nine. Both auxiliary
second-moment inputs and their exact positive-pair transport are proved. -/
theorem source_ninth_first_fourth_moment {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ P₀ : ℝ, 1 ≤ P₀ ∧ ∀ P : ℝ, P₀ ≤ P →
      ∀ H Q R M : ℝ, 1 ≤ H → H ≤ 2*P → 1 ≤ M → 1 ≤ R →
      M*R ≤ 2*P → R ≤ P^(ε/6) →
      (∫ α in (0 : ℝ)..1, ‖sourceNinthFirstSum P H Q R M α‖^4) ≤
        C*P^(2+ε)*M^3*H^3 := by
  obtain ⟨C,hC,P₀,hP₀,hbound⟩ := family_first_fourth_bound (show 0 < ε/2 by positivity)
  refine ⟨C,hC,P₀,hP₀,?_⟩
  intro P hPP₀ H Q R M hH hHP hM hR hMR hRP
  have hP : 1 ≤ P := hP₀.trans hPP₀
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  let B := Finset.Icc 1 ⌊H⌋₊ ×ˢ coefficientBlock Q R M
  have hpos : ∀ b ∈ B, 0 < b.1 ∧ 0 < b.2 := by
    intro b hb
    have hb := Finset.mem_product.mp hb
    exact ⟨(Finset.mem_Icc.mp hb.1).1,
      (mem_smoothNumbers.mp (Finset.mem_filter.mp hb.2).1).1.1⟩
  have hbox : ∀ b ∈ B, (b.1 : ℝ) ≤ 2*P ∧ (b.2 : ℝ) ≤ 2*P := by
    intro b hb
    have hb := Finset.mem_product.mp hb
    exact ⟨((Nat.cast_le.mpr (Finset.mem_Icc.mp hb.1).2).trans (Nat.floor_le hH0)).trans hHP,
      ((Finset.mem_filter.mp hb.2).2.2).trans hMR⟩
  have hc : ((coefficientBlock Q R M).card : ℝ) ≤ M*R := by
    calc
      _ ≤ ((smoothNumbers (M*R) R).card : ℝ) := by
        exact_mod_cast Finset.card_le_card (coefficientBlock_subset Q R M)
      _ ≤ (⌊M*R⌋₊ : ℝ) := by exact_mod_cast smoothNumbers_card_le (M*R) R
      _ ≤ M*R := Nat.floor_le (mul_nonneg hM0 hR0)
  have hBcard : (B.card : ℝ) ≤ H*M*R := by
    simp only [B,Finset.card_product,Nat.card_Icc,Nat.add_sub_cancel,Nat.cast_mul]
    exact (mul_le_mul (Nat.floor_le hH0) hc (Nat.cast_nonneg _) hH0).trans_eq (by ring)
  have hb := hbound P hPP₀ B ⌊2*P⌋₊ (Nat.floor_le (by positivity)) hpos hbox
  have hRpow : R^3 ≤ P^(ε/2) := by
    calc
      _ ≤ (P^(ε/6))^3 := pow_le_pow_left₀ hR0 hRP 3
      _ = P^(ε/2) := by
        rw [← Real.rpow_mul_natCast hPpos.le]
        congr 1
        norm_num
        ring
  simp_rw [sourceNinthFirstSum_eq_family]
  calc
    _ ≤ C*P^(2+ε/2)*(B.card : ℝ)^3 := hb
    _ ≤ C*P^(2+ε/2)*(H*M*R)^3 := by gcongr
    _ = C*P^(2+ε/2)*H^3*M^3*R^3 := by ring
    _ ≤ C*P^(2+ε/2)*H^3*M^3*P^(ε/2) := by gcongr
    _ = C*P^(2+ε)*M^3*H^3 := by
      have hpow : P^(2+ε/2)*P^(ε/2)=P^(2+ε) := by
        rw [← Real.rpow_add hPpos]
        congr 1
        ring
      calc
        _ = C*(P^(2+ε/2)*P^(ε/2))*M^3*H^3 := by ring
        _ = _ := by rw [hpow]

#print axioms source_ninth_first_fourth_moment
#print axioms family_difference_second_bound
#print axioms family_first_fourth_bound
end Waring.SeedCompletionNinthFourthBounds
