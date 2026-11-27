import Waring.SeedCompletionFirstWeyl
import Waring.SeedCompletionEvenSecondBox
import Waring.FirstDifferenceSource

/-! # Actual even-degree first auxiliary fourth moments

The ordinary positive-pair difference is enclosed in the literal Cartesian
second-phase domain. Its short coefficient range is the only additional
size condition, and is sufficient for the coefficient-uniform curve bound.
-/

noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionEvenFourth
open IntegerDifferencePolynomial SeedCompletionBackwardMoments SeedCompletionBackwardCount
open SeedCompletionFirstWeyl PolicyCompletionHolder UnseparatedDifferencing
open SeedCompletionNinthFourth (secondMoment_image)
open SeedCompletionNinthFourthBounds (centers centers_pos centers_width centers_card
  secondMoment_congr firstCode firstCode_injOn sum_natural_centers)
open FirstDifferenceSecond

theorem secondMoment_mono {ι : Type*} {A B : Finset ι} (hAB : A ⊆ B) (f : ι → ℤ) :
    secondMoment A f ≤ secondMoment B f := by
  classical
  rw [secondMoment_eq_count,secondMoment_eq_count]
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro p hp
  simp only [crossFrequencyPairs,Finset.mem_filter,Finset.mem_product] at hp ⊢
  exact ⟨⟨hAB hp.1.1,hAB hp.1.2⟩,hp.2⟩

theorem familyFirst_second_eq_image (k : ℕ) (B : Finset Label) (N : ℕ) :
    (∫ α in (0 : ℝ)..1, ‖familyFirstSum k B N α‖^2) =
      secondMoment ((B ×ˢ centers N).image firstCode)
        (fun p => (powerPolynomial k [((p.1 : ℤ),(p.2.1 : ℤ))]).eval (p.2.2 : ℤ)) := by
  rw [secondMoment_image _ _ (firstCode_injOn B N)]
  have heq := secondMoment_congr (B ×ˢ centers N)
    (fun p => (powerPolynomial k [(((firstCode p).1 : ℤ),((firstCode p).2.1 : ℤ))]).eval
      ((firstCode p).2.2 : ℤ))
    (fun p => firstPhase k p.1 p.2) (by
      intro p hp
      have hz := centers_pos (Finset.mem_product.mp hp).2
      simp only [firstCode,Int.toNat_of_nonneg (by omega : 0 ≤ p.2),firstPhase])
  rw [heq]
  simp only [secondMoment,Finset.sum_product,familyFirstSum,familySum]

theorem family_first_second_bound (d : ℕ) (hd : supportedHalfDegree d)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ P₀ : ℝ, 1 ≤ P₀ ∧ ∀ P : ℝ, P₀ ≤ P →
      ∀ (B : Finset Label) (N : ℕ), (N : ℝ) ≤ 2*P →
      (∀ b ∈ B,0 < b.1 ∧ 0 < b.2) →
      (∀ b ∈ B,(b.1 : ℝ) ≤ 2*P ∧ (b.2 : ℝ) ≤ 2*P) →
      (∫ α in (0 : ℝ)..1, ‖familyFirstSum (2*d) B N α‖^2) ≤
        C*P^ε*(B.card : ℝ)*N := by
  obtain ⟨C,hC,P₀,hP₀,hbound⟩ := actual_first_difference_second_scaled d hd
    2 (by norm_num) hε
  refine ⟨C,hC,P₀,hP₀,?_⟩
  intro P hPP₀ B N hN hpos hbox
  let A := (B ×ˢ centers N).image firstCode
  have hApos : ∀ x ∈ A,0 < x.1 ∧ 0 < x.2.1 ∧ 0 < x.2.2 := by
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

def secondHeights (H : Finset ℕ) (N : ℕ) : Finset (ℕ×ℕ) :=
  H.image (fun h => 2*h) ×ˢ Finset.Icc 1 N

theorem secondHeights_card (H : Finset ℕ) (N : ℕ) :
    (secondHeights H N).card=H.card*N := by
  rw [secondHeights,Finset.card_product,Finset.card_image_of_injective]
  · simp
  · intro a b he
    change 2*a=2*b at he
    omega

theorem differenceCode_subset (H B : Finset ℕ) (N : ℕ) :
    ((positiveDifferenceDomain (H ×ˢ B) (centers N)).image differenceCode) ⊆
      secondHeights H N ×ˢ (B ×ˢ Finset.Icc 1 (2*N)) := by
  intro x hx
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
  rcases Finset.mem_product.mp hp with ⟨hb,hpair⟩
  rcases Finset.mem_product.mp hb with ⟨hh,hm⟩
  rcases Finset.mem_filter.mp hpair with ⟨hpair,horder⟩
  rcases Finset.mem_product.mp hpair with ⟨hz,hw⟩
  have hz := Finset.mem_Icc.mp hz
  have hw := Finset.mem_Icc.mp hw
  apply Finset.mem_product.mpr
  constructor
  · apply Finset.mem_product.mpr
    exact ⟨Finset.mem_image_of_mem (fun h => 2*h) hh,
      Finset.mem_Icc.mpr ⟨by change 1 ≤ (p.2.1-p.2.2).toNat; omega,
        by change (p.2.1-p.2.2).toNat ≤ N; omega⟩⟩
  · exact Finset.mem_product.mpr ⟨hm,Finset.mem_Icc.mpr
      ⟨by change 1 ≤ (p.2.1+p.2.2).toNat; omega,
        by change (p.2.1+p.2.2).toNat ≤ 2*N; omega⟩⟩

/-- The full actual differenced energy, with a coefficient-cardinality cap. -/
theorem family_difference_second_bound (d : ℕ) (hd : supportedHalfDegree d)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ P₀ : ℝ, 1 ≤ P₀ ∧ ∀ P : ℝ, P₀ ≤ P →
      ∀ (H B : Finset ℕ) (N : ℕ),(N : ℝ) ≤ 2*P →
      (∀ h ∈ H,0 < h ∧ (h : ℝ) ≤ 2*P) →
      (∀ m ∈ B,0 < m ∧ (m : ℝ) ≤ 2*P) →
      (B.card : ℝ) ≤ P^(1/3 : ℝ) →
      (∫ α in (0 : ℝ)..1, ‖familyDifferenceSum (2*d) (H ×ˢ B) N α‖^2) ≤
        C*P^(2+ε)*(H.card : ℝ)*(B.card : ℝ) := by
  obtain ⟨C,hC,P₀,hP₀,hbound⟩ :=
    SeedCompletionEvenSecondCount.actual_even_second_on_box d hd hε
  refine ⟨2*C*(4 : ℝ)^(1+ε),by positivity,P₀,hP₀,?_⟩
  intro P hPP₀ H B N hN hH hB hBc
  have hP : 1 ≤ P := hP₀.trans hPP₀
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hPP : P₀ ≤ 4*P := hPP₀.trans (by linarith)
  have hheight : ∀ h ∈ secondHeights H N,
      0 < h.1 ∧ 0 < h.2 ∧ (h.1 : ℝ) ≤ 4*P ∧ (h.2 : ℝ) ≤ 4*P := by
    intro h hh
    rcases Finset.mem_product.mp hh with ⟨hh,ha⟩
    obtain ⟨u,hu,he⟩ := Finset.mem_image.mp hh
    have ha := Finset.mem_Icc.mp ha
    have hule := (hH u hu).2
    have hal : (h.2 : ℝ) ≤ 2*P := (Nat.cast_le.mpr ha.2).trans hN
    refine ⟨?_,ha.1,?_,by linarith⟩
    · have hu := (hH u hu).1
      omega
    · have he' : (h.1 : ℝ)=2*(u : ℝ) := by exact_mod_cast he.symm
      rw [he']
      linarith
  have hcoeff : ∀ m ∈ B,0 < m ∧ (m : ℝ) ≤ 4*P :=
    fun m hm => ⟨(hB m hm).1,(hB m hm).2.trans (by linarith)⟩
  have hcenters : ∀ z ∈ Finset.Icc 1 (2*N),0 < z ∧ (z : ℝ) ≤ 4*P := by
    intro z hz
    have hz := Finset.mem_Icc.mp hz
    refine ⟨hz.1,?_⟩
    have hl : (z : ℝ) ≤ 2*(N : ℝ) := by exact_mod_cast hz.2
    linarith
  have hBc' : (B.card : ℝ) ≤ (4*P)^(1/3 : ℝ) :=
    hBc.trans (Real.rpow_le_rpow hPpos.le (by linarith) (by norm_num))
  have hZc : ((Finset.Icc 1 (2*N)).card : ℝ) ≤ 4*P := by
    simp only [Nat.card_Icc,Nat.add_sub_cancel,Nat.cast_mul,Nat.cast_ofNat]
    linarith
  have hb := hbound (4*P) hPP (secondHeights H N) B (Finset.Icc 1 (2*N))
    hheight hcoeff hcenters hBc' hZc
  change secondMoment (secondHeights H N ×ˢ (B ×ˢ Finset.Icc 1 (2*N)))
    (secondPhase (2*d)) ≤ _ at hb
  rw [familyDifference_second_eq,positive_difference_second_eq (2*d) (H ×ˢ B) (centers N)
    (fun b hb => (hB b.2 (Finset.mem_product.mp hb).2).1)
    (fun z hz => centers_pos hz)]
  calc
    _ ≤ secondMoment (secondHeights H N ×ˢ (B ×ˢ Finset.Icc 1 (2*N)))
        (secondPhase (2*d)) := secondMoment_mono (differenceCode_subset H B N) _
    _ ≤ C*(4*P)^(1+ε)*((secondHeights H N).card : ℝ)*(B.card : ℝ) := hb
    _ = C*(4 : ℝ)^(1+ε)*P^(1+ε)*(H.card : ℝ)*(B.card : ℝ)*N := by
      rw [secondHeights_card,Nat.cast_mul,Real.mul_rpow (by norm_num) hPpos.le]
      ring
    _ ≤ C*(4 : ℝ)^(1+ε)*P^(1+ε)*(H.card : ℝ)*(B.card : ℝ)*(2*P) := by gcongr
    _ = _ := by
      have hp : P^(1+ε)*P=P^(2+ε) := by
        calc
          _ = P^(1+ε)*P^(1 : ℝ) := by rw [Real.rpow_one]
          _ = _ := by rw [← Real.rpow_add hPpos]; congr 1; ring
      calc
        _ = (2*C*(4 : ℝ)^(1+ε))*(P^(1+ε)*P)*(H.card : ℝ)*(B.card : ℝ) := by ring
        _ = _ := by rw [hp]

#print axioms family_difference_second_bound
end Waring.SeedCompletionEvenFourth
