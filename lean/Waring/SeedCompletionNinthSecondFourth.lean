import Waring.SeedCompletionNinthSecondWeyl

/-! # Genuine degree-nine j=2 auxiliary fourth moment

Both coefficient blocks vary. The new ordinary-difference phase has a
fixed last coefficient one, and its proved even-curve energy completes
the Weyl step without an auxiliary moment assumption.
-/

noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionNinthSecondWeyl
open IntegerDifferencePolynomial SeedCompletionBackwardMoments
open PolicyCompletionHolder UnseparatedDifferencing
open SeedCompletionNinthDouble (Pair)
open SeedCompletionNinthTriple (Heights)
open SeedCompletionNinthFourthBounds (centers centers_pos centers_width centers_card)

theorem family_second_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∃ P₀ : ℝ,1 ≤ P₀ ∧ ∀ P : ℝ,P₀ ≤ P →
      ∀ (H B : Finset Pair) (N : ℕ),(N : ℝ) ≤ 4*P →
      (∀ h ∈ H,0 < h.1 ∧ 0 < h.2 ∧ (h.1 : ℝ) ≤ 4*P ∧ (h.2 : ℝ) ≤ 4*P) →
      (∀ m ∈ B,0 < m.1 ∧ 0 < m.2 ∧ (m.1 : ℝ) ≤ 4*P ∧ (m.2 : ℝ) ≤ 4*P) →
      (B.card : ℝ) ≤ P^(1/3 : ℝ) →
      (∫ α in (0 : ℝ)..1,‖familySum (H ×ˢ B) N α‖^2) ≤
        C*P^(1+ε)*(H.card : ℝ)*(B.card : ℝ) := by
  obtain ⟨C,hC,P₀,hP₀,hbound⟩ := SeedCompletionNinthDoubleBox.actual_second_diagonal_size
    4 (by norm_num) hε
  refine ⟨C,hC,P₀,hP₀,?_⟩
  intro P hPP H B N hN hH hB hBc
  have hP : 1 ≤ P := hP₀.trans hPP
  have hBc' : (B.card : ℝ) ≤ P := hBc.trans (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hP
      (show (1/3 : ℝ) ≤ 1 by norm_num))
  have hZp : ∀ z ∈ Finset.Icc 1 N,0 < z := fun z hz => (Finset.mem_Icc.mp hz).1
  have hZb : ∀ z ∈ Finset.Icc 1 N,(z : ℝ) ≤ 4*P :=
    fun z hz => (Nat.cast_le.mpr (Finset.mem_Icc.mp hz).2).trans hN
  have hZc : ((Finset.Icc 1 N).card : ℝ) ≤ 4*P := by simpa using hN
  simp_rw [familySum_eq_actualSum]
  exact hbound P hPP H B (Finset.Icc 1 N)
    (fun h hh => ⟨(hH h hh).1,(hH h hh).2.1⟩)
    (fun m hm => ⟨(hB m hm).1,(hB m hm).2.1⟩) hZp
    (fun h hh => (hH h hh).2.2) (fun m hm => (hB m hm).2.2) hZb hBc' hZc

def doublePair (h : Pair) : Pair := (2*h.1,2*h.2)
def thirdHeights (H : Finset Pair) (N : ℕ) : Finset Heights :=
  H.image doublePair ×ˢ Finset.Icc 1 N

theorem doublePair_injective : Function.Injective doublePair := by
  intro a b he
  have h1 : 2*a.1=2*b.1 := congrArg Prod.fst he
  have h2 : 2*a.2=2*b.2 := congrArg Prod.snd he
  exact Prod.ext (by omega) (by omega)

theorem thirdHeights_card (H : Finset Pair) (N : ℕ) : (thirdHeights H N).card=H.card*N := by
  rw [thirdHeights,Finset.card_product,Finset.card_image_of_injective _ doublePair_injective]
  simp

theorem differenceCode_subset (H B : Finset Pair) (N : ℕ) :
    ((positiveDifferenceDomain (H ×ˢ B) (centers N)).image differenceCode) ⊆
      thirdHeights H N ×ˢ (B ×ˢ Finset.Icc 1 (2*N)) := by
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
    exact ⟨Finset.mem_image_of_mem doublePair hh,
      Finset.mem_Icc.mpr ⟨by change 1 ≤ (p.2.1-p.2.2).toNat; omega,
        by change (p.2.1-p.2.2).toNat ≤ N; omega⟩⟩
  · exact Finset.mem_product.mpr ⟨hm,Finset.mem_Icc.mpr
      ⟨by change 1 ≤ (p.2.1+p.2.2).toNat; omega,
        by change (p.2.1+p.2.2).toNat ≤ 2*N; omega⟩⟩

theorem family_difference_second_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∃ P₀ : ℝ,1 ≤ P₀ ∧ ∀ P : ℝ,P₀ ≤ P →
      ∀ (H B : Finset Pair) (N : ℕ),(N : ℝ) ≤ 4*P →
      (∀ h ∈ H,0 < h.1 ∧ 0 < h.2 ∧ (h.1 : ℝ) ≤ 4*P ∧ (h.2 : ℝ) ≤ 4*P) →
      (∀ m ∈ B,0 < m.1 ∧ 0 < m.2 ∧ (m.1 : ℝ) ≤ 4*P ∧ (m.2 : ℝ) ≤ 4*P) →
      (B.card : ℝ) ≤ P^(1/3 : ℝ) →
      (∫ α in (0 : ℝ)..1,‖differenceSum (H ×ˢ B) N α‖^2) ≤
        C*P^(2+ε)*(H.card : ℝ)*(B.card : ℝ) := by
  obtain ⟨C,hC,P₀,hP₀,hbound⟩ := SeedCompletionNinthTripleBox.actual_second_on_box hε
  refine ⟨4*C*(8 : ℝ)^(1+ε),by positivity,P₀,hP₀,?_⟩
  intro P hPP H B N hN hH hB hBc
  have hP : 1 ≤ P := hP₀.trans hPP
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hPP' : P₀ ≤ 8*P := hPP.trans (by linarith)
  have hHp : ∀ h ∈ thirdHeights H N,0 < h.1.1 ∧ 0 < h.1.2 ∧ 0 < h.2 := by
    intro h hh
    rcases Finset.mem_product.mp hh with ⟨hh,ha⟩
    obtain ⟨u,hu,he⟩ := Finset.mem_image.mp hh
    have hu := hH u hu
    have ha := (Finset.mem_Icc.mp ha).1
    have he1 : 2*u.1=h.1.1 := congrArg Prod.fst he
    have he2 : 2*u.2=h.1.2 := congrArg Prod.snd he
    exact ⟨by omega,by omega,ha⟩
  have hHb : ∀ h ∈ thirdHeights H N,
      (h.1.1 : ℝ) ≤ 8*P ∧ (h.1.2 : ℝ) ≤ 8*P ∧ (h.2 : ℝ) ≤ 8*P := by
    intro h hh
    rcases Finset.mem_product.mp hh with ⟨hh,ha⟩
    obtain ⟨u,hu,he⟩ := Finset.mem_image.mp hh
    have hu := hH u hu
    have ha : (h.2 : ℝ) ≤ 4*P := (Nat.cast_le.mpr (Finset.mem_Icc.mp ha).2).trans hN
    have he1 : (h.1.1 : ℝ)=2*(u.1 : ℝ) := by exact_mod_cast (congrArg Prod.fst he).symm
    have he2 : (h.1.2 : ℝ)=2*(u.2 : ℝ) := by exact_mod_cast (congrArg Prod.snd he).symm
    exact ⟨by linarith [hu.2.2.1],by linarith [hu.2.2.2],by linarith⟩
  have hBp : ∀ m ∈ B,0 < m.1 ∧ 0 < m.2 := fun m hm => ⟨(hB m hm).1,(hB m hm).2.1⟩
  have hBb : ∀ m ∈ B,(m.1 : ℝ) ≤ 8*P ∧ (m.2 : ℝ) ≤ 8*P := by
    intro m hm
    exact ⟨(hB m hm).2.2.1.trans (by linarith),(hB m hm).2.2.2.trans (by linarith)⟩
  have hZp : ∀ z ∈ Finset.Icc 1 (2*N),0 < z := fun z hz => (Finset.mem_Icc.mp hz).1
  have hZb : ∀ z ∈ Finset.Icc 1 (2*N),(z : ℝ) ≤ 8*P := by
    intro z hz
    have hz : (z : ℝ) ≤ 2*(N : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hz).2
    linarith
  have hBc' : (B.card : ℝ) ≤ (8*P)^(1/3 : ℝ) :=
    hBc.trans (Real.rpow_le_rpow hPpos.le (by linarith) (by norm_num))
  have hZc : ((Finset.Icc 1 (2*N)).card : ℝ) ≤ 8*P := by
    simp only [Nat.card_Icc,Nat.add_sub_cancel,Nat.cast_mul,Nat.cast_ofNat]
    linarith
  have hb := hbound (8*P) hPP' (thirdHeights H N) B (Finset.Icc 1 (2*N))
    hHp hBp hZp hHb hBb hZb hBc' hZc
  change secondMoment (thirdHeights H N ×ˢ (B ×ˢ Finset.Icc 1 (2*N))) thirdPhase ≤ _ at hb
  rw [difference_second_eq,positive_difference_second_eq (H ×ˢ B) (centers N)
    (fun b hb => hBp b.2 (Finset.mem_product.mp hb).2) (fun z hz => centers_pos hz)]
  calc
    _ ≤ secondMoment (thirdHeights H N ×ˢ (B ×ˢ Finset.Icc 1 (2*N))) thirdPhase :=
      SeedCompletionEvenFourth.secondMoment_mono (differenceCode_subset H B N) _
    _ ≤ C*(8*P)^(1+ε)*((thirdHeights H N).card : ℝ)*(B.card : ℝ) := hb
    _ = C*(8 : ℝ)^(1+ε)*P^(1+ε)*(H.card : ℝ)*(B.card : ℝ)*N := by
      rw [thirdHeights_card,Nat.cast_mul,Real.mul_rpow (by norm_num) hPpos.le]
      ring
    _ ≤ C*(8 : ℝ)^(1+ε)*P^(1+ε)*(H.card : ℝ)*(B.card : ℝ)*(4*P) := by gcongr
    _ = _ := by
      have hp : P^(1+ε)*P=P^(2+ε) := by
        calc
          _ = P^(1+ε)*P^(1 : ℝ) := by rw [Real.rpow_one]
          _ = _ := by rw [← Real.rpow_add hPpos]; congr 1; ring
      calc
        _ = (4*C*(8 : ℝ)^(1+ε))*(P^(1+ε)*P)*(H.card : ℝ)*(B.card : ℝ) := by ring
        _ = _ := by rw [hp]

/-- The genuine full F2 fourth moment on source-sized Cartesian boxes. -/
theorem family_fourth_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∃ P₀ : ℝ,1 ≤ P₀ ∧ ∀ P : ℝ,P₀ ≤ P →
      ∀ (H B : Finset Pair) (N : ℕ),(N : ℝ) ≤ 4*P →
      (∀ h ∈ H,0 < h.1 ∧ 0 < h.2 ∧ (h.1 : ℝ) ≤ 4*P ∧ (h.2 : ℝ) ≤ 4*P) →
      (∀ m ∈ B,0 < m.1 ∧ 0 < m.2 ∧ (m.1 : ℝ) ≤ 4*P ∧ (m.2 : ℝ) ≤ 4*P) →
      (B.card : ℝ) ≤ P^(1/3 : ℝ) →
      (∫ α in (0 : ℝ)..1,‖familySum (H ×ˢ B) N α‖^4) ≤
        C*P^(2+ε)*((H ×ˢ B).card : ℝ)^3 := by
  obtain ⟨C1,hC1,P1,hP1,hfirst⟩ := family_second_bound hε
  obtain ⟨C2,hC2,P2,hP2,hdiff⟩ := family_difference_second_bound hε
  refine ⟨8*C1+4*C2,by positivity,max P1 P2,hP1.trans (le_max_left _ _),?_⟩
  intro P hPP H B N hN hH hB hBc
  have hP : 1 ≤ P := hP1.trans ((le_max_left _ _).trans hPP)
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  let A := H ×ˢ B
  have H1 := hfirst P ((le_max_left _ _).trans hPP) H B N hN hH hB hBc
  have H2 := hdiff P ((le_max_right _ _).trans hPP) H B N hN hH hB hBc
  have H1' : (∫ α in (0 : ℝ)..1,‖familySum A N α‖^2) ≤ C1*P^(1+ε)*(A.card : ℝ) :=
    H1.trans_eq (by simp only [A,Finset.card_product,Nat.cast_mul]; ring)
  have H2' : (∫ α in (0 : ℝ)..1,‖differenceSum A N α‖^2) ≤ C2*P^(2+ε)*(A.card : ℝ) :=
    H2.trans_eq (by simp only [A,Finset.card_product,Nat.cast_mul]; ring)
  have HF := PolicyCompletionFourthMoment.fourier_family_fourth_moment_bound A
    (fun _ => centers N) firstPhase N (fun b hb => (centers_card N).le)
    (fun b hb => centers_width N)
  change (∫ α in (0 : ℝ)..1,‖familySum A N α‖^4) ≤
    2*(N : ℝ)*(A.card : ℝ)^2*(∫ α in (0 : ℝ)..1,‖familySum A N α‖^2)+
    4*(A.card : ℝ)^2*(∫ α in (0 : ℝ)..1,‖differenceSum A N α‖^2) at HF
  calc
    _ ≤ _ := HF
    _ ≤ 2*(N : ℝ)*(A.card : ℝ)^2*(C1*P^(1+ε)*(A.card : ℝ))+
        4*(A.card : ℝ)^2*(C2*P^(2+ε)*(A.card : ℝ)) :=
      add_le_add (mul_le_mul_of_nonneg_left H1' (by positivity))
        (mul_le_mul_of_nonneg_left H2' (by positivity))
    _ ≤ 2*(4*P)*(A.card : ℝ)^2*(C1*P^(1+ε)*(A.card : ℝ))+
        4*(A.card : ℝ)^2*(C2*P^(2+ε)*(A.card : ℝ)) := by gcongr
    _ = _ := by
      rw [Real.rpow_add hPpos,Real.rpow_add hPpos,Real.rpow_one,Real.rpow_two]
      ring

#print axioms family_difference_second_bound
#print axioms family_fourth_bound
end Waring.SeedCompletionNinthSecondWeyl
