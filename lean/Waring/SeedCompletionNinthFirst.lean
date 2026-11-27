import Waring.SeedCompletionQuadraticRepresentations
import Waring.FirstDifferenceSource

/-!
# The actual degree-nine first-difference second moment

The degree-nine phase has the factor (h*m^9)^2+3*z^2. The complete positive
quadratic representation bound controls its remaining fibers after h and
the factor are chosen as divisors of the frequency. Thus no Thue theorem
or assumed first-difference mean value is needed in degree nine.
-/

noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionNinthFirst
open SeedCompletionQuadraticRepresentations IntegerDifferencePolynomial AuxiliaryL2Grouping

abbrev Index := ℕ × ℕ × ℕ

def normFactor (h m z : ℕ) : ℕ := (h*m^9)^2+3*z^2

def ninthFirstPhase (h m z : ℕ) : ℕ :=
  2*h*normFactor h m z *
    (3*z^6+27*z^4*(h*m^9)^2+33*z^2*(h*m^9)^4+(h*m^9)^6)

def indexValue (x : Index) : ℕ := ninthFirstPhase x.1 x.2.1 x.2.2
def indexPhase (x : Index) : ℤ := (indexValue x : ℤ)

theorem phase_pos {h m z : ℕ} (hh : 0 < h) (hz : 0 < z) :
    0 < ninthFirstPhase h m z := by
  unfold ninthFirstPhase normFactor
  positivity

theorem height_dvd (h m z : ℕ) : h ∣ ninthFirstPhase h m z := by
  unfold ninthFirstPhase
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_left h 2) _) _

theorem normFactor_dvd (h m z : ℕ) : normFactor h m z ∣ ninthFirstPhase h m z := by
  unfold ninthFirstPhase
  exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _

/-- The factorization is exactly the source normalized centered difference. -/
theorem phase_eq_powerPolynomial (h m z : ℕ) (hm : 0 < m) :
    (ninthFirstPhase h m z : ℤ) =
      (powerPolynomial 9 [((h : ℤ),(m : ℤ))]).eval (z : ℤ) := by
  have hm0 : (m : ℤ)^9 ≠ 0 := pow_ne_zero _ (by exact_mod_cast hm.ne')
  apply mul_left_cancel₀ hm0
  have H := congrArg (fun p : Polynomial ℤ => p.eval (z : ℤ))
    (difference_mul 9 (h : ℤ) (m : ℤ) (Polynomial.X^9))
  have H' : (m : ℤ)^9*(powerPolynomial 9 [((h : ℤ),(m : ℤ))]).eval (z : ℤ) =
      ((z : ℤ)+(h : ℤ)*(m : ℤ)^9)^9-((z : ℤ)-(h : ℤ)*(m : ℤ)^9)^9 := by
    simpa only [powerPolynomial,Polynomial.eval_mul,Polynomial.eval_C,
      Polynomial.eval_sub,Polynomial.eval_comp,Polynomial.eval_pow,
      Polynomial.eval_add,Polynomial.eval_X] using H
  rw [H']
  unfold ninthFirstPhase normFactor
  push_cast
  ring

/-- The actual positive fiber embeds in divisor labels and quadratic pairs. -/
def fiberCode (x : Index) : Σ _ : ℕ × ℕ, ℕ × ℕ :=
  ⟨(x.1,normFactor x.1 x.2.1 x.2.2),(x.1*x.2.1^9,x.2.2)⟩

theorem fiberCode_injective (A : Finset Index) (hpos : ∀ x ∈ A, 0 < x.1) :
    Set.InjOn fiberCode A := by
  intro x hx y hy heq
  have hlabel := congrArg (fun t : Σ _ : ℕ × ℕ, ℕ × ℕ => t.1) heq
  have hpair := congrArg (fun t : Σ _ : ℕ × ℕ, ℕ × ℕ => t.2) heq
  dsimp only [fiberCode] at hlabel hpair
  have hh : x.1=y.1 := congrArg (fun p : ℕ × ℕ => p.1) hlabel
  have hz := congrArg (fun p : ℕ × ℕ => p.2) hpair
  have hm : x.1*x.2.1^9=y.1*y.2.1^9 := congrArg (fun p : ℕ × ℕ => p.1) hpair
  rw [← hh] at hm
  have hpow := Nat.mul_left_cancel (hpos x hx) hm
  have hmeq : x.2.1=y.2.1 := Nat.pow_left_injective (by norm_num : 9 ≠ 0) hpow
  exact Prod.ext hh (Prod.ext hmeq hz)

/-- An explicit fifth divisor power controls every nonzero phase fiber. -/
theorem fiber_card_le_divisors_five (A : Finset Index)
    (hpos : ∀ x ∈ A, 0 < x.1 ∧ 0 < x.2.1 ∧ 0 < x.2.2)
    {n : ℕ} (hn : 0 < n) :
    ((A.filter (fun x => indexValue x=n)).card) ≤ n.divisors.card^5 := by
  classical
  let T := (n.divisors ×ˢ n.divisors).sigma (fun p => representations p.2)
  have hcode : Set.MapsTo fiberCode (A.filter (fun x => indexValue x=n)) T := by
    intro x hx
    obtain ⟨hx,hval⟩ := Finset.mem_filter.mp hx
    have hp := hpos x hx
    apply Finset.mem_sigma.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_,?_⟩,?_⟩
    · exact Nat.mem_divisors.mpr ⟨hval ▸ height_dvd x.1 x.2.1 x.2.2,hn.ne'⟩
    · exact Nat.mem_divisors.mpr ⟨hval ▸ normFactor_dvd x.1 x.2.1 x.2.2,hn.ne'⟩
    · exact mem_representations.mpr ⟨mul_pos hp.1 (pow_pos hp.2.1 9),hp.2.2,rfl⟩
  have hcard : (A.filter (fun x => indexValue x=n)).card ≤ T.card :=
    Finset.card_le_card_of_injOn fiberCode hcode
      ((fiberCode_injective A (fun x hx => (hpos x hx).1)).mono (Finset.filter_subset _ _))
  apply hcard.trans
  rw [Finset.card_sigma]
  calc
    _ ≤ ∑ _p ∈ n.divisors ×ˢ n.divisors, n.divisors.card^3 := by
      apply Finset.sum_le_sum
      intro p hp
      have hp2 := (Finset.mem_product.mp hp).2
      have hpn := (Nat.mem_divisors.mp hp2).1
      exact (representations_card_le_divisors_cube (Nat.pos_of_mem_divisors hp2)).trans
        (Nat.pow_le_pow_left (Finset.card_le_card (Nat.divisors_subset_of_dvd hn.ne' hpn)) 3)
    _ = n.divisors.card^5 := by simp [Finset.card_product]; ring

/-- Uniform subpower fiber bound for actual integer frequencies. -/
theorem fiber_le_rpow {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P → ∀ A : Finset Index,
      (∀ x ∈ A, 0 < x.1 ∧ 0 < x.2.1 ∧ 0 < x.2.2) →
      (∀ x ∈ A, ((indexPhase x).natAbs : ℝ) ≤ P^B) →
      ∀ n ∈ A.image indexPhase,
        ((A.filter (fun x => indexPhase x=n)).card : ℝ) ≤ C*P^ε := by
  let δ := ε/(B+1)
  have hδ : 0 < δ := div_pos hε (by linarith)
  have hBδ : B*δ ≤ ε := by
    have heq : δ*(B+1)=ε := div_mul_cancel₀ ε (by linarith)
    nlinarith
  obtain ⟨C,hC,hdiv⟩ := divisor_power_le_rpow 5 hδ
  refine ⟨C,hC,?_⟩
  intro P hP A hpos hsize n hn
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hn
  have hn0 : 0 < indexValue x := phase_pos (m := x.2.1) (hpos x hx).1 (hpos x hx).2.2
  have hsize' : (indexValue x : ℝ) ≤ P^B := by
    simpa only [indexPhase,Int.natAbs_natCast] using hsize x hx
  have hfilter : A.filter (fun y => indexPhase y=indexPhase x) =
      A.filter (fun y => indexValue y=indexValue x) := by
    ext y
    simp only [Finset.mem_filter,indexPhase,Nat.cast_inj]
  rw [hfilter]
  calc
    _ ≤ ((indexValue x).divisors.card : ℝ)^5 := by
      exact_mod_cast fiber_card_le_divisors_five A hpos hn0
    _ ≤ C*(indexValue x : ℝ)^δ := hdiv _ hn0
    _ ≤ C*(P^B)^δ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) hsize' hδ.le) hC.le
    _ = C*P^(B*δ) := by rw [← Real.rpow_mul (zero_le_one.trans hP)]
    _ ≤ C*P^ε := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hP hBδ) hC.le

/-- The sharp actual second moment, before discharging the box height. -/
theorem first_second_moment {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P → ∀ A : Finset Index,
      (∀ x ∈ A, 0 < x.1 ∧ 0 < x.2.1 ∧ 0 < x.2.2) →
      (∀ x ∈ A, ((indexPhase x).natAbs : ℝ) ≤ P^B) →
      (∫ α in (0 : ℝ)..1,
        ‖∑ x ∈ A, fourier (indexPhase x) (α : AddCircle (1 : ℝ))‖^2) ≤
          C*P^ε*(A.card : ℝ) := by
  obtain ⟨C,hC,hbound⟩ := fiber_le_rpow hB hε
  refine ⟨C,hC,?_⟩
  intro P hP A hpos hsize
  rw [interval_integral_sq_norm_eq_collision_count]
  exact FirstDifferenceSecond.collision_energy_le_fiber_bound A indexPhase
    (hbound P hP A hpos hsize)

/-- Explicit polynomial size on a positive box. -/
theorem phase_real_le {h m z : ℕ} {P : ℝ} (hP : 1 ≤ P)
    (hh : (h : ℝ) ≤ P) (hm : (m : ℝ) ≤ P) (hz : (z : ℝ) ≤ P) :
    (ninthFirstPhase h m z : ℝ) ≤ 512*P^81 := by
  have hmono : (ninthFirstPhase h m z : ℝ) ≤
      2*P*((P*P^9)^2+3*P^2)*
        (3*P^6+27*P^4*(P*P^9)^2+33*P^2*(P*P^9)^4+(P*P^9)^6) := by
    unfold ninthFirstPhase normFactor
    push_cast
    gcongr
  have h9 : P^9 ≤ P^81 := pow_le_pow_right₀ hP (by norm_num)
  have h27 : P^27 ≤ P^81 := pow_le_pow_right₀ hP (by norm_num)
  have h45 : P^45 ≤ P^81 := pow_le_pow_right₀ hP (by norm_num)
  have h63 : P^63 ≤ P^81 := pow_le_pow_right₀ hP (by norm_num)
  calc
    _ ≤ _ := hmono
    _ = 18*P^9+168*P^27+252*P^45+72*P^63+2*P^81 := by ring
    _ ≤ _ := by linarith

/-- Unconditional actual first-difference L2 in degree nine. -/
theorem actual_ninth_first_second_on_box {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ P₀ : ℝ, 1 ≤ P₀ ∧ ∀ P : ℝ, P₀ ≤ P →
      ∀ A : Finset Index,
      (∀ x ∈ A, 0 < x.1 ∧ 0 < x.2.1 ∧ 0 < x.2.2) →
      (∀ x ∈ A, (x.1 : ℝ) ≤ P ∧ (x.2.1 : ℝ) ≤ P ∧ (x.2.2 : ℝ) ≤ P) →
      (∫ α in (0 : ℝ)..1,
        ‖∑ x ∈ A, fourier
          ((powerPolynomial 9 [((x.1 : ℤ),(x.2.1 : ℤ))]).eval (x.2.2 : ℤ))
          (α : AddCircle (1 : ℝ))‖^2) ≤ C*P^ε*(A.card : ℝ) := by
  obtain ⟨C,hC,hbound⟩ := first_second_moment (B := 82) (by norm_num) hε
  refine ⟨C,hC,512,by norm_num,?_⟩
  intro P hPP₀ A hpos hbox
  have hP : 1 ≤ P := (by norm_num : (1 : ℝ) ≤ 512).trans hPP₀
  have hsum (α : ℝ) :
      (∑ x ∈ A, fourier
        ((powerPolynomial 9 [((x.1 : ℤ),(x.2.1 : ℤ))]).eval (x.2.2 : ℤ))
        (α : AddCircle (1 : ℝ))) =
      ∑ x ∈ A, fourier (indexPhase x) (α : AddCircle (1 : ℝ)) := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [← phase_eq_powerPolynomial x.1 x.2.1 x.2.2 (hpos x hx).2.1]
    rfl
  simp_rw [hsum]
  apply hbound P hP A hpos
  intro x hx
  simp only [indexPhase,indexValue,Int.natAbs_natCast]
  have hb := hbox x hx
  calc
    _ ≤ 512*P^81 := phase_real_le hP hb.1 hb.2.1 hb.2.2
    _ ≤ P*P^81 := mul_le_mul_of_nonneg_right hPP₀ (by positivity)
    _ = P^82 := by ring
    _ = P^(82 : ℝ) := by norm_num

theorem actual_ninth_first_second_scaled (L : ℝ) (hL : 1 ≤ L) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ P₀ : ℝ, 1 ≤ P₀ ∧ ∀ P : ℝ, P₀ ≤ P →
      ∀ A : Finset Index,
      (∀ x ∈ A, 0 < x.1 ∧ 0 < x.2.1 ∧ 0 < x.2.2) →
      (∀ x ∈ A, (x.1 : ℝ) ≤ L*P ∧ (x.2.1 : ℝ) ≤ L*P ∧ (x.2.2 : ℝ) ≤ L*P) →
      (∫ α in (0 : ℝ)..1,
        ‖∑ x ∈ A, fourier
          ((powerPolynomial 9 [((x.1 : ℤ),(x.2.1 : ℤ))]).eval (x.2.2 : ℤ))
          (α : AddCircle (1 : ℝ))‖^2) ≤ C*P^ε*(A.card : ℝ) := by
  obtain ⟨C,hC,P₀,hP₀,hbound⟩ := actual_ninth_first_second_on_box hε
  refine ⟨C*L^ε,mul_pos hC (Real.rpow_pos_of_pos (zero_lt_one.trans_le hL) _),P₀,hP₀,?_⟩
  intro P hP A hpos hbox
  have hP0 : 0 ≤ P := zero_le_one.trans (hP₀.trans hP)
  have hPL : P₀ ≤ L*P := hP.trans (le_mul_of_one_le_left hP0 hL)
  convert hbound (L*P) hPL A hpos hbox using 1
  rw [Real.mul_rpow (zero_le_one.trans hL) hP0]
  ring

open CoefficientPower SmoothMoments FirstDifferenceSecond in
def sourceNinthFirstSum (P H Q R M α : ℝ) : ℂ :=
  ∑ x ∈ sourceFirstDomain P H Q R M,
    fourier ((powerPolynomial 9 [((x.1 : ℤ),(x.2.1 : ℤ))]).eval (x.2.2 : ℤ))
      (α : AddCircle (1 : ℝ))

open CoefficientPower SmoothMoments FirstDifferenceSecond in
/-- The literal source estimate in degree nine, with all smooth block and
height ranges retained and R absorbed by an explicit smoothness exponent. -/
theorem source_ninth_first_second_moment {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ P₀ : ℝ, 1 ≤ P₀ ∧ ∀ P : ℝ, P₀ ≤ P →
      ∀ H Q R M : ℝ, 1 ≤ H → H ≤ 2*P → 1 ≤ M → 1 ≤ R →
      M*R ≤ 2*P → R ≤ P^(ε/2) →
      (∫ α in (0 : ℝ)..1, ‖sourceNinthFirstSum P H Q R M α‖^2) ≤
        C*P^(1+ε)*M*H := by
  obtain ⟨C,hC,P₀,hP₀,hbound⟩ := actual_ninth_first_second_scaled
    2 (by norm_num) (show 0 < ε/2 by positivity)
  refine ⟨2*C,by positivity,P₀,hP₀,?_⟩
  intro P hPP₀ H Q R M hH hHP hM hR hMR hRP
  have hP : 1 ≤ P := hP₀.trans hPP₀
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hpos : ∀ x ∈ sourceFirstDomain P H Q R M,
      0 < x.1 ∧ 0 < x.2.1 ∧ 0 < x.2.2 := by
    intro x hx
    rcases Finset.mem_product.mp hx with ⟨hh,hmz⟩
    rcases Finset.mem_product.mp hmz with ⟨hm,hz⟩
    have hm' := (mem_smoothNumbers.mp (Finset.mem_filter.mp hm).1).1.1
    exact ⟨(Finset.mem_Icc.mp hh).1,hm',(Finset.mem_Icc.mp hz).1⟩
  have hbox : ∀ x ∈ sourceFirstDomain P H Q R M,
      (x.1 : ℝ) ≤ 2*P ∧ (x.2.1 : ℝ) ≤ 2*P ∧ (x.2.2 : ℝ) ≤ 2*P := by
    intro x hx
    rcases Finset.mem_product.mp hx with ⟨hh,hmz⟩
    rcases Finset.mem_product.mp hmz with ⟨hm,hz⟩
    refine ⟨((Nat.cast_le.mpr (Finset.mem_Icc.mp hh).2).trans (Nat.floor_le hH0)).trans hHP,
      ((Finset.mem_filter.mp hm).2.2).trans hMR,?_⟩
    exact (Nat.cast_le.mpr (Finset.mem_Icc.mp hz).2).trans (Nat.floor_le (by positivity))
  have hb := hbound P hPP₀ (sourceFirstDomain P H Q R M) hpos hbox
  change (∫ α in (0 : ℝ)..1, ‖sourceNinthFirstSum P H Q R M α‖^2) ≤ _ at hb
  calc
    _ ≤ C*P^(ε/2)*((sourceFirstDomain P H Q R M).card : ℝ) := hb
    _ ≤ C*P^(ε/2)*(2*P*H*M*R) :=
      mul_le_mul_of_nonneg_left (sourceFirstDomain_card hPpos.le hH0 (mul_nonneg hM0 hR0))
        (mul_nonneg hC.le (Real.rpow_nonneg hPpos.le _))
    _ ≤ C*P^(ε/2)*(2*P*H*M*P^(ε/2)) := by gcongr
    _ = (2*C)*P^(1+ε)*M*H := by
      rw [Real.rpow_add hPpos,Real.rpow_one,
        show ε = ε/2+ε/2 by ring,Real.rpow_add hPpos]
      ring

#print axioms actual_ninth_first_second_on_box
#print axioms source_ninth_first_second_moment
#print axioms phase_eq_powerPolynomial
#print axioms fiber_card_le_divisors_five
#print axioms first_second_moment
end Waring.SeedCompletionNinthFirst
