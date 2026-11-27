import Waring.FirstDifferenceCount

/-!
# A divisor bound for the degree-nine second difference

The second coefficient is exactly one, as in the ordinary Weyl step used
to estimate the fourth moment of the first auxiliary sum. The normalized
second difference has the three positive divisors h, a, z. Fixing these
makes its value strictly increasing in the remaining coefficient m.
-/

noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionNinthSecond
open IntegerDifferencePolynomial AuxiliaryL2Grouping

/-- Positive expansion of Psi_2 in degree nine with second coefficient one. -/
def ninthSecondPhase (h m a z : ℕ) : ℕ :=
  96*h*a*z *
    (3*z^6 + 21*a^2*z^4 + 21*a^4*z^2 + 3*a^6 +
      7*h^2*m^18*(3*z^4 + 10*a^2*z^2 + 3*a^4) +
      21*h^4*m^36*(z^2+a^2) + 3*h^6*m^54)

theorem phase_pos {h m a z : ℕ} (hh : 0 < h) (ha : 0 < a) (hz : 0 < z) :
    0 < ninthSecondPhase h m a z := by
  unfold ninthSecondPhase
  positivity

theorem height_dvd (h m a z : ℕ) : h ∣ ninthSecondPhase h m a z := by
  unfold ninthSecondPhase
  apply dvd_mul_of_dvd_left
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_left h 96) a) z

theorem secondHeight_dvd (h m a z : ℕ) : a ∣ ninthSecondPhase h m a z := by
  unfold ninthSecondPhase
  apply dvd_mul_of_dvd_left
  exact dvd_mul_of_dvd_left (dvd_mul_left a (96*h)) z

theorem center_dvd (h m a z : ℕ) : z ∣ ninthSecondPhase h m a z := by
  unfold ninthSecondPhase
  exact dvd_mul_of_dvd_left (dvd_mul_left z (96*h*a)) _

theorem phase_strictMono {h a z : ℕ} (hh : 0 < h) (ha : 0 < a) (hz : 0 < z) :
    StrictMono (fun m => ninthSecondPhase h m a z) := by
  intro m n hmn
  unfold ninthSecondPhase
  apply Nat.mul_lt_mul_of_pos_left _ (by positivity)
  apply Nat.add_lt_add_of_le_of_lt
  · gcongr
  · exact Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_left hmn (by norm_num)) (by positivity)

/-- The exact polynomial identity, before dividing by the first coefficient. -/
theorem phase_mul_identity (h m a z : ℕ) :
    (m : ℤ)^9*(ninthSecondPhase h m a z : ℤ) =
      (((z : ℤ)+(a : ℤ)+(h : ℤ)*(m : ℤ)^9)^9 -
        ((z : ℤ)+(a : ℤ)-(h : ℤ)*(m : ℤ)^9)^9) -
      (((z : ℤ)-(a : ℤ)+(h : ℤ)*(m : ℤ)^9)^9 -
        ((z : ℤ)-(a : ℤ)-(h : ℤ)*(m : ℤ)^9)^9) := by
  unfold ninthSecondPhase
  push_cast
  ring

theorem first_mul_identity (h m z : ℤ) :
    m^9*(powerPolynomial 9 [(h,m)]).eval z = (z+h*m^9)^9-(z-h*m^9)^9 := by
  have H := congrArg (fun p : Polynomial ℤ => p.eval z)
    (difference_mul 9 h m (Polynomial.X^9))
  simpa only [powerPolynomial,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_sub,Polynomial.eval_comp,Polynomial.eval_pow,
    Polynomial.eval_add,Polynomial.eval_X] using H

/-- The expansion is the actual second normalized centered difference. -/
theorem phase_eq_powerPolynomial (h m a z : ℕ) (hm : 0 < m) :
    (ninthSecondPhase h m a z : ℤ) =
      (powerPolynomial 9 [((a : ℤ),1),((h : ℤ),(m : ℤ))]).eval (z : ℤ) := by
  have hm0 : (m : ℤ)^9 ≠ 0 := pow_ne_zero _ (by exact_mod_cast hm.ne')
  apply mul_left_cancel₀ hm0
  rw [phase_mul_identity]
  have H := congrArg (fun p : Polynomial ℤ => p.eval (z : ℤ))
    (difference_mul 9 (a : ℤ) 1 (powerPolynomial 9 [((h : ℤ),(m : ℤ))]))
  have H' : (powerPolynomial 9 [((a : ℤ),1),((h : ℤ),(m : ℤ))]).eval (z : ℤ) =
      (powerPolynomial 9 [((h : ℤ),(m : ℤ))]).eval ((z : ℤ)+(a : ℤ)) -
      (powerPolynomial 9 [((h : ℤ),(m : ℤ))]).eval ((z : ℤ)-(a : ℤ)) := by
    simpa only [powerPolynomial,Polynomial.eval_mul,Polynomial.eval_C,
      Polynomial.eval_sub,Polynomial.eval_comp,Polynomial.eval_pow,
      Polynomial.eval_add,Polynomial.eval_X,one_pow,mul_one,one_mul] using H
  rw [H',mul_sub,first_mul_identity,first_mul_identity]

abbrev Index := ℕ × ℕ × ℕ × ℕ

def indexPhase (x : Index) : ℤ := (ninthSecondPhase x.1 x.2.1 x.2.2.1 x.2.2.2 : ℤ)
def divisorKey (x : Index) : Fin 3 → ℕ := ![x.1,x.2.2.1,x.2.2.2]

theorem divisorKey_dvd (x : Index) (i : Fin 3) : (divisorKey x i : ℤ) ∣ indexPhase x := by
  fin_cases i
  · simpa only [divisorKey,Matrix.cons_val_zero,indexPhase] using
      (show (x.1 : ℤ) ∣ (ninthSecondPhase x.1 x.2.1 x.2.2.1 x.2.2.2 : ℤ) by
        exact_mod_cast height_dvd x.1 x.2.1 x.2.2.1 x.2.2.2)
  · simpa only [divisorKey,Matrix.cons_val_one,Matrix.cons_val_zero,indexPhase] using
      (show (x.2.2.1 : ℤ) ∣ (ninthSecondPhase x.1 x.2.1 x.2.2.1 x.2.2.2 : ℤ) by
        exact_mod_cast secondHeight_dvd x.1 x.2.1 x.2.2.1 x.2.2.2)
  · simpa only [divisorKey,Matrix.cons_val_two,Matrix.cons_val_zero,indexPhase] using
      (show (x.2.2.2 : ℤ) ∣ (ninthSecondPhase x.1 x.2.1 x.2.2.1 x.2.2.2 : ℤ) by
        exact_mod_cast center_dvd x.1 x.2.1 x.2.2.1 x.2.2.2)

theorem divisorKey_injOn_fiber (A : Finset Index)
    (hpos : ∀ x ∈ A, 0 < x.1 ∧ 0 < x.2.2.1 ∧ 0 < x.2.2.2) (n : ℤ) :
    Set.InjOn divisorKey ((A.filter (fun x => indexPhase x=n)) : Set Index) := by
  intro x hx y hy hkey
  have hh := congrFun hkey 0
  have ha := congrFun hkey 1
  have hz := congrFun hkey 2
  simp only [divisorKey,Matrix.cons_val_zero] at hh
  simp only [divisorKey,Matrix.cons_val_one,Matrix.cons_val_zero] at ha
  change x.2.2.2 = y.2.2.2 at hz
  have hf := (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm
  dsimp only [indexPhase] at hf
  have heq : ninthSecondPhase x.1 x.2.1 x.2.2.1 x.2.2.2 =
      ninthSecondPhase y.1 y.2.1 y.2.2.1 y.2.2.2 := by exact_mod_cast hf
  rw [← hh,← ha,← hz] at heq
  have hp := hpos x (Finset.mem_filter.mp hx).1
  have hm := (phase_strictMono hp.1 hp.2.1 hp.2.2).injective heq
  exact Prod.ext hh (Prod.ext hm (Prod.ext ha hz))

/-- Uniform fiber bounds from three positive divisors of each frequency. -/
theorem fiber_le_rpow {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P → ∀ A : Finset Index,
      (∀ x ∈ A, 0 < x.1 ∧ 0 < x.2.2.1 ∧ 0 < x.2.2.2) →
      (∀ x ∈ A, ((indexPhase x).natAbs : ℝ) ≤ P^B) →
      ∀ n ∈ A.image indexPhase,
        ((A.filter (fun x => indexPhase x=n)).card : ℝ) ≤ C*P^ε := by
  obtain ⟨C,hC,hbound⟩ := frequency_key_multiplicity 3 hB hε
  refine ⟨C,hC,?_⟩
  intro P hP A hpos hsize n hn
  have hne : ∀ x ∈ A, indexPhase x ≠ 0 := by
    intro x hx
    have hp := phase_pos (m := x.2.1) (hpos x hx).1 (hpos x hx).2.1 (hpos x hx).2.2
    unfold indexPhase
    exact_mod_cast hp.ne'
  have hb := hbound P hP Index A indexPhase divisorKey
    (fun x hx => ⟨hne x hx,hsize x hx⟩) (fun x hx i => divisorKey_dvd x i) n hn
  have hcard := Finset.card_image_of_injOn (divisorKey_injOn_fiber A hpos n)
  rwa [hcard] at hb

/-- The exact second moment, retaining the actual finite domain. -/
theorem second_moment {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P → ∀ A : Finset Index,
      (∀ x ∈ A, 0 < x.1 ∧ 0 < x.2.2.1 ∧ 0 < x.2.2.2) →
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

/-- A fixed polynomial bound on every literal positive parameter box. -/
theorem phase_real_le {h m a z : ℕ} {P : ℝ} (hP : 1 ≤ P)
    (hh : (h : ℝ) ≤ P) (hm : (m : ℝ) ≤ P)
    (ha : (a : ℝ) ≤ P) (hz : (z : ℝ) ≤ P) :
    (ninthSecondPhase h m a z : ℝ) ≤ 19680*P^63 := by
  have hP0 : 0 ≤ P := zero_le_one.trans hP
  have hmono : (ninthSecondPhase h m a z : ℝ) ≤
      96*P*P*P * (3*P^6 + 21*P^2*P^4 + 21*P^4*P^2 + 3*P^6 +
        7*P^2*P^18*(3*P^4+10*P^2*P^2+3*P^4) +
        21*P^4*P^36*(P^2+P^2) + 3*P^6*P^54) := by
    unfold ninthSecondPhase
    push_cast
    gcongr
  have h6 : P^6 ≤ P^60 := pow_le_pow_right₀ hP (by norm_num)
  have h24 : P^24 ≤ P^60 := pow_le_pow_right₀ hP (by norm_num)
  have h42 : P^42 ≤ P^60 := pow_le_pow_right₀ hP (by norm_num)
  have hin : 48*P^6+112*P^24+42*P^42+3*P^60 ≤ 205*P^60 := by linarith
  calc
    _ ≤ _ := hmono
    _ = 96*P^3*(48*P^6+112*P^24+42*P^42+3*P^60) := by ring
    _ ≤ 96*P^3*(205*P^60) := mul_le_mul_of_nonneg_left hin (by positivity)
    _ = _ := by ring

/-- The sharp degree-nine second-difference L2 estimate on an arbitrary
positive finite box. Every frequency-size premise has been discharged. -/
theorem actual_second_difference_second_on_box {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ P₀ : ℝ, 1 ≤ P₀ ∧ ∀ P : ℝ, P₀ ≤ P →
      ∀ A : Finset Index,
      (∀ x ∈ A, 0 < x.1 ∧ 0 < x.2.1 ∧ 0 < x.2.2.1 ∧ 0 < x.2.2.2) →
      (∀ x ∈ A, (x.1 : ℝ) ≤ P ∧ (x.2.1 : ℝ) ≤ P ∧
        (x.2.2.1 : ℝ) ≤ P ∧ (x.2.2.2 : ℝ) ≤ P) →
      (∫ α in (0 : ℝ)..1,
        ‖∑ x ∈ A, fourier
          ((powerPolynomial 9 [((x.2.2.1 : ℤ),1),((x.1 : ℤ),(x.2.1 : ℤ))]).eval
            (x.2.2.2 : ℤ)) (α : AddCircle (1 : ℝ))‖^2) ≤
          C*P^ε*(A.card : ℝ) := by
  obtain ⟨C,hC,hbound⟩ := second_moment (B := 64) (by norm_num) hε
  refine ⟨C,hC,19680,by norm_num,?_⟩
  intro P hPP₀ A hpos hbox
  have hP : 1 ≤ P := (by norm_num : (1 : ℝ) ≤ 19680).trans hPP₀
  have hsum (α : ℝ) :
      (∑ x ∈ A, fourier
        ((powerPolynomial 9 [((x.2.2.1 : ℤ),1),((x.1 : ℤ),(x.2.1 : ℤ))]).eval
          (x.2.2.2 : ℤ)) (α : AddCircle (1 : ℝ))) =
      ∑ x ∈ A, fourier (indexPhase x) (α : AddCircle (1 : ℝ)) := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [← phase_eq_powerPolynomial x.1 x.2.1 x.2.2.1 x.2.2.2 (hpos x hx).2.1]
    rfl
  simp_rw [hsum]
  apply hbound P hP A (fun x hx => ⟨(hpos x hx).1,(hpos x hx).2.2⟩)
  intro x hx
  simp only [indexPhase,Int.natAbs_natCast,Real.rpow_natCast]
  have hb := hbox x hx
  calc
    _ ≤ 19680*P^63 := phase_real_le hP hb.1 hb.2.1 hb.2.2.1 hb.2.2.2
    _ ≤ P*P^63 := mul_le_mul_of_nonneg_right hPP₀ (by positivity)
    _ = P^64 := by ring
    _ = P^(64 : ℝ) := by norm_num

#print axioms actual_second_difference_second_on_box
#print axioms phase_eq_powerPolynomial
#print axioms fiber_le_rpow
#print axioms second_moment
end Waring.SeedCompletionNinthSecond
