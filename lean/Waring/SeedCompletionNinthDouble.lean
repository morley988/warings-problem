import Waring.SeedCompletionNinthSecond
import Waring.DerivativeZeroCount

/-!
# The actual degree-nine second difference with both coefficients varying

The odd center supplies a third divisor for frequency grouping. Equality
of the complete center polynomials determines the two scaled coefficients
up to permutation. These are the arithmetic inputs of the genuine j=2
second moment; neither coefficient is fixed to one in this module.
-/

noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionNinthDouble
open IntegerDifferencePolynomial AuxiliaryL2Grouping

abbrev Pair := ℕ × ℕ

def amplitude (h m : Pair) : Pair := (h.1*m.1^9,h.2*m.2^9)
def leadingFactor (h : Pair) : ℕ := 96*h.1*h.2

def doublePhase (h m : Pair) (z : ℕ) : ℕ :=
  let a := (amplitude h m).1
  let b := (amplitude h m).2
  leadingFactor h *
    (3*z^7 + 21*(a^2+b^2)*z^5 +
      (21*(a^4+b^4)+70*a^2*b^2)*z^3 +
      (3*(a^6+b^6)+21*(a^4*b^2+a^2*b^4))*z)

def doublePolynomial (h m : Pair) : Polynomial ℤ :=
  let a := (amplitude h m).1
  let b := (amplitude h m).2
  Polynomial.monomial 7 ((leadingFactor h*3 : ℕ) : ℤ) +
  Polynomial.monomial 5 ((leadingFactor h*(21*(a^2+b^2)) : ℕ) : ℤ) +
  Polynomial.monomial 3 ((leadingFactor h*(21*(a^4+b^4)+70*a^2*b^2) : ℕ) : ℤ) +
  Polynomial.monomial 1 ((leadingFactor h*(3*(a^6+b^6)+21*(a^4*b^2+a^2*b^4)) : ℕ) : ℤ)

theorem doublePolynomial_eval (h m : Pair) (z : ℕ) :
    (doublePolynomial h m).eval (z : ℤ) = (doublePhase h m z : ℤ) := by
  simp only [doublePolynomial,Polynomial.eval_add,Polynomial.eval_monomial,
    doublePhase]
  push_cast
  ring

/-- Expansion before cancellation of the two normalizing powers. -/
theorem doublePhase_mul_identity (h m : Pair) (z : ℕ) :
    (m.1 : ℤ)^9*(m.2 : ℤ)^9*(doublePhase h m z : ℤ) =
      ((((z : ℤ)+(h.2 : ℤ)*(m.2 : ℤ)^9)+(h.1 : ℤ)*(m.1 : ℤ)^9)^9 -
        (((z : ℤ)+(h.2 : ℤ)*(m.2 : ℤ)^9)-(h.1 : ℤ)*(m.1 : ℤ)^9)^9) -
      ((((z : ℤ)-(h.2 : ℤ)*(m.2 : ℤ)^9)+(h.1 : ℤ)*(m.1 : ℤ)^9)^9 -
        (((z : ℤ)-(h.2 : ℤ)*(m.2 : ℤ)^9)-(h.1 : ℤ)*(m.1 : ℤ)^9)^9) := by
  unfold doublePhase leadingFactor amplitude
  push_cast
  ring

/-- Both coefficient powers are normalized exactly as in the source. -/
theorem doublePhase_eq_powerPolynomial (h m : Pair) (z : ℕ)
    (hm₁ : 0 < m.1) (hm₂ : 0 < m.2) :
    (doublePhase h m z : ℤ) =
      (powerPolynomial 9 [((h.2 : ℤ),(m.2 : ℤ)),((h.1 : ℤ),(m.1 : ℤ))]).eval (z : ℤ) := by
  have hm1 : (m.1 : ℤ)^9 ≠ 0 := pow_ne_zero _ (by exact_mod_cast hm₁.ne')
  have hm2 : (m.2 : ℤ)^9 ≠ 0 := pow_ne_zero _ (by exact_mod_cast hm₂.ne')
  apply mul_left_cancel₀ (mul_ne_zero hm1 hm2)
  rw [doublePhase_mul_identity]
  have H := congrArg (fun p : Polynomial ℤ => p.eval (z : ℤ))
    (difference_mul 9 (h.2 : ℤ) (m.2 : ℤ)
      (powerPolynomial 9 [((h.1 : ℤ),(m.1 : ℤ))]))
  have H' : (m.2 : ℤ)^9 *
      (powerPolynomial 9 [((h.2 : ℤ),(m.2 : ℤ)),((h.1 : ℤ),(m.1 : ℤ))]).eval (z : ℤ) =
      (powerPolynomial 9 [((h.1 : ℤ),(m.1 : ℤ))]).eval
        ((z : ℤ)+(h.2 : ℤ)*(m.2 : ℤ)^9) -
      (powerPolynomial 9 [((h.1 : ℤ),(m.1 : ℤ))]).eval
        ((z : ℤ)-(h.2 : ℤ)*(m.2 : ℤ)^9) := by
    simpa only [powerPolynomial,Polynomial.eval_mul,Polynomial.eval_C,
      Polynomial.eval_sub,Polynomial.eval_comp,Polynomial.eval_pow,
      Polynomial.eval_add,Polynomial.eval_X] using H
  rw [mul_assoc,H',mul_sub,
    SeedCompletionNinthSecond.first_mul_identity,
    SeedCompletionNinthSecond.first_mul_identity]

theorem doublePhase_pos {h m : Pair} {z : ℕ}
    (h₁ : 0 < h.1) (h₂ : 0 < h.2) (hz : 0 < z) :
    0 < doublePhase h m z := by
  unfold doublePhase leadingFactor
  positivity

theorem firstHeight_dvd (h m : Pair) (z : ℕ) : h.1 ∣ doublePhase h m z := by
  unfold doublePhase leadingFactor
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_left h.1 96) h.2) _

theorem secondHeight_dvd (h m : Pair) (z : ℕ) : h.2 ∣ doublePhase h m z := by
  unfold doublePhase leadingFactor
  exact dvd_mul_of_dvd_left (dvd_mul_left h.2 (96*h.1)) _

theorem center_dvd (h m : Pair) (z : ℕ) : z ∣ doublePhase h m z := by
  unfold doublePhase
  apply dvd_mul_of_dvd_right
  apply dvd_add
  · apply dvd_add
    · apply dvd_add
      · exact dvd_mul_of_dvd_right (dvd_pow_self z (by norm_num : 7 ≠ 0)) 3
      · exact dvd_mul_of_dvd_right (dvd_pow_self z (by norm_num : 5 ≠ 0)) _
    · exact dvd_mul_of_dvd_right (dvd_pow_self z (by norm_num : 3 ≠ 0)) _
  · exact dvd_mul_left z _

theorem doublePolynomial_coeff_five (h m : Pair) :
    (doublePolynomial h m).coeff 5 =
      (leadingFactor h*(21*((amplitude h m).1^2+(amplitude h m).2^2)) : ℕ) := by
  simp [doublePolynomial,Polynomial.coeff_monomial]

theorem doublePolynomial_coeff_three (h m : Pair) :
    (doublePolynomial h m).coeff 3 =
      (leadingFactor h*(21*((amplitude h m).1^4+(amplitude h m).2^4)+
        70*(amplitude h m).1^2*(amplitude h m).2^2) : ℕ) := by
  simp [doublePolynomial,Polynomial.coeff_monomial]

theorem doublePolynomial_natDegree_le (h m : Pair) :
    (doublePolynomial h m).natDegree ≤ 7 := by
  unfold doublePolynomial
  apply (Polynomial.natDegree_add_le _ _).trans
  apply max_le
  · apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le
    · apply (Polynomial.natDegree_add_le _ _).trans
      exact max_le (Polynomial.natDegree_monomial_le _) ((Polynomial.natDegree_monomial_le _).trans (by norm_num))
    · exact (Polynomial.natDegree_monomial_le _).trans (by norm_num)
  · exact (Polynomial.natDegree_monomial_le _).trans (by norm_num)

/-- Positive natural pairs are determined up to interchange by their first
and second elementary symmetric polynomials. -/
theorem pair_eq_or_swap_of_sum_prod {a b c d : ℕ}
    (hs : a+b=c+d) (hp : a*b=c*d) :
    (a=c ∧ b=d) ∨ (a=d ∧ b=c) := by
  have hs' : (a : ℤ)+b=c+d := by exact_mod_cast hs
  have hp' : (a : ℤ)*b=c*d := by exact_mod_cast hp
  have he : ((a : ℤ)-c)*((a : ℤ)-d)=0 := by nlinarith
  rcases mul_eq_zero.mp he with hc | hd
  · have hac : a=c := by exact_mod_cast (sub_eq_zero.mp hc)
    exact Or.inl ⟨hac,by omega⟩
  · have had : a=d := by exact_mod_cast (sub_eq_zero.mp hd)
    exact Or.inr ⟨had,by omega⟩

/-- Literal equality of the two degree-seven center polynomials determines
(h1*m1^9,h2*m2^9) up to permutation. -/
theorem amplitude_eq_or_swap {h m n : Pair}
    (h₁ : 0 < h.1) (h₂ : 0 < h.2)
    (he : doublePolynomial h m = doublePolynomial h n) :
    amplitude h m = amplitude h n ∨
      amplitude h m = ((amplitude h n).2,(amplitude h n).1) := by
  have hc5 := congrArg (fun p : Polynomial ℤ => p.coeff 5) he
  dsimp only at hc5
  rw [doublePolynomial_coeff_five,doublePolynomial_coeff_five] at hc5
  have h5 : leadingFactor h*(21*((amplitude h m).1^2+(amplitude h m).2^2)) =
      leadingFactor h*(21*((amplitude h n).1^2+(amplitude h n).2^2)) := by exact_mod_cast hc5
  have hL : 0 < leadingFactor h := by unfold leadingFactor; positivity
  have hs : (amplitude h m).1^2+(amplitude h m).2^2 =
      (amplitude h n).1^2+(amplitude h n).2^2 := by
    exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 21)
      (Nat.eq_of_mul_eq_mul_left hL h5)
  have hc3 := congrArg (fun p : Polynomial ℤ => p.coeff 3) he
  dsimp only at hc3
  rw [doublePolynomial_coeff_three,doublePolynomial_coeff_three] at hc3
  have h3 : leadingFactor h*(21*((amplitude h m).1^4+(amplitude h m).2^4)+
      70*(amplitude h m).1^2*(amplitude h m).2^2) =
      leadingFactor h*(21*((amplitude h n).1^4+(amplitude h n).2^4)+
      70*(amplitude h n).1^2*(amplitude h n).2^2) := by exact_mod_cast hc3
  have h3' := Nat.eq_of_mul_eq_mul_left hL h3
  have hprod : (amplitude h m).1^2*(amplitude h m).2^2 =
      (amplitude h n).1^2*(amplitude h n).2^2 := by
    nlinarith [congrArg (fun t : ℕ => t^2) hs]
  rcases pair_eq_or_swap_of_sum_prod hs hprod with hpair | hpair
  · exact Or.inl (Prod.ext
      (Nat.pow_left_injective (by norm_num : 2 ≠ 0) hpair.1)
      (Nat.pow_left_injective (by norm_num : 2 ≠ 0) hpair.2))
  · exact Or.inr (Prod.ext
      (Nat.pow_left_injective (by norm_num : 2 ≠ 0) hpair.1)
      (Nat.pow_left_injective (by norm_num : 2 ≠ 0) hpair.2))

/-- The amplitudes have an injective dependence on the positive coefficients
once the positive heights are fixed. -/
theorem amplitude_injective {h : Pair} (h₁ : 0 < h.1) (h₂ : 0 < h.2) :
    Function.Injective (amplitude h) := by
  intro m n he
  have h1 := congrArg Prod.fst he
  have h2 := congrArg Prod.snd he
  change h.1*m.1^9=h.1*n.1^9 at h1
  change h.2*m.2^9=h.2*n.2^9 at h2
  exact Prod.ext
    (Nat.pow_left_injective (by norm_num : 9 ≠ 0) (Nat.eq_of_mul_eq_mul_left h₁ h1))
    (Nat.pow_left_injective (by norm_num : 9 ≠ 0) (Nat.eq_of_mul_eq_mul_left h₂ h2))

/-- Every complete center-polynomial fiber contains at most two coefficient
pairs, with no finiteness or size premise on their possible values. -/
theorem polynomial_fiber_card_le_two (h m : Pair) (B : Finset Pair)
    (h₁ : 0 < h.1) (h₂ : 0 < h.2) :
    (B.filter (fun n => doublePolynomial h n=doublePolynomial h m)).card ≤ 2 := by
  classical
  let F := B.filter (fun n => doublePolynomial h n=doublePolynomial h m)
  have hs : F.image (amplitude h) ⊆
      {amplitude h m,((amplitude h m).2,(amplitude h m).1)} := by
    intro x hx
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hx
    rcases amplitude_eq_or_swap h₁ h₂ (Finset.mem_filter.mp hn).2 with he | he
    · exact Finset.mem_insert.mpr (Or.inl he)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr he))
  calc
    _ = (F.image (amplitude h)).card := by
      symm
      exact Finset.card_image_iff.mpr (amplitude_injective h₁ h₂).injOn
    _ ≤ ({amplitude h m,((amplitude h m).2,(amplitude h m).1)} : Finset Pair).card :=
      Finset.card_le_card hs
    _ ≤ 2 := Finset.card_le_two

/-- A genuinely unequal pair of center polynomials agrees at at most seven
integer centers, independently of all coefficients and box lengths. -/
theorem unequal_polynomial_centers_card_le (h m n : Pair) (Z : Finset ℕ)
    (hne : doublePolynomial h m ≠ doublePolynomial h n) :
    (Z.filter (fun z => doublePhase h m z=doublePhase h n z)).card ≤ 7 := by
  classical
  let F := Z.filter (fun z => doublePhase h m z=doublePhase h n z)
  let p := doublePolynomial h m-doublePolynomial h n
  have hp : p ≠ 0 := sub_ne_zero.mpr hne
  have hroots : ∀ z ∈ F.image (fun z : ℕ => (z : ℤ)), z ∈ p.roots := by
    intro z hz
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hz
    apply (Polynomial.mem_roots hp).mpr
    change p.eval (t : ℤ)=0
    simp only [p,Polynomial.eval_sub,doublePolynomial_eval]
    exact sub_eq_zero.mpr (by exact_mod_cast (Finset.mem_filter.mp ht).2)
  have hdeg : p.natDegree ≤ 7 := (Polynomial.natDegree_sub_le _ _).trans
    (max_le (doublePolynomial_natDegree_le h m) (doublePolynomial_natDegree_le h n))
  calc
    _ = (F.image (fun z : ℕ => (z : ℤ))).card := by
      symm
      exact Finset.card_image_of_injective _ Nat.cast_injective
    _ ≤ p.natDegree := Polynomial.card_le_degree_of_subset_roots hroots
    _ ≤ 7 := hdeg

#print axioms doublePhase_eq_powerPolynomial
#print axioms unequal_polynomial_centers_card_le
#print axioms polynomial_fiber_card_le_two
#print axioms amplitude_eq_or_swap
end Waring.SeedCompletionNinthDouble
