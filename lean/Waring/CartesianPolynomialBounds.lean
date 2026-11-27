import Waring.CoefficientFactorization
import Waring.CoefficientPower

/-!
# Cartesian coefficient families and the completed source product

This module joins the actual five original polynomial families to their
quadratic/coefficient products. The Cartesian coefficient tuple is regrouped
exactly, then factored, and only then is a triangle inequality applied over
the ordinary shifts and h parameters. Every completed quadratic sum uses
one common real modulation.
-/

noncomputable section
open scoped BigOperators
namespace Waring.CartesianPolynomialBounds
open PolynomialSumReduction CoefficientFactorization QuadraticModulation

def cartesianParameters {j : ℕ} (H : Finset (Fin j → ℝ)) (C : Fin j → Finset ℝ) :=
  H ×ˢ Fintype.piFinset C

def centeredSet (N : ℕ) : Finset ℤ := Finset.Icc (-(2*(N:ℤ))) (2*(N:ℤ))

def completionLoss (N : ℕ) : ℝ := 4*(2+Real.log (2*(N:ℝ))/Real.log 2)

def firstProducts {j : ℕ} (p : ℕ) (A α : ℝ) (H : Finset (Fin j → ℝ))
    (C : Fin j → Finset ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  ∑ hu ∈ H ×ˢ Finset.Icc (1:ℤ) (N:ℤ),
    ‖quadraticSum (centeredSet N) (3*α*A*((∏ l, hu.1 l)*(hu.2:ℝ))) t‖ *
      ∏ l, ‖coefficientSum p (C l) ((4*α*A*((∏ l, hu.1 l)*(hu.2:ℝ)))*(hu.1 l)^2)‖

def secondProducts {j : ℕ} (p : ℕ) (A α : ℝ) (H : Finset (Fin j → ℝ))
    (C : Fin j → Finset ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  ∑ huv ∈ (H ×ˢ Finset.Icc (1:ℤ) (N:ℤ)) ×ˢ Finset.Icc (1:ℤ) (N:ℤ),
    ‖quadraticSum (centeredSet N)
      (3*α*A*((∏ l, huv.1.1 l)*(huv.1.2:ℝ)*(huv.2:ℝ))) t‖ *
      ∏ l, ‖coefficientSum p (C l)
        ((4*α*A*((∏ l, huv.1.1 l)*(huv.1.2:ℝ)*(huv.2:ℝ)))*(huv.1.1 l)^2)‖

theorem cartesianParameters_card {j : ℕ} (H : Finset (Fin j → ℝ))
    (C : Fin j → Finset ℝ) :
    (cartesianParameters H C).card = H.card * ∏ i, (C i).card := by
  simp only [cartesianParameters, Finset.card_product, Fintype.card_piFinset]

theorem coefficientSum_nat_image (p : ℕ) (C : Finset ℕ) (β : ℝ) :
    coefficientSum p (C.image (fun m : ℕ => (m:ℝ))) β =
      CoefficientPower.coefficientWeyl C p β := by
  classical
  unfold coefficientSum CoefficientPower.coefficientWeyl
  exact Finset.sum_image (fun _ _ _ _ h => Nat.cast_injective h)

theorem parityInterval_subset_centered (N Q : ℕ) (s : ℤ)
    (hQN : Q ≤ N) (hs : 0 ≤ s) :
    parityInterval 1 ((Q:ℤ)-s) s ⊆ centeredSet N := by
  intro ξ hξ
  have hh := Finset.mem_Icc.mp (Finset.mem_filter.mp hξ).1
  apply Finset.mem_Icc.mpr
  constructor <;> omega

theorem parityInterval_length_le (N Q : ℕ) (s : ℤ)
    (hQN : Q ≤ N) (hs : 0 ≤ s) :
    (2*((Q:ℤ)-s)+s+1-(2+s)).toNat ≤ 2*N := by
  omega

/-- Exact regrouping of m and the first ordinary shift. -/
theorem reducedFirst_cartesian {j : ℕ} (p : ℕ) (A α : ℝ)
    (H : Finset (Fin j → ℝ)) (C : Fin j → Finset ℝ) (a b : ℤ) (N : ℕ) :
    reducedFirstSum p A (cartesianParameters H C) Prod.fst Prod.snd α a b N =
      ∑ hu ∈ H ×ˢ Finset.Icc (1:ℤ) (N:ℤ), ∑ m ∈ Fintype.piFinset C,
        ∑ ξ ∈ parityInterval a (b-hu.2) hu.2,
          e (α*normalForm p A ((∏ l, hu.1 l)*(hu.2:ℝ)) ((hu.2:ℝ)^2) hu.1 m (ξ:ℝ)) := by
  classical
  simp only [reducedFirstSum, cartesianParameters, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro h hh
  exact Finset.sum_comm

/-- Exact regrouping of m and both ordinary shifts; no extra m tuple. -/
theorem reducedSecond_cartesian {j : ℕ} (p : ℕ) (A α : ℝ)
    (H : Finset (Fin j → ℝ)) (C : Fin j → Finset ℝ) (a b : ℤ) (N : ℕ) :
    reducedSecondSum p A (cartesianParameters H C) Prod.fst Prod.snd α a b N =
      ∑ huv ∈ (H ×ˢ Finset.Icc (1:ℤ) (N:ℤ)) ×ˢ Finset.Icc (1:ℤ) (N:ℤ),
        ∑ m ∈ Fintype.piFinset C,
          ∑ ξ ∈ parityInterval a (b-huv.1.2-huv.2) (huv.1.2+huv.2),
            e (α*normalForm p A ((∏ l, huv.1.1 l)*(huv.1.2:ℝ)*(huv.2:ℝ))
              ((huv.1.2:ℝ)^2+(huv.2:ℝ)^2) huv.1.1 m (ξ:ℝ)) := by
  classical
  simp only [reducedSecondSum, cartesianParameters, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro h hh
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  exact Finset.sum_comm

/-- The actual first reduced sum is bounded by the completed common-t
product. The parity intervals are proved to lie inside the centered range. -/
theorem reducedFirst_completed_bound {j : ℕ} (p : ℕ) (A α : ℝ)
    (H : Finset (Fin j → ℝ)) (C : Fin j → Finset ℝ) (N Q : ℕ)
    (hN : 0 < N) (hQN : Q ≤ N) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ t ∈ Set.Icc (0:ℝ) 1, firstProducts p A α H C N t ≤ B) :
    ‖reducedFirstSum p A (cartesianParameters H C) Prod.fst Prod.snd α 1 Q N‖ ≤
      completionLoss N*B := by
  rw [reducedFirst_cartesian]
  have Hbound := completed_product_bound (H ×ˢ Finset.Icc (1:ℤ) (N:ℤ)) p A α
    (fun hu => (∏ l, hu.1 l)*(hu.2:ℝ)) (fun hu => (hu.2:ℝ)^2)
    (fun _ => C) Prod.fst (fun hu => 2+hu.2) (fun hu => 2*((Q:ℤ)-hu.2)+hu.2)
    Prod.snd (centeredSet N) (2*N) (by omega)
    (by
      intro hu hhu
      have hs := (Finset.mem_Icc.mp (Finset.mem_product.mp hhu).2).1
      exact parityInterval_length_le N Q hu.2 hQN (by omega))
    (by
      intro hu hhu
      have hs := (Finset.mem_Icc.mp (Finset.mem_product.mp hhu).2).1
      exact parityInterval_subset_centered N Q hu.2 hQN (by omega))
    B hB0 hB
  simpa only [parityInterval, mul_one, completionLoss, Nat.cast_mul, Nat.cast_ofNat] using Hbound

theorem reducedSecond_completed_bound {j : ℕ} (p : ℕ) (A α : ℝ)
    (H : Finset (Fin j → ℝ)) (C : Fin j → Finset ℝ) (N Q : ℕ)
    (hN : 0 < N) (hQN : Q ≤ N) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ t ∈ Set.Icc (0:ℝ) 1, secondProducts p A α H C N t ≤ B) :
    ‖reducedSecondSum p A (cartesianParameters H C) Prod.fst Prod.snd α 1 Q N‖ ≤
      completionLoss N*B := by
  rw [reducedSecond_cartesian]
  have Hbound := completed_product_bound
    ((H ×ˢ Finset.Icc (1:ℤ) (N:ℤ)) ×ˢ Finset.Icc (1:ℤ) (N:ℤ)) p A α
    (fun huv => (∏ l, huv.1.1 l)*(huv.1.2:ℝ)*(huv.2:ℝ))
    (fun huv => (huv.1.2:ℝ)^2+(huv.2:ℝ)^2) (fun _ => C) (fun huv => huv.1.1)
    (fun huv => 2+(huv.1.2+huv.2))
    (fun huv => 2*((Q:ℤ)-huv.1.2-huv.2)+(huv.1.2+huv.2))
    (fun huv => huv.1.2+huv.2) (centeredSet N) (2*N) (by omega)
    (by
      intro huv hhuv
      have hu := (Finset.mem_Icc.mp (Finset.mem_product.mp (Finset.mem_product.mp hhuv).1).2).1
      have hv := (Finset.mem_Icc.mp (Finset.mem_product.mp hhuv).2).1
      have hh := parityInterval_length_le N Q (huv.1.2+huv.2) hQN (by omega)
      simpa only [sub_add_eq_sub_sub] using hh)
    (by
      intro huv hhuv
      have hu := (Finset.mem_Icc.mp (Finset.mem_product.mp (Finset.mem_product.mp hhuv).1).2).1
      have hv := (Finset.mem_Icc.mp (Finset.mem_product.mp hhuv).2).1
      have hh := parityInterval_subset_centered N Q (huv.1.2+huv.2) hQN (by omega)
      simpa only [parityInterval, mul_one, sub_add_eq_sub_sub] using hh)
    B hB0 hB
  simpa only [parityInterval, mul_one, completionLoss, Nat.cast_mul, Nat.cast_ofNat] using Hbound

private theorem coefficient_tuple_nonzero {j : ℕ} (H : Finset (Fin j → ℝ))
    (C : Fin j → Finset ℝ) (hC : ∀ l, ∀ m ∈ C l, m ≠ 0) :
    ∀ hm ∈ cartesianParameters H C, ∀ l, hm.2 l ≠ 0 := by
  intro hm hhm l
  exact hC l _ (Fintype.mem_piFinset.mp (Finset.mem_product.mp hhm).2 l)

/-- End-to-end k=8, j=4 conversion of the actual original family to its
completed common-t quadratic/coefficient product estimate. -/
theorem cartesian_k8_j4_completed_bound (H : Finset (Fin 4 → ℝ))
    (C : Fin 4 → Finset ℝ) (α : ℝ) (N Q : ℕ) (hN : 0 < N) (hQN : Q ≤ N)
    (hC : ∀ l, ∀ m ∈ C l, m ≠ 0) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ t ∈ Set.Icc (0:ℝ) 1, secondProducts 16 26880 α H C N t ≤ B) :
    ‖polynomialFamily 8 (cartesianParameters H C) Prod.fst Prod.snd α 1 Q‖^4 ≤
      16*((N:ℝ)^3*((H.card*∏ l, (C l).card:ℕ):ℝ)^4+(N:ℝ)*((H.card*∏ l, (C l).card:ℕ):ℝ)^3*(completionLoss N*B)) := by
  have Hfirst := family_k8_j4_quadratic_bound (cartesianParameters H C)
    Prod.fst Prod.snd α 1 Q N hN (by omega) (coefficient_tuple_nonzero H C hC)
  have HG := reducedSecond_completed_bound 16 26880 α H C N Q hN hQN B hB0 hB
  have Hmul := mul_le_mul_of_nonneg_left HG
    (show 0 ≤ (N:ℝ)*((cartesianParameters H C).card:ℝ)^3 by positivity)
  rw [cartesianParameters_card] at Hfirst Hmul
  exact Hfirst.trans (mul_le_mul_of_nonneg_left (add_le_add_left Hmul _) (by norm_num : (0:ℝ) ≤ 16))

/-- End-to-end k=8, j=5 conversion of the actual original family to its
completed common-t quadratic/coefficient product estimate. -/
theorem cartesian_k8_j5_completed_bound (H : Finset (Fin 5 → ℝ))
    (C : Fin 5 → Finset ℝ) (α : ℝ) (N Q : ℕ) (hN : 0 < N) (hQN : Q ≤ N)
    (hC : ∀ l, ∀ m ∈ C l, m ≠ 0) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ t ∈ Set.Icc (0:ℝ) 1, firstProducts 16 53760 α H C N t ≤ B) :
    ‖polynomialFamily 8 (cartesianParameters H C) Prod.fst Prod.snd α 1 Q‖^2 ≤
      (N:ℝ)*((H.card*∏ l, (C l).card:ℕ):ℝ)^2+2*((H.card*∏ l, (C l).card:ℕ):ℝ)*(completionLoss N*B) := by
  have Hfirst := family_k8_j5_quadratic_bound (cartesianParameters H C)
    Prod.fst Prod.snd α 1 Q N (by omega) (coefficient_tuple_nonzero H C hC)
  have HG := reducedFirst_completed_bound 16 53760 α H C N Q hN hQN B hB0 hB
  have Hmul := mul_le_mul_of_nonneg_left HG
    (show 0 ≤ 2*((cartesianParameters H C).card:ℝ) by positivity)
  rw [cartesianParameters_card] at Hfirst Hmul
  exact Hfirst.trans (add_le_add_left Hmul _)

/-- End-to-end k=9, j=5 conversion of the actual original family to its
completed common-t quadratic/coefficient product estimate. -/
theorem cartesian_k9_j5_completed_bound (H : Finset (Fin 5 → ℝ))
    (C : Fin 5 → Finset ℝ) (α : ℝ) (N Q : ℕ) (hN : 0 < N) (hQN : Q ≤ N)
    (hC : ∀ l, ∀ m ∈ C l, m ≠ 0) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ t ∈ Set.Icc (0:ℝ) 1, secondProducts 18 483840 α H C N t ≤ B) :
    ‖polynomialFamily 9 (cartesianParameters H C) Prod.fst Prod.snd α 1 Q‖^4 ≤
      16*((N:ℝ)^3*((H.card*∏ l, (C l).card:ℕ):ℝ)^4+(N:ℝ)*((H.card*∏ l, (C l).card:ℕ):ℝ)^3*(completionLoss N*B)) := by
  have Hfirst := family_k9_j5_quadratic_bound (cartesianParameters H C)
    Prod.fst Prod.snd α 1 Q N hN (by omega) (coefficient_tuple_nonzero H C hC)
  have HG := reducedSecond_completed_bound 18 483840 α H C N Q hN hQN B hB0 hB
  have Hmul := mul_le_mul_of_nonneg_left HG
    (show 0 ≤ (N:ℝ)*((cartesianParameters H C).card:ℝ)^3 by positivity)
  rw [cartesianParameters_card] at Hfirst Hmul
  exact Hfirst.trans (mul_le_mul_of_nonneg_left (add_le_add_left Hmul _) (by norm_num : (0:ℝ) ≤ 16))

/-- End-to-end k=9, j=6 conversion of the actual original family to its
completed common-t quadratic/coefficient product estimate. -/
theorem cartesian_k9_j6_completed_bound (H : Finset (Fin 6 → ℝ))
    (C : Fin 6 → Finset ℝ) (α : ℝ) (N Q : ℕ) (hN : 0 < N) (hQN : Q ≤ N)
    (hC : ∀ l, ∀ m ∈ C l, m ≠ 0) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ t ∈ Set.Icc (0:ℝ) 1, firstProducts 18 967680 α H C N t ≤ B) :
    ‖polynomialFamily 9 (cartesianParameters H C) Prod.fst Prod.snd α 1 Q‖^2 ≤
      (N:ℝ)*((H.card*∏ l, (C l).card:ℕ):ℝ)^2+2*((H.card*∏ l, (C l).card:ℕ):ℝ)*(completionLoss N*B) := by
  have Hfirst := family_k9_j6_quadratic_bound (cartesianParameters H C)
    Prod.fst Prod.snd α 1 Q N (by omega) (coefficient_tuple_nonzero H C hC)
  have HG := reducedFirst_completed_bound 18 967680 α H C N Q hN hQN B hB0 hB
  have Hmul := mul_le_mul_of_nonneg_left HG
    (show 0 ≤ 2*((cartesianParameters H C).card:ℝ) by positivity)
  rw [cartesianParameters_card] at Hfirst Hmul
  exact Hfirst.trans (add_le_add_left Hmul _)

def zeroProducts {j : ℕ} (p : ℕ) (A α : ℝ) (H : Finset (Fin j → ℝ))
    (C : Fin j → Finset ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  ∑ h ∈ H, ‖quadraticSum (centeredSet N) (3*α*A*(∏ l, h l)) t‖ *
    ∏ l, ‖coefficientSum p (C l) ((4*α*A*(∏ l, h l))*(h l)^2)‖

/-- The r=0 case has no differencing loss. The same common-t parity
completion applies to its already-quadratic original polynomial. -/
theorem cartesian_k8_j6_completed_bound (H : Finset (Fin 6 → ℝ))
    (C : Fin 6 → Finset ℝ) (α : ℝ) (N Q : ℕ) (hN : 0 < N) (hQN : Q ≤ N)
    (hC : ∀ l, ∀ m ∈ C l, m ≠ 0) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ t ∈ Set.Icc (0:ℝ) 1, zeroProducts 16 107520 α H C N t ≤ B) :
    ‖polynomialFamily 8 (cartesianParameters H C) Prod.fst Prod.snd α 1 Q‖ ≤
      completionLoss N*B := by
  rw [family_k8_j6_quadratic_identity (cartesianParameters H C) Prod.fst Prod.snd α 1 Q
    (coefficient_tuple_nonzero H C hC)]
  simp only [cartesianParameters, Finset.sum_product]
  have Hbound := completed_product_bound H 16 107520 α
    (fun h => ∏ l, h l) (fun _ => 0) (fun _ => C) id
    (fun _ => 2) (fun _ => 2*(Q:ℤ)) (fun _ => 0) (centeredSet N) (2*N) (by omega)
    (by intro h hh; have := parityInterval_length_le N Q 0 hQN (by omega); simpa using this)
    (by intro h hh; have := parityInterval_subset_centered N Q 0 hQN (by omega)
        simpa only [parityInterval, mul_one, sub_zero, add_zero] using this)
    B hB0 hB
  simpa only [parityInterval, mul_one, add_zero, completionLoss, Nat.cast_mul, Nat.cast_ofNat, id_eq] using Hbound

#print axioms reducedFirst_completed_bound
#print axioms reducedSecond_completed_bound
#print axioms cartesian_k8_j4_completed_bound
#print axioms cartesian_k8_j5_completed_bound
#print axioms cartesian_k8_j6_completed_bound
#print axioms cartesian_k9_j5_completed_bound
#print axioms cartesian_k9_j6_completed_bound

end Waring.CartesianPolynomialBounds
