import Waring.CartesianResourceMoments

/-!
# Exact cast and ordinary-shift adapters for finite resource averages

The analytic cap theorem uses real h tuples and integer ordinary shifts.
The multiplicity theorem uses positive natural tuples. These are exactly
the same finite averages after the injective casts and Cartesian regrouping
proved here; no moment or cardinality comparison is assumed.
-/

noncomputable section
open scoped BigOperators
namespace Waring.CartesianMomentAdapters
open CartesianProductSampling CartesianResourceMoments ProductMultiplicity
open FiniteResourceHolder ResourceDifferencingCap CoefficientFactorization

def realTuple {j : ℕ} (h : Fin j → ℕ) : Fin j → ℝ := fun i => (h i:ℝ)
def realBox {j : ℕ} (bounds : Fin j → ℕ) : Finset (Fin j → ℝ) :=
  (positiveBox bounds).image realTuple

theorem realTuple_injective {j : ℕ} : Function.Injective (@realTuple j) := by
  intro h g heq
  funext i
  have hi := congrFun heq i
  dsimp [realTuple] at hi
  exact_mod_cast hi

theorem realBox_card {j : ℕ} (bounds : Fin j → ℕ) :
    (realBox bounds).card = tupleProduct bounds := by
  rw [realBox, Finset.card_image_of_injective _ realTuple_injective, positiveBox_card]

theorem sum_realBox {j : ℕ} (bounds : Fin j → ℕ) (F : (Fin j → ℝ) → ℝ) :
    (∑ h ∈ realBox bounds, F h) = ∑ h ∈ positiveBox bounds, F (realTuple h) := by
  exact Finset.sum_image (fun _ _ _ _ heq => realTuple_injective heq)

theorem average_finset {σ : Type*} (s : Finset σ) (F : σ → ℝ) :
    average (fun x : s => F x) = (∑ x ∈ s, F x)/(s.card:ℝ) := by
  unfold average
  rw [Fintype.card_coe]
  congr 1
  exact Finset.sum_attach s F

theorem sum_int_Icc_nat (N : ℕ) (F : ℤ → ℝ) :
    (∑ u ∈ Finset.Icc (1:ℤ) (N:ℤ), F u) = ∑ u ∈ Finset.Icc 1 N, F (u:ℤ) := by
  symm
  apply Finset.sum_bij (fun (u : ℕ) _ => (u:ℤ))
  · intro u hu
    have hh := Finset.mem_Icc.mp hu
    exact Finset.mem_Icc.mpr ⟨by exact_mod_cast hh.1,by exact_mod_cast hh.2⟩
  · intro u hu v hv heq
    exact_mod_cast heq
  · intro z hz
    have hh := Finset.mem_Icc.mp hz
    have hz0 : 0 ≤ z := by omega
    refine ⟨z.toNat, Finset.mem_Icc.mpr ⟨by omega,by omega⟩, ?_⟩
    exact Int.toNat_of_nonneg hz0
  · intro u hu
    rfl

theorem first_sum_transport {j : ℕ} (bounds : Fin j → ℕ) (N : ℕ)
    (F : (Fin j → ℝ) → ℤ → ℝ) :
    (∑ h ∈ realBox bounds, ∑ u ∈ Finset.Icc (1:ℤ) (N:ℤ), F h u) =
      ∑ x ∈ positiveBox (Fin.cons N bounds), F (realTuple (fun i => x i.succ)) (x 0:ℤ) := by
  rw [positiveBox_sum_head_tail (Fin.cons N bounds) (fun u h => F (realTuple h) (u:ℤ))]
  simp only [Fin.cons_zero, Fin.cons_succ]
  rw [sum_realBox bounds (fun h => ∑ u ∈ Finset.Icc (1:ℤ) (N:ℤ), F h u)]
  simp_rw [sum_int_Icc_nat]
  exact Finset.sum_comm

theorem second_sum_transport {j : ℕ} (bounds : Fin j → ℕ) (N : ℕ)
    (F : (Fin j → ℝ) → ℤ → ℤ → ℝ) :
    (∑ h ∈ realBox bounds, ∑ u ∈ Finset.Icc (1:ℤ) (N:ℤ),
      ∑ v ∈ Finset.Icc (1:ℤ) (N:ℤ), F h u v) =
      ∑ x ∈ positiveBox (Fin.cons N (Fin.cons N bounds)),
        F (realTuple (fun i => x i.succ.succ)) (x 0:ℤ) (x 1:ℤ) := by
  have hhead := positiveBox_sum_head_tail (Fin.cons N (Fin.cons N bounds))
    (fun u y => F (realTuple (fun i => y i.succ)) (u:ℤ) (y 0:ℤ))
  simp only [Fin.succ_zero_eq_one] at hhead
  rw [hhead]
  simp only [Fin.cons_zero, Fin.cons_succ]
  rw [sum_realBox bounds (fun h => ∑ u ∈ Finset.Icc (1:ℤ) (N:ℤ),
    ∑ v ∈ Finset.Icc (1:ℤ) (N:ℤ), F h u v)]
  simp_rw [sum_int_Icc_nat]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  rw [positiveBox_sum_head_tail (Fin.cons N bounds) (fun v h => F (realTuple h) (u:ℤ) (v:ℤ))]
  simp only [Fin.cons_zero, Fin.cons_succ]
  exact Finset.sum_comm

theorem first_average_transport {j : ℕ} (bounds : Fin j → ℕ) (N : ℕ)
    (F : (Fin j → ℝ) → ℤ → ℝ) :
    average (fun x : realBox bounds ×ˢ Finset.Icc (1:ℤ) (N:ℤ) => F x.val.1 x.val.2) =
      average (fun x : positiveBox (Fin.cons N bounds) =>
        F (realTuple (fun i => x.val i.succ)) (x.val 0:ℤ)) := by
  rw [average_finset (realBox bounds ×ˢ Finset.Icc (1:ℤ) (N:ℤ))
      (fun (x : (Fin j → ℝ) × ℤ) => F x.1 x.2),
    average_positiveBox (Fin.cons N bounds) (fun x => F (realTuple (fun i => x i.succ)) (x 0:ℤ)),
    Finset.sum_product, first_sum_transport bounds N F]
  have hc : (Finset.Icc (1:ℤ) (N:ℤ)).card=N := by rw [Int.card_Icc]; omega
  rw [Finset.card_product, realBox_card, hc]
  simp only [tupleProduct, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Nat.cast_mul, mul_comm]

theorem second_average_transport {j : ℕ} (bounds : Fin j → ℕ) (N : ℕ)
    (F : (Fin j → ℝ) → ℤ → ℤ → ℝ) :
    average (fun x : (realBox bounds ×ˢ Finset.Icc (1:ℤ) (N:ℤ)) ×ˢ Finset.Icc (1:ℤ) (N:ℤ) =>
      F x.val.1.1 x.val.1.2 x.val.2) =
      average (fun x : positiveBox (Fin.cons N (Fin.cons N bounds)) =>
        F (realTuple (fun i => x.val i.succ.succ)) (x.val 0:ℤ) (x.val 1:ℤ)) := by
  rw [average_finset ((realBox bounds ×ˢ Finset.Icc (1:ℤ) (N:ℤ)) ×ˢ Finset.Icc (1:ℤ) (N:ℤ))
      (fun (x : ((Fin j → ℝ) × ℤ) × ℤ) => F x.1.1 x.1.2 x.2),
    average_positiveBox (Fin.cons N (Fin.cons N bounds))
      (fun x => F (realTuple (fun i => x i.succ.succ)) (x 0:ℤ) (x 1:ℤ))]
  simp only [Finset.sum_product]
  rw [second_sum_transport bounds N F]
  have hc : (Finset.Icc (1:ℤ) (N:ℤ)).card=N := by rw [Int.card_Icc]; omega
  simp only [Finset.card_product, realBox_card, hc, tupleProduct, Fin.prod_univ_succ,
    Fin.cons_zero, Fin.cons_succ, Nat.cast_mul]
  congr 1
  ring

def realCoefficientSets {j : ℕ} (C : Fin j → Finset ℕ) : Fin j → Finset ℝ :=
  fun i => (C i).image (fun m : ℕ => (m:ℝ))

/-- Exact first-difference quadratic resource average on the natural tuple box. -/
theorem first_quadratic_moment_eq {j : ℕ} (bounds : Fin j → ℕ) (N p A q : ℕ)
    (C : Fin j → Finset ℝ) (V : Fin j → ℝ) (α t : ℝ) :
    average (fun x : realBox bounds ×ˢ Finset.Icc (1:ℤ) (N:ℤ) =>
      (firstFactors p (A:ℝ) α C N V t none x.val)^q) =
      quadraticBoxMoment (Fin.cons N bounds) (CartesianPolynomialBounds.centeredSet N)
        (4*(N:ℝ)+1) α t (3*A) q := by
  calc
    _ = average (fun x : positiveBox (Fin.cons N bounds) =>
        (firstFactors p (A:ℝ) α C N V t none (realTuple (fun i => x.val i.succ),(x.val 0:ℤ)))^q) :=
      first_average_transport bounds N (fun h u => (firstFactors p (A:ℝ) α C N V t none (h,u))^q)
    _ = _ := by
      unfold quadraticBoxMoment
      apply congrArg (fun f : positiveBox (Fin.cons N bounds) → ℝ => average f)
      funext x
      dsimp only [firstFactors, PolynomialResourceBounds.normalizedFactor,
        PolynomialResourceBounds.actualFactor, sourceCaps]
      have hp : 3*α*(A:ℝ)*((∏ l, realTuple (fun i => x.val i.succ) l)*((x.val 0:ℤ):ℝ)) =
          ((3*A:ℕ):ℝ)*((tupleProduct x.val:ℝ)*α) := by
        simp only [realTuple, tupleProduct, Fin.prod_univ_succ,
          Nat.cast_mul, Nat.cast_prod, Int.cast_natCast, Nat.cast_ofNat]
        ring
      exact congrArg (fun β : ℝ =>
        (‖quadraticSum (CartesianPolynomialBounds.centeredSet N) β t‖/(4*(N:ℝ)+1))^q) hp

/-- Exact first-difference coefficient resource average. Its distinguished
coordinate is the original h_i, after the ordinary-shift coordinates. -/
theorem first_coefficient_moment_eq {j : ℕ} (bounds : Fin j → ℕ) (N p A power : ℕ)
    (C : Fin j → Finset ℕ) (V : Fin j → ℝ) (α t : ℝ) (i : Fin j) :
    average (fun x : realBox bounds ×ˢ Finset.Icc (1:ℤ) (N:ℤ) =>
      (firstFactors p (A:ℝ) α (realCoefficientSets C) N V t (some i) x.val)^(2*power)) =
      coefficientBoxMomentAt (Fin.cons N bounds) i.succ (C i) p power (V i) (((4*A:ℕ):ℝ)*α) := by
  calc
    _ = average (fun x : positiveBox (Fin.cons N bounds) =>
        (firstFactors p (A:ℝ) α (realCoefficientSets C) N V t (some i) (realTuple (fun i => x.val i.succ),(x.val 0:ℤ)))^(2*power)) :=
      first_average_transport bounds N
        (fun h u => (firstFactors p (A:ℝ) α (realCoefficientSets C) N V t (some i) (h,u))^(2*power))
    _ = _ := by
      unfold coefficientBoxMomentAt
      apply congrArg (fun f : positiveBox (Fin.cons N bounds) → ℝ => average f)
      funext x
      dsimp only [firstFactors, PolynomialResourceBounds.normalizedFactor,
        PolynomialResourceBounds.actualFactor, sourceCaps, realCoefficientSets]
      rw [CartesianPolynomialBounds.coefficientSum_nat_image]
      have hp : (4*α*(A:ℝ)*((∏ l, realTuple (fun i => x.val i.succ) l)*((x.val 0:ℤ):ℝ)))*(realTuple (fun i => x.val i.succ) i)^2 =
          (((4*A:ℕ):ℝ)*α)*(tupleProduct x.val:ℝ)*(x.val i.succ:ℝ)^2 := by
        simp only [realTuple, tupleProduct, Fin.prod_univ_succ,
          Nat.cast_mul, Nat.cast_prod, Int.cast_natCast, Nat.cast_ofNat]
        ring
      exact congrArg (fun β : ℝ => (‖CoefficientPower.coefficientWeyl (C i) p β‖/(V i))^(2*power)) hp

/-- Exact second-difference quadratic resource average on the natural tuple box. -/
theorem second_quadratic_moment_eq {j : ℕ} (bounds : Fin j → ℕ) (N p A q : ℕ)
    (C : Fin j → Finset ℝ) (V : Fin j → ℝ) (α t : ℝ) :
    average (fun x : (realBox bounds ×ˢ Finset.Icc (1:ℤ) (N:ℤ)) ×ˢ Finset.Icc (1:ℤ) (N:ℤ) =>
      (secondFactors p (A:ℝ) α C N V t none x.val)^q) =
      quadraticBoxMoment (Fin.cons N (Fin.cons N bounds)) (CartesianPolynomialBounds.centeredSet N)
        (4*(N:ℝ)+1) α t (3*A) q := by
  calc
    _ = average (fun x : positiveBox (Fin.cons N (Fin.cons N bounds)) =>
        (secondFactors p (A:ℝ) α C N V t none ((realTuple (fun i => x.val i.succ.succ),(x.val 0:ℤ)),(x.val 1:ℤ)))^q) :=
      second_average_transport bounds N (fun h u v => (secondFactors p (A:ℝ) α C N V t none ((h,u),v))^q)
    _ = _ := by
      unfold quadraticBoxMoment
      apply congrArg (fun f : positiveBox (Fin.cons N (Fin.cons N bounds)) → ℝ => average f)
      funext x
      dsimp only [secondFactors, PolynomialResourceBounds.normalizedFactor,
        PolynomialResourceBounds.actualFactor, sourceCaps]
      have hp : 3*α*(A:ℝ)*((∏ l, realTuple (fun i => x.val i.succ.succ) l)*((x.val 0:ℤ):ℝ)*((x.val 1:ℤ):ℝ)) =
          ((3*A:ℕ):ℝ)*((tupleProduct x.val:ℝ)*α) := by
        simp only [realTuple, tupleProduct, Fin.prod_univ_succ, Fin.succ_zero_eq_one,
          Nat.cast_mul, Nat.cast_prod, Int.cast_natCast, Nat.cast_ofNat]
        ring
      exact congrArg (fun β : ℝ =>
        (‖quadraticSum (CartesianPolynomialBounds.centeredSet N) β t‖/(4*(N:ℝ)+1))^q) hp

/-- Exact second-difference coefficient resource average. Its distinguished
coordinate is the original h_i, after the ordinary-shift coordinates. -/
theorem second_coefficient_moment_eq {j : ℕ} (bounds : Fin j → ℕ) (N p A power : ℕ)
    (C : Fin j → Finset ℕ) (V : Fin j → ℝ) (α t : ℝ) (i : Fin j) :
    average (fun x : (realBox bounds ×ˢ Finset.Icc (1:ℤ) (N:ℤ)) ×ˢ Finset.Icc (1:ℤ) (N:ℤ) =>
      (secondFactors p (A:ℝ) α (realCoefficientSets C) N V t (some i) x.val)^(2*power)) =
      coefficientBoxMomentAt (Fin.cons N (Fin.cons N bounds)) i.succ.succ (C i) p power (V i) (((4*A:ℕ):ℝ)*α) := by
  calc
    _ = average (fun x : positiveBox (Fin.cons N (Fin.cons N bounds)) =>
        (secondFactors p (A:ℝ) α (realCoefficientSets C) N V t (some i) ((realTuple (fun i => x.val i.succ.succ),(x.val 0:ℤ)),(x.val 1:ℤ)))^(2*power)) :=
      second_average_transport bounds N
        (fun h u v => (secondFactors p (A:ℝ) α (realCoefficientSets C) N V t (some i) ((h,u),v))^(2*power))
    _ = _ := by
      unfold coefficientBoxMomentAt
      apply congrArg (fun f : positiveBox (Fin.cons N (Fin.cons N bounds)) → ℝ => average f)
      funext x
      dsimp only [secondFactors, PolynomialResourceBounds.normalizedFactor,
        PolynomialResourceBounds.actualFactor, sourceCaps, realCoefficientSets]
      rw [CartesianPolynomialBounds.coefficientSum_nat_image]
      have hp : (4*α*(A:ℝ)*((∏ l, realTuple (fun i => x.val i.succ.succ) l)*((x.val 0:ℤ):ℝ)*((x.val 1:ℤ):ℝ)))*(realTuple (fun i => x.val i.succ.succ) i)^2 =
          (((4*A:ℕ):ℝ)*α)*(tupleProduct x.val:ℝ)*(x.val i.succ.succ:ℝ)^2 := by
        simp only [realTuple, tupleProduct, Fin.prod_univ_succ, Fin.succ_zero_eq_one,
          Nat.cast_mul, Nat.cast_prod, Int.cast_natCast, Nat.cast_ofNat]
        ring
      exact congrArg (fun β : ℝ => (‖CoefficientPower.coefficientWeyl (C i) p β‖/(V i))^(2*power)) hp

theorem zero_average_transport {j : ℕ} (bounds : Fin j → ℕ) (F : (Fin j → ℝ) → ℝ) :
    average (fun x : realBox bounds => F x.val) =
      average (fun x : positiveBox bounds => F (realTuple x.val)) := by
  rw [average_finset (realBox bounds) F,
    average_positiveBox bounds (fun x => F (realTuple x)), realBox_card, sum_realBox]

theorem zero_quadratic_moment_eq {j : ℕ} (bounds : Fin j → ℕ) (N p A q : ℕ)
    (C : Fin j → Finset ℝ) (V : Fin j → ℝ) (α t : ℝ) :
    average (fun x : realBox bounds => (zeroFactors p (A:ℝ) α C N V t none x.val)^q) =
      quadraticBoxMoment bounds (CartesianPolynomialBounds.centeredSet N)
        (4*(N:ℝ)+1) α t (3*A) q := by
  calc
    _ = average (fun x : positiveBox bounds =>
        (zeroFactors p (A:ℝ) α C N V t none (realTuple x.val))^q) :=
      zero_average_transport bounds (fun h => (zeroFactors p (A:ℝ) α C N V t none h)^q)
    _ = _ := by
      unfold quadraticBoxMoment
      apply congrArg (fun f : positiveBox bounds → ℝ => average f)
      funext x
      dsimp only [zeroFactors, PolynomialResourceBounds.normalizedFactor,
        PolynomialResourceBounds.actualFactor, sourceCaps]
      have hp : 3*α*(A:ℝ)*(∏ l, realTuple x.val l) =
          ((3*A:ℕ):ℝ)*((tupleProduct x.val:ℝ)*α) := by
        simp only [realTuple, tupleProduct, Nat.cast_mul, Nat.cast_prod, Nat.cast_ofNat]
        ring
      exact congrArg (fun β : ℝ =>
        (‖quadraticSum (CartesianPolynomialBounds.centeredSet N) β t‖/(4*(N:ℝ)+1))^q) hp

theorem zero_coefficient_moment_eq {j : ℕ} (bounds : Fin (j+1) → ℕ) (N p A power : ℕ)
    (C : Fin (j+1) → Finset ℕ) (V : Fin (j+1) → ℝ) (α t : ℝ) (i : Fin (j+1)) :
    average (fun x : realBox bounds =>
      (zeroFactors p (A:ℝ) α (realCoefficientSets C) N V t (some i) x.val)^(2*power)) =
      coefficientBoxMomentAt bounds i (C i) p power (V i) (((4*A:ℕ):ℝ)*α) := by
  calc
    _ = average (fun x : positiveBox bounds =>
        (zeroFactors p (A:ℝ) α (realCoefficientSets C) N V t (some i) (realTuple x.val))^(2*power)) :=
      zero_average_transport bounds
        (fun h => (zeroFactors p (A:ℝ) α (realCoefficientSets C) N V t (some i) h)^(2*power))
    _ = _ := by
      unfold coefficientBoxMomentAt
      apply congrArg (fun f : positiveBox bounds → ℝ => average f)
      funext x
      dsimp only [zeroFactors, PolynomialResourceBounds.normalizedFactor,
        PolynomialResourceBounds.actualFactor, sourceCaps, realCoefficientSets]
      rw [CartesianPolynomialBounds.coefficientSum_nat_image]
      have hp : (4*α*(A:ℝ)*(∏ l, realTuple x.val l))*(realTuple x.val i)^2 =
          (((4*A:ℕ):ℝ)*α)*(tupleProduct x.val:ℝ)*(x.val i:ℝ)^2 := by
        simp only [realTuple, tupleProduct, Nat.cast_mul, Nat.cast_prod, Nat.cast_ofNat]
        ring
      exact congrArg (fun β : ℝ => (‖CoefficientPower.coefficientWeyl (C i) p β‖/(V i))^(2*power)) hp

#print axioms zero_average_transport
#print axioms zero_quadratic_moment_eq
#print axioms zero_coefficient_moment_eq
#print axioms first_average_transport
#print axioms second_average_transport
#print axioms first_quadratic_moment_eq
#print axioms second_quadratic_moment_eq
#print axioms first_coefficient_moment_eq
#print axioms second_coefficient_moment_eq

end Waring.CartesianMomentAdapters
