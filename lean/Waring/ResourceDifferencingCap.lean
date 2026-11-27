import Waring.PolynomialResourceBounds

/-!
# Finite resource moments through completion and the diagonal cap

Resource data have their literal finite-average semantics. The original
parameter tuple remains Cartesian through the exact polynomial reduction.
All constants from centered completion and ordinary differencing are kept.
-/

noncomputable section
open scoped BigOperators
namespace Waring.ResourceDifferencingCap
open PolynomialSumReduction CartesianPolynomialBounds PolynomialResourceBounds
open CoefficientFactorization FiniteResourceHolder UnseparatedDifferencing Differences

structure Allocation (j : ℕ) (ρ : Type*) [Fintype ρ] where
  factor : ρ → Option (Fin j)
  order : ρ → ℝ
  weight : ρ → ℝ
  constant : ρ → ℝ
  saving : ρ → ℝ
  order_nonneg : ∀ r, 0 ≤ order r
  weight_nonneg : ∀ r, 0 ≤ weight r
  constant_nonneg : ∀ r, 0 ≤ constant r
  mass_le : ∑ r, weight r ≤ 1
  load_le : ∀ i, ∑ r ∈ Finset.univ.filter (fun r => factor r=i), order r*weight r ≤ 1

def Allocation.totalSaving {j ρ} [Fintype ρ] (R : Allocation j ρ) : ℝ :=
  ∑ r, R.weight r*R.saving r

def Allocation.totalConstant {j ρ} [Fintype ρ] (R : Allocation j ρ) : ℝ :=
  ∏ r, (R.constant r)^(R.weight r)

def Allocation.HasMoments {j ρ σ} [Fintype ρ] [Fintype σ]
    (R : Allocation j ρ) (P : ℝ) (f : Option (Fin j) → σ → ℝ) : Prop :=
  ∀ r, average (fun x => (f (R.factor r) x)^(R.order r)) ≤ R.constant r*P^(-R.saving r)

theorem Allocation.totalConstant_nonneg {j ρ} [Fintype ρ] (R : Allocation j ρ) :
    0 ≤ R.totalConstant :=
  Finset.prod_nonneg (fun r _ => Real.rpow_nonneg (R.constant_nonneg r) _)

def sourceCaps {j : ℕ} (N : ℕ) (V : Fin j → ℝ) : Option (Fin j) → ℝ
  | none => 4*(N:ℝ)+1
  | some i => V i

def parameterScale {j : ℕ} (H : Finset (Fin j → ℝ)) (V : Fin j → ℝ) : ℝ :=
  (H.card:ℝ)*∏ i, V i

def firstFactors {j : ℕ} (p : ℕ) (A α : ℝ) (C : Fin j → Finset ℝ)
    (N : ℕ) (V : Fin j → ℝ) (t : ℝ) :=
  normalizedFactor p (centeredSet N) C
    (fun hu : (Fin j → ℝ) × ℤ => 3*α*A*((∏ l, hu.1 l)*(hu.2:ℝ)))
    (fun l hu => (4*α*A*((∏ l', hu.1 l')*(hu.2:ℝ)))*(hu.1 l)^2)
    t (sourceCaps N V)

def secondFactors {j : ℕ} (p : ℕ) (A α : ℝ) (C : Fin j → Finset ℝ)
    (N : ℕ) (V : Fin j → ℝ) (t : ℝ) :=
  normalizedFactor p (centeredSet N) C
    (fun huv : ((Fin j → ℝ) × ℤ) × ℤ =>
      3*α*A*((∏ l, huv.1.1 l)*(huv.1.2:ℝ)*(huv.2:ℝ)))
    (fun l huv => (4*α*A*((∏ l', huv.1.1 l')*(huv.1.2:ℝ)*(huv.2:ℝ)))*(huv.1.1 l)^2)
    t (sourceCaps N V)

theorem centeredSet_card (N : ℕ) : (centeredSet N).card = 4*N+1 := by
  rw [centeredSet, Int.card_Icc]
  omega

theorem sourceCaps_pos {j : ℕ} (N : ℕ) (V : Fin j → ℝ) (hV : ∀ i, 0 < V i)
    (i : Option (Fin j)) : 0 < sourceCaps N V i := by
  cases i with
  | none => dsimp [sourceCaps]; positivity
  | some i => exact hV i

theorem parameterScale_nonneg {j : ℕ} (H : Finset (Fin j → ℝ)) (V : Fin j → ℝ)
    (hV : ∀ i, 0 ≤ V i) : 0 ≤ parameterScale H V :=
  mul_nonneg (by positivity) (Finset.prod_nonneg (fun i _ => hV i))

theorem parameter_card_le_scale {j : ℕ} (H : Finset (Fin j → ℝ))
    (C : Fin j → Finset ℝ) (V : Fin j → ℝ) (hC : ∀ i, ((C i).card:ℝ) ≤ V i) :
    ((cartesianParameters H C).card:ℝ) ≤ parameterScale H V := by
  rw [cartesianParameters_card, Nat.cast_mul, Nat.cast_prod]
  exact mul_le_mul_of_nonneg_left
    (Finset.prod_le_prod (fun i _ => by positivity) (fun i _ => hC i)) (by positivity)

theorem completionLoss_nonneg (N : ℕ) (hN : 0 < N) : 0 ≤ completionLoss N := by
  have hNR : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hl := Real.log_nonneg (show (1:ℝ) ≤ 2*(N:ℝ) by linarith)
  have h2 := Real.log_pos (show (1:ℝ) < 2 by norm_num)
  unfold completionLoss
  positivity

def Allocation.effectiveConstant {j ρ} [Fintype ρ] (R : Allocation j ρ) (N : ℕ) : ℝ :=
  5*completionLoss N*R.totalConstant

theorem Allocation.effectiveConstant_nonneg {j ρ} [Fintype ρ]
    (R : Allocation j ρ) (N : ℕ) (hN : 0 < N) : 0 ≤ R.effectiveConstant N :=
  mul_nonneg (mul_nonneg (by norm_num) (completionLoss_nonneg N hN)) R.totalConstant_nonneg

theorem firstProducts_resource_bound {j ρ} [Fintype ρ]
    (R : Allocation j ρ) (p : ℕ) (A α : ℝ) (H : Finset (Fin j → ℝ))
    (hH : H.Nonempty) (C : Fin j → Finset ℝ) (N : ℕ) (hN : 0 < N)
    (V : Fin j → ℝ) (hV : ∀ i, 0 < V i) (hC : ∀ i, ((C i).card:ℝ) ≤ V i)
    (t : ℝ) (hmom : R.HasMoments (N:ℝ)
      (fun i (x : H ×ˢ Finset.Icc (1:ℤ) (N:ℤ)) => firstFactors p A α C N V t i x)) :
    firstProducts p A α H C N t ≤
      5*(N:ℝ)^2*parameterScale H V*R.totalConstant*(N:ℝ)^(-R.totalSaving) := by
  have hNR : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : 0 < (N:ℝ) := by exact_mod_cast hN
  have hs : (H ×ˢ Finset.Icc (1:ℤ) (N:ℤ)).Nonempty :=
    ⟨(hH.choose,1), Finset.mem_product.mpr ⟨hH.choose_spec, Finset.mem_Icc.mpr ⟨le_rfl,by omega⟩⟩⟩
  have Hbound := finite_product_resource_saving (H ×ˢ Finset.Icc (1:ℤ) (N:ℤ)) hs
    p (centeredSet N) C
    (fun hu => 3*α*A*((∏ l, hu.1 l)*(hu.2:ℝ)))
    (fun l hu => (4*α*A*((∏ l', hu.1 l')*(hu.2:ℝ)))*(hu.1 l)^2) t
    (sourceCaps N V) (sourceCaps_pos N V hV)
    (by simp only [centeredSet_card, sourceCaps, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, le_refl])
    hC R.factor R.order R.weight R.order_nonneg R.weight_nonneg R.mass_le R.load_le
    N hNpos R.constant R.saving R.constant_nonneg hmom
  have hc : (Finset.Icc (1:ℤ) (N:ℤ)).card = N := by rw [Int.card_Icc]; omega
  have hZ : 4*(N:ℝ)+1 ≤ 5*(N:ℝ) := by linarith
  have hm := mul_le_mul_of_nonneg_left hZ
    (show 0 ≤ (H.card:ℝ)*(N:ℝ)*(∏ i, V i)*R.totalConstant*(N:ℝ)^(-R.totalSaving) from
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hNpos.le)
        (Finset.prod_nonneg (fun i _ => (hV i).le))) R.totalConstant_nonneg)
        (Real.rpow_nonneg hNpos.le _))
  simp only [Finset.card_product, hc, Nat.cast_mul, Fintype.prod_option, sourceCaps] at Hbound
  change firstProducts p A α H C N t ≤ _ at Hbound
  unfold Allocation.totalConstant Allocation.totalSaving parameterScale at *
  exact Hbound.trans (by convert hm using 1 <;> ring)

theorem secondProducts_resource_bound {j ρ} [Fintype ρ]
    (R : Allocation j ρ) (p : ℕ) (A α : ℝ) (H : Finset (Fin j → ℝ))
    (hH : H.Nonempty) (C : Fin j → Finset ℝ) (N : ℕ) (hN : 0 < N)
    (V : Fin j → ℝ) (hV : ∀ i, 0 < V i) (hC : ∀ i, ((C i).card:ℝ) ≤ V i)
    (t : ℝ) (hmom : R.HasMoments (N:ℝ)
      (fun i (x : (H ×ˢ Finset.Icc (1:ℤ) (N:ℤ)) ×ˢ Finset.Icc (1:ℤ) (N:ℤ)) =>
        secondFactors p A α C N V t i x)) :
    secondProducts p A α H C N t ≤
      5*(N:ℝ)^3*parameterScale H V*R.totalConstant*(N:ℝ)^(-R.totalSaving) := by
  have hNR : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : 0 < (N:ℝ) := by exact_mod_cast hN
  have hs : ((H ×ˢ Finset.Icc (1:ℤ) (N:ℤ)) ×ˢ Finset.Icc (1:ℤ) (N:ℤ)).Nonempty :=
    ⟨((hH.choose,1),1), Finset.mem_product.mpr ⟨Finset.mem_product.mpr
      ⟨hH.choose_spec, Finset.mem_Icc.mpr ⟨le_rfl,by dsimp; omega⟩⟩,
      Finset.mem_Icc.mpr ⟨le_rfl,by dsimp; omega⟩⟩⟩
  have Hbound := finite_product_resource_saving
    ((H ×ˢ Finset.Icc (1:ℤ) (N:ℤ)) ×ˢ Finset.Icc (1:ℤ) (N:ℤ)) hs p (centeredSet N) C
    (fun huv => 3*α*A*((∏ l, huv.1.1 l)*(huv.1.2:ℝ)*(huv.2:ℝ)))
    (fun l huv => (4*α*A*((∏ l', huv.1.1 l')*(huv.1.2:ℝ)*(huv.2:ℝ)))*(huv.1.1 l)^2) t
    (sourceCaps N V) (sourceCaps_pos N V hV)
    (by simp only [centeredSet_card, sourceCaps, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, le_refl])
    hC R.factor R.order R.weight R.order_nonneg R.weight_nonneg R.mass_le R.load_le
    N hNpos R.constant R.saving R.constant_nonneg hmom
  have hc : (Finset.Icc (1:ℤ) (N:ℤ)).card = N := by rw [Int.card_Icc]; omega
  have hZ : 4*(N:ℝ)+1 ≤ 5*(N:ℝ) := by linarith
  have hm := mul_le_mul_of_nonneg_left hZ
    (show 0 ≤ (H.card:ℝ)*(N:ℝ)^2*(∏ i, V i)*R.totalConstant*(N:ℝ)^(-R.totalSaving) from
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (sq_nonneg _))
        (Finset.prod_nonneg (fun i _ => (hV i).le))) R.totalConstant_nonneg)
        (Real.rpow_nonneg hNpos.le _))
  simp only [Finset.card_product, hc, Nat.cast_mul, Fintype.prod_option, sourceCaps] at Hbound
  change secondProducts p A α H C N t ≤ _ at Hbound
  unfold Allocation.totalConstant Allocation.totalSaving parameterScale at *
  exact Hbound.trans (by convert hm using 1 <;> ring)

theorem first_reduced_resource_bound {j ρ} [Fintype ρ]
    (R : Allocation j ρ) (p : ℕ) (A α : ℝ) (H : Finset (Fin j → ℝ))
    (hH : H.Nonempty) (C : Fin j → Finset ℝ) (N Q : ℕ) (hN : 0 < N) (hQN : Q ≤ N)
    (V : Fin j → ℝ) (hV : ∀ i, 0 < V i) (hC : ∀ i, ((C i).card:ℝ) ≤ V i)
    (hmom : ∀ t ∈ Set.Icc (0:ℝ) 1, R.HasMoments (N:ℝ)
      (fun i (x : H ×ˢ Finset.Icc (1:ℤ) (N:ℤ)) => firstFactors p A α C N V t i x)) :
    ‖reducedFirstSum p A (cartesianParameters H C) Prod.fst Prod.snd α 1 Q N‖ ≤
      R.effectiveConstant N*(N:ℝ)^2*parameterScale H V*(N:ℝ)^(-R.totalSaving) := by
  have HB0 : 0 ≤ 5*(N:ℝ)^2*parameterScale H V*R.totalConstant*(N:ℝ)^(-R.totalSaving) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by positivity)
      (parameterScale_nonneg H V (fun i => (hV i).le))) R.totalConstant_nonneg)
      (Real.rpow_nonneg (by positivity) _)
  have HG := reducedFirst_completed_bound p A α H C N Q hN hQN _ HB0
    (fun t ht => firstProducts_resource_bound R p A α H hH C N hN V hV hC t (hmom t ht))
  exact HG.trans_eq (by unfold Allocation.effectiveConstant; ring)

theorem second_reduced_resource_bound {j ρ} [Fintype ρ]
    (R : Allocation j ρ) (p : ℕ) (A α : ℝ) (H : Finset (Fin j → ℝ))
    (hH : H.Nonempty) (C : Fin j → Finset ℝ) (N Q : ℕ) (hN : 0 < N) (hQN : Q ≤ N)
    (V : Fin j → ℝ) (hV : ∀ i, 0 < V i) (hC : ∀ i, ((C i).card:ℝ) ≤ V i)
    (hmom : ∀ t ∈ Set.Icc (0:ℝ) 1, R.HasMoments (N:ℝ)
      (fun i (x : (H ×ˢ Finset.Icc (1:ℤ) (N:ℤ)) ×ˢ Finset.Icc (1:ℤ) (N:ℤ)) =>
        secondFactors p A α C N V t i x)) :
    ‖reducedSecondSum p A (cartesianParameters H C) Prod.fst Prod.snd α 1 Q N‖ ≤
      R.effectiveConstant N*(N:ℝ)^3*parameterScale H V*(N:ℝ)^(-R.totalSaving) := by
  have HB0 : 0 ≤ 5*(N:ℝ)^3*parameterScale H V*R.totalConstant*(N:ℝ)^(-R.totalSaving) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by positivity)
      (parameterScale_nonneg H V (fun i => (hV i).le))) R.totalConstant_nonneg)
      (Real.rpow_nonneg (by positivity) _)
  have HG := reducedSecond_completed_bound p A α H C N Q hN hQN _ HB0
    (fun t ht => secondProducts_resource_bound R p A α H hH C N hN V hV hC t (hmom t ht))
  exact HG.trans_eq (by unfold Allocation.effectiveConstant; ring)

/-- Scalar diagonal/root calculation for the actual one-difference shape. -/
theorem first_scalar_cap {F G B K P S : ℝ} (hF : 0 ≤ F) (hB : 0 ≤ B)
    (hK : 0 ≤ K) (hP : 1 ≤ P)
    (hfirst : F^2 ≤ P*B^2+2*B*G) (hG : G ≤ K*P^2*B*P^(-S)) :
    F ≤ (2*(1+2*K))^((2:ℝ)⁻¹)*(P*B)*P^(-min 1 S/2) := by
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hstep : F^2 ≤ P*B^2+2*B*(K*P^2*B*P^(-S)) :=
    hfirst.trans (add_le_add_left (mul_le_mul_of_nonneg_left hG (by positivity)) _)
  have hid : P*B^2+2*B*(K*P^2*B*P^(-S)) =
      (P*B)^2*(P^(-1:ℝ)+2*K*P^(-S)) := by
    rw [Real.rpow_neg_one]
    field_simp
  rw [hid] at hstep
  have hcompare : P^(-1:ℝ)+2*K*P^(-S) ≤ (1+2*K)*(P^(-1:ℝ)+P^(-S)) := by
    have hh : 0 ≤ 2*K*P^(-1:ℝ)+P^(-S) := by positivity
    nlinarith only [hh]
  have hbound : F^2 ≤ (1+2*K)*(P*B)^2*(P^(-1:ℝ)+P^(-S)) := by
    exact hstep.trans ((mul_le_mul_of_nonneg_left hcompare (sq_nonneg _)).trans_eq (by ring))
  simpa only [Nat.reducePow, pow_one] using
    DiagonalCap.ordinary_differencing_cap (F:=F) (A:=P*B) (C:=1+2*K) (P:=P) (S:=S) 1
      hF (mul_nonneg hPpos.le hB) (by positivity) hP hbound

/-- Scalar diagonal/root calculation for the actual two-difference shape. -/
theorem second_scalar_cap {F G B K P S : ℝ} (hF : 0 ≤ F) (hB : 0 ≤ B)
    (hK : 0 ≤ K) (hP : 1 ≤ P)
    (hfirst : F^4 ≤ 16*(P^3*B^4+P*B^3*G)) (hG : G ≤ K*P^3*B*P^(-S)) :
    F ≤ (32*(1+K))^((4:ℝ)⁻¹)*(P*B)*P^(-min 1 S/4) := by
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hstep : F^4 ≤ 16*(P^3*B^4+P*B^3*(K*P^3*B*P^(-S))) := by
    exact hfirst.trans (mul_le_mul_of_nonneg_left
      (add_le_add_left (mul_le_mul_of_nonneg_left hG (by positivity)) _) (by norm_num))
  have hid : 16*(P^3*B^4+P*B^3*(K*P^3*B*P^(-S))) =
      16*(P*B)^4*(P^(-1:ℝ)+K*P^(-S)) := by
    rw [Real.rpow_neg_one]
    field_simp
  rw [hid] at hstep
  have hcompare : P^(-1:ℝ)+K*P^(-S) ≤ (1+K)*(P^(-1:ℝ)+P^(-S)) := by
    have hh : 0 ≤ K*P^(-1:ℝ)+P^(-S) := by positivity
    nlinarith only [hh]
  have hbound : F^4 ≤ (16*(1+K))*(P*B)^4*(P^(-1:ℝ)+P^(-S)) := by
    exact hstep.trans ((mul_le_mul_of_nonneg_left hcompare (by positivity : 0 ≤ 16*(P*B)^4)).trans_eq (by ring))
  have HH := DiagonalCap.ordinary_differencing_cap (F:=F) (A:=P*B)
    (C:=16*(1+K)) (P:=P) (S:=S) 2 hF (mul_nonneg hPpos.le hB) (by positivity) hP hbound
  norm_num only [Nat.reducePow, show (2:ℝ)^2=4 by norm_num,
    show 2*(16*(1+K))=32*(1+K) by ring] at HH
  simpa only [one_div] using HH

/-- Actual original polynomial family through finite resource averages,
coefficient factorization, common completion, and the diagonal/root cap. -/
theorem first_polynomial_resource_cap {j ρ} [Fintype ρ]
    (R : Allocation j ρ) (k p : ℕ) (A α : ℝ) (H : Finset (Fin j → ℝ))
    (hH : H.Nonempty) (C : Fin j → Finset ℝ) (N Q : ℕ) (hN : 0 < N) (hQN : Q ≤ N)
    (V : Fin j → ℝ) (hV : ∀ i, 0 < V i) (hC : ∀ i, ((C i).card:ℝ) ≤ V i)
    (hm : ∀ i, ∀ m ∈ C i, m ≠ 0)
    (hred : ∀ h m : Fin j → ℝ, (∀ l, m l ≠ 0) → ∀ u z : ℝ,
      ordinaryDifference (modifiedCenteredPower k (parameters h m)) u z = normalForm p A ((∏ l, h l)*u) (u^2) h m (2*z+u))
    (hmom : ∀ t ∈ Set.Icc (0:ℝ) 1, R.HasMoments (N:ℝ)
      (fun i (x : H ×ˢ Finset.Icc (1:ℤ) (N:ℤ)) => firstFactors p A α C N V t i x)) :
    ‖polynomialFamily k (cartesianParameters H C) Prod.fst Prod.snd α 1 Q‖ ≤
      (2*(1+2*R.effectiveConstant N))^((2:ℝ)⁻¹)*((N:ℝ)*parameterScale H V)*(N:ℝ)^(-min 1 R.totalSaving/2) := by
  have htuple : ∀ hm' ∈ cartesianParameters H C, ∀ l, hm'.2 l ≠ 0 := by
    intro hm' hhm l
    exact hm l _ (Fintype.mem_piFinset.mp (Finset.mem_product.mp hhm).2 l)
  have Horig := first_unseparated_real_bound (cartesianParameters H C)
    (fun _ => Finset.Icc (1:ℤ) (Q:ℤ))
    (fun hm' z => QuadraticModulation.e (α*modifiedCenteredPower k (parameters hm'.1 hm'.2) z))
    N N (parameterScale H V) le_rfl (parameter_card_le_scale H C V hC)
    (by intro hm' hh; rw [Int.card_Icc]; omega)
    (by intro hm' hh z hz w hw
        have hz' := Finset.mem_Icc.mp hz
        have hw' := Finset.mem_Icc.mp hw
        omega)
    (by intro hm' hh z; simp only [QuadraticModulation.norm_e, le_refl])
  rw [firstDifference_reduced k p A (cartesianParameters H C) Prod.fst Prod.snd α 1 Q N
    (fun hm' hh u z => hred hm'.1 hm'.2 (htuple hm' hh) u z)] at Horig
  have HG := first_reduced_resource_bound R p A α H hH C N Q hN hQN V hV hC hmom
  exact first_scalar_cap (norm_nonneg _)
    (parameterScale_nonneg H V (fun i => (hV i).le)) (R.effectiveConstant_nonneg N hN)
    (by exact_mod_cast hN) Horig HG

/-- Actual original polynomial family through finite resource averages,
coefficient factorization, common completion, and the diagonal/root cap. -/
theorem second_polynomial_resource_cap {j ρ} [Fintype ρ]
    (R : Allocation j ρ) (k p : ℕ) (A α : ℝ) (H : Finset (Fin j → ℝ))
    (hH : H.Nonempty) (C : Fin j → Finset ℝ) (N Q : ℕ) (hN : 0 < N) (hQN : Q ≤ N)
    (V : Fin j → ℝ) (hV : ∀ i, 0 < V i) (hC : ∀ i, ((C i).card:ℝ) ≤ V i)
    (hm : ∀ i, ∀ m ∈ C i, m ≠ 0)
    (hred : ∀ h m : Fin j → ℝ, (∀ l, m l ≠ 0) → ∀ u v z : ℝ,
      ordinaryDifference (ordinaryDifference (modifiedCenteredPower k (parameters h m)) u) v z = normalForm p A ((∏ l, h l)*u*v) (u^2+v^2) h m (2*z+u+v))
    (hmom : ∀ t ∈ Set.Icc (0:ℝ) 1, R.HasMoments (N:ℝ)
      (fun i (x : (H ×ˢ Finset.Icc (1:ℤ) (N:ℤ)) ×ˢ Finset.Icc (1:ℤ) (N:ℤ)) => secondFactors p A α C N V t i x)) :
    ‖polynomialFamily k (cartesianParameters H C) Prod.fst Prod.snd α 1 Q‖ ≤
      (32*(1+R.effectiveConstant N))^((4:ℝ)⁻¹)*((N:ℝ)*parameterScale H V)*(N:ℝ)^(-min 1 R.totalSaving/4) := by
  have htuple : ∀ hm' ∈ cartesianParameters H C, ∀ l, hm'.2 l ≠ 0 := by
    intro hm' hhm l
    exact hm l _ (Fintype.mem_piFinset.mp (Finset.mem_product.mp hhm).2 l)
  have Horig := second_unseparated_real_bound (cartesianParameters H C)
    (fun _ => Finset.Icc (1:ℤ) (Q:ℤ))
    (fun hm' z => QuadraticModulation.e (α*modifiedCenteredPower k (parameters hm'.1 hm'.2) z))
    N N (parameterScale H V) hN le_rfl (parameter_card_le_scale H C V hC)
    (by intro hm' hh; rw [Int.card_Icc]; omega)
    (by intro hm' hh z hz w hw
        have hz' := Finset.mem_Icc.mp hz
        have hw' := Finset.mem_Icc.mp hw
        omega)
    (by intro hm' hh z; simp only [QuadraticModulation.norm_e, le_refl])
  rw [secondDifference_reduced k p A (cartesianParameters H C) Prod.fst Prod.snd α 1 Q N
    (fun hm' hh u v z => hred hm'.1 hm'.2 (htuple hm' hh) u v z)] at Horig
  have HG := second_reduced_resource_bound R p A α H hH C N Q hN hQN V hV hC hmom
  exact second_scalar_cap (norm_nonneg _)
    (parameterScale_nonneg H V (fun i => (hV i).le)) (R.effectiveConstant_nonneg N hN)
    (by exact_mod_cast hN) Horig HG

/-- The concrete k=8, j=4 resource/cap theorem. All polynomial,
factorization, completion, and diagonal/root steps are discharged. -/
theorem k8_j4_resource_cap {ρ} [Fintype ρ]
    (R : Allocation 4 ρ) (α : ℝ) (H : Finset (Fin 4 → ℝ))
    (hH : H.Nonempty) (C : Fin 4 → Finset ℝ) (N Q : ℕ) (hN : 0 < N) (hQN : Q ≤ N)
    (V : Fin 4 → ℝ) (hV : ∀ i, 0 < V i) (hC : ∀ i, ((C i).card:ℝ) ≤ V i)
    (hm : ∀ i, ∀ m ∈ C i, m ≠ 0)
    (hmom : ∀ t ∈ Set.Icc (0:ℝ) 1, R.HasMoments (N:ℝ)
      (fun i (x : (H ×ˢ Finset.Icc (1:ℤ) (N:ℤ)) ×ˢ Finset.Icc (1:ℤ) (N:ℤ)) => secondFactors 16 26880 α C N V t i x)) :
    ‖polynomialFamily 8 (cartesianParameters H C) Prod.fst Prod.snd α 1 Q‖ ≤
      (32*(1+R.effectiveConstant N))^((4:ℝ)⁻¹)*((N:ℝ)*parameterScale H V)*(N:ℝ)^(-min 1 R.totalSaving/4) := by
  exact second_polynomial_resource_cap R 8 16 26880 α H hH C N Q hN hQN V hV hC hm
    (fun h m hm u v z => reduction_k8_j4 h m u v z hm) hmom

/-- The concrete k=8, j=5 resource/cap theorem. All polynomial,
factorization, completion, and diagonal/root steps are discharged. -/
theorem k8_j5_resource_cap {ρ} [Fintype ρ]
    (R : Allocation 5 ρ) (α : ℝ) (H : Finset (Fin 5 → ℝ))
    (hH : H.Nonempty) (C : Fin 5 → Finset ℝ) (N Q : ℕ) (hN : 0 < N) (hQN : Q ≤ N)
    (V : Fin 5 → ℝ) (hV : ∀ i, 0 < V i) (hC : ∀ i, ((C i).card:ℝ) ≤ V i)
    (hm : ∀ i, ∀ m ∈ C i, m ≠ 0)
    (hmom : ∀ t ∈ Set.Icc (0:ℝ) 1, R.HasMoments (N:ℝ)
      (fun i (x : H ×ˢ Finset.Icc (1:ℤ) (N:ℤ)) => firstFactors 16 53760 α C N V t i x)) :
    ‖polynomialFamily 8 (cartesianParameters H C) Prod.fst Prod.snd α 1 Q‖ ≤
      (2*(1+2*R.effectiveConstant N))^((2:ℝ)⁻¹)*((N:ℝ)*parameterScale H V)*(N:ℝ)^(-min 1 R.totalSaving/2) := by
  exact first_polynomial_resource_cap R 8 16 53760 α H hH C N Q hN hQN V hV hC hm
    (fun h m hm u z => reduction_k8_j5 h m u z hm) hmom

/-- The concrete k=9, j=5 resource/cap theorem. All polynomial,
factorization, completion, and diagonal/root steps are discharged. -/
theorem k9_j5_resource_cap {ρ} [Fintype ρ]
    (R : Allocation 5 ρ) (α : ℝ) (H : Finset (Fin 5 → ℝ))
    (hH : H.Nonempty) (C : Fin 5 → Finset ℝ) (N Q : ℕ) (hN : 0 < N) (hQN : Q ≤ N)
    (V : Fin 5 → ℝ) (hV : ∀ i, 0 < V i) (hC : ∀ i, ((C i).card:ℝ) ≤ V i)
    (hm : ∀ i, ∀ m ∈ C i, m ≠ 0)
    (hmom : ∀ t ∈ Set.Icc (0:ℝ) 1, R.HasMoments (N:ℝ)
      (fun i (x : (H ×ˢ Finset.Icc (1:ℤ) (N:ℤ)) ×ˢ Finset.Icc (1:ℤ) (N:ℤ)) => secondFactors 18 483840 α C N V t i x)) :
    ‖polynomialFamily 9 (cartesianParameters H C) Prod.fst Prod.snd α 1 Q‖ ≤
      (32*(1+R.effectiveConstant N))^((4:ℝ)⁻¹)*((N:ℝ)*parameterScale H V)*(N:ℝ)^(-min 1 R.totalSaving/4) := by
  exact second_polynomial_resource_cap R 9 18 483840 α H hH C N Q hN hQN V hV hC hm
    (fun h m hm u v z => reduction_k9_j5 h m u v z hm) hmom

/-- The concrete k=9, j=6 resource/cap theorem. All polynomial,
factorization, completion, and diagonal/root steps are discharged. -/
theorem k9_j6_resource_cap {ρ} [Fintype ρ]
    (R : Allocation 6 ρ) (α : ℝ) (H : Finset (Fin 6 → ℝ))
    (hH : H.Nonempty) (C : Fin 6 → Finset ℝ) (N Q : ℕ) (hN : 0 < N) (hQN : Q ≤ N)
    (V : Fin 6 → ℝ) (hV : ∀ i, 0 < V i) (hC : ∀ i, ((C i).card:ℝ) ≤ V i)
    (hm : ∀ i, ∀ m ∈ C i, m ≠ 0)
    (hmom : ∀ t ∈ Set.Icc (0:ℝ) 1, R.HasMoments (N:ℝ)
      (fun i (x : H ×ˢ Finset.Icc (1:ℤ) (N:ℤ)) => firstFactors 18 967680 α C N V t i x)) :
    ‖polynomialFamily 9 (cartesianParameters H C) Prod.fst Prod.snd α 1 Q‖ ≤
      (2*(1+2*R.effectiveConstant N))^((2:ℝ)⁻¹)*((N:ℝ)*parameterScale H V)*(N:ℝ)^(-min 1 R.totalSaving/2) := by
  exact first_polynomial_resource_cap R 9 18 967680 α H hH C N Q hN hQN V hV hC hm
    (fun h m hm u z => reduction_k9_j6 h m u z hm) hmom

def zeroFactors {j : ℕ} (p : ℕ) (A α : ℝ) (C : Fin j → Finset ℝ)
    (N : ℕ) (V : Fin j → ℝ) (t : ℝ) :=
  normalizedFactor p (centeredSet N) C
    (fun h : Fin j → ℝ => 3*α*A*(∏ l, h l))
    (fun l h => (4*α*A*(∏ l', h l'))*(h l)^2) t (sourceCaps N V)

theorem zeroProducts_resource_bound {j ρ} [Fintype ρ]
    (R : Allocation j ρ) (p : ℕ) (A α : ℝ) (H : Finset (Fin j → ℝ))
    (hH : H.Nonempty) (C : Fin j → Finset ℝ) (N : ℕ) (hN : 0 < N)
    (V : Fin j → ℝ) (hV : ∀ i, 0 < V i) (hC : ∀ i, ((C i).card:ℝ) ≤ V i)
    (t : ℝ) (hmom : R.HasMoments (N:ℝ)
      (fun i (x : H) => zeroFactors p A α C N V t i x)) :
    zeroProducts p A α H C N t ≤
      5*(N:ℝ)*parameterScale H V*R.totalConstant*(N:ℝ)^(-R.totalSaving) := by
  have hNR : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : 0 < (N:ℝ) := by exact_mod_cast hN
  have Hbound := finite_product_resource_saving H hH p (centeredSet N) C
    (fun h => 3*α*A*(∏ l, h l))
    (fun l h => (4*α*A*(∏ l', h l'))*(h l)^2) t
    (sourceCaps N V) (sourceCaps_pos N V hV)
    (by simp only [centeredSet_card, sourceCaps, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, le_refl])
    hC R.factor R.order R.weight R.order_nonneg R.weight_nonneg R.mass_le R.load_le
    N hNpos R.constant R.saving R.constant_nonneg hmom
  have hZ : 4*(N:ℝ)+1 ≤ 5*(N:ℝ) := by linarith
  have hm := mul_le_mul_of_nonneg_left hZ
    (show 0 ≤ (H.card:ℝ)*(∏ i, V i)*R.totalConstant*(N:ℝ)^(-R.totalSaving) from
      mul_nonneg (mul_nonneg (mul_nonneg (by positivity)
        (Finset.prod_nonneg (fun i _ => (hV i).le))) R.totalConstant_nonneg)
        (Real.rpow_nonneg hNpos.le _))
  simp only [Fintype.prod_option, sourceCaps] at Hbound
  change zeroProducts p A α H C N t ≤ _ at Hbound
  unfold Allocation.totalConstant Allocation.totalSaving parameterScale at *
  exact Hbound.trans (by convert hm using 1 <;> ring)

/-- The already-quadratic degree-eight policy, from actual finite moments
through exact coefficient factorization and common parity completion. -/
theorem k8_j6_resource_bound {ρ} [Fintype ρ]
    (R : Allocation 6 ρ) (α : ℝ) (H : Finset (Fin 6 → ℝ))
    (hH : H.Nonempty) (C : Fin 6 → Finset ℝ) (N Q : ℕ) (hN : 0 < N) (hQN : Q ≤ N)
    (V : Fin 6 → ℝ) (hV : ∀ i, 0 < V i) (hC : ∀ i, ((C i).card:ℝ) ≤ V i)
    (hm : ∀ i, ∀ m ∈ C i, m ≠ 0)
    (hmom : ∀ t ∈ Set.Icc (0:ℝ) 1, R.HasMoments (N:ℝ)
      (fun i (x : H) => zeroFactors 16 107520 α C N V t i x)) :
    ‖polynomialFamily 8 (cartesianParameters H C) Prod.fst Prod.snd α 1 Q‖ ≤
      R.effectiveConstant N*((N:ℝ)*parameterScale H V)*(N:ℝ)^(-R.totalSaving) := by
  have HB0 : 0 ≤ 5*(N:ℝ)*parameterScale H V*R.totalConstant*(N:ℝ)^(-R.totalSaving) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by positivity)
      (parameterScale_nonneg H V (fun i => (hV i).le))) R.totalConstant_nonneg)
      (Real.rpow_nonneg (by positivity) _)
  have HG := cartesian_k8_j6_completed_bound H C α N Q hN hQN hm _ HB0
    (fun t ht => zeroProducts_resource_bound R 16 107520 α H hH C N hN V hV hC t (hmom t ht))
  exact HG.trans_eq (by unfold Allocation.effectiveConstant; ring)

/-- Capping the r=0 saving at one is permissible and gives the same
certificate convention as the one- and two-difference cases. -/
theorem k8_j6_resource_cap {ρ} [Fintype ρ]
    (R : Allocation 6 ρ) (α : ℝ) (H : Finset (Fin 6 → ℝ))
    (hH : H.Nonempty) (C : Fin 6 → Finset ℝ) (N Q : ℕ) (hN : 0 < N) (hQN : Q ≤ N)
    (V : Fin 6 → ℝ) (hV : ∀ i, 0 < V i) (hC : ∀ i, ((C i).card:ℝ) ≤ V i)
    (hm : ∀ i, ∀ m ∈ C i, m ≠ 0)
    (hmom : ∀ t ∈ Set.Icc (0:ℝ) 1, R.HasMoments (N:ℝ)
      (fun i (x : H) => zeroFactors 16 107520 α C N V t i x)) :
    ‖polynomialFamily 8 (cartesianParameters H C) Prod.fst Prod.snd α 1 Q‖ ≤
      R.effectiveConstant N*((N:ℝ)*parameterScale H V)*(N:ℝ)^(-min 1 R.totalSaving) := by
  have HH := k8_j6_resource_bound R α H hH C N Q hN hQN V hV hC hm hmom
  exact HH.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (neg_le_neg (min_le_right 1 R.totalSaving)))
    (mul_nonneg (R.effectiveConstant_nonneg N hN)
      (mul_nonneg (by positivity) (parameterScale_nonneg H V (fun i => (hV i).le)))))

#print axioms first_polynomial_resource_cap
#print axioms second_polynomial_resource_cap
#print axioms k8_j4_resource_cap
#print axioms k8_j5_resource_cap
#print axioms k8_j6_resource_cap
#print axioms k9_j5_resource_cap
#print axioms k9_j6_resource_cap

end Waring.ResourceDifferencingCap
