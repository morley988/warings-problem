import Waring.PolicyCompletionTerminalShape
import Waring.PolicyCompletionLoss

/-! # The exact root and diagonal cap for every source terminal shape -/
noncomputable section
open scoped BigOperators
namespace Waring.PolicyCompletionShapeCap
open PolicyCompletionTerminalShape ResourceDifferencingCap FiniteResourceHolder
open PolynomialSumReduction CartesianPolynomialBounds Differences CoefficientFactorization

/-- These are the literal polynomial identities used by the five terminal shapes. -/
def Reduction (s : Shape) (k j A : ℕ) : Prop :=
  match s with
  | .zero=>k=8 ∧ j=6 ∧ A=107520
  | .first=>∀h m : Fin j→ℝ,(∀i,m i≠0)→∀u z : ℝ,
    ordinaryDifference (modifiedCenteredPower k (parameters h m)) u z=
      normalForm (2*k) A ((∏i,h i)*u) (u^2) h m (2*z+u)
  | .second=>∀h m : Fin j→ℝ,(∀i,m i≠0)→∀u v z : ℝ,
    ordinaryDifference (ordinaryDifference (modifiedCenteredPower k (parameters h m)) u) v z=
      normalForm (2*k) A ((∏i,h i)*u*v) (u^2+v^2) h m (2*z+u+v)

def prefactorA : Shape→ℝ
  | .zero=>0 | .first=>2 | .second=>32
def prefactorB : Shape→ℝ
  | .zero=>1 | .first=>4 | .second=>32

theorem root_ge_one (s : Shape) : 1≤root s := by cases s <;> norm_num [root]
theorem prefactorA_nonneg (s : Shape) : 0≤prefactorA s := by cases s <;> norm_num [prefactorA]
theorem prefactorB_pos (s : Shape) : 0<prefactorB s := by cases s <;> norm_num [prefactorB]

theorem shape_cap_with_loss {j : ℕ} {ρ : Type*} [Fintype ρ]
    (R : Allocation j ρ) (s : Shape) (k A : ℕ) (hred : Reduction s k j A)
    (α : ℝ) (H : Finset (Fin j→ℝ)) (hH : H.Nonempty)
    (C : Fin j→Finset ℝ) (N Q : ℕ) (hN : 0<N) (hQN : Q≤N)
    (V : Fin j→ℝ) (hV : ∀i,0<V i) (hC : ∀i,((C i).card:ℝ)≤V i)
    (hm : ∀i,∀m∈C i,m≠0) {δ : ℝ} (hδ : 0≤δ)
    (hmom : ∀t∈Set.Icc (0:ℝ) 1,∀r,
      average (fun x : samples s H N=>
        (factors s (2*k) A α C N V t (R.factor r) x.val)^(R.order r))≤
          R.constant r*(N:ℝ)^(δ-R.saving r)) :
    ‖polynomialFamily k (cartesianParameters H C) Prod.fst Prod.snd α 1 Q‖≤
      (prefactorA s+prefactorB s*R.effectiveConstant N)^(1/root s)*
        ((N:ℝ)*parameterScale H V)*(N:ℝ)^(δ/root s-min 1 R.totalSaving/root s) := by
  cases s with
  | zero =>
    rcases hred with ⟨rfl,rfl,rfl⟩
    have hc := k8_j6_resource_cap (R.withLoss δ) α H hH C N Q hN hQN V hV hC hm
      (fun t ht=>R.hasMoments_withLoss N δ _ (hmom t ht))
    rw [R.withLoss_effectiveConstant] at hc
    have hp := R.withLoss_cap_power (P:=(N:ℝ)) (d:=1) (by exact_mod_cast hN) hδ (by norm_num)
    have hn := mul_nonneg (R.effectiveConstant_nonneg N hN)
      (mul_nonneg (Nat.cast_nonneg N) (parameterScale_nonneg H V (fun i=>(hV i).le)))
    have h := hc.trans (mul_le_mul_of_nonneg_left (by simpa only [div_one] using hp) hn)
    simpa only [prefactorA,prefactorB,root,one_mul,zero_add,div_one,Real.rpow_one] using h
  | first =>
    have hc := first_polynomial_resource_cap_with_loss R k (2*k) A α H hH C N Q hN hQN
      V hV hC hm hred hδ hmom
    have hid : 2*(1+2*R.effectiveConstant N)=2+4*R.effectiveConstant N := by ring
    rw [hid] at hc
    simpa only [prefactorA,prefactorB,root,one_div] using hc
  | second =>
    have hc := second_polynomial_resource_cap_with_loss R k (2*k) A α H hH C N Q hN hQN
      V hV hC hm hred hδ hmom
    have hid : 32*(1+R.effectiveConstant N)=32+32*R.effectiveConstant N := by ring
    rw [hid] at hc
    simpa only [prefactorA,prefactorB,root,one_div] using hc

theorem reduction8_6 : Reduction .zero 8 6 107520 := ⟨rfl,rfl,rfl⟩
theorem reduction8_5 : Reduction .first 8 5 53760 := by
  intro h m hm u z
  exact reduction_k8_j5 h m u z hm
theorem reduction8_4 : Reduction .second 8 4 26880 := by
  intro h m hm u v z
  exact reduction_k8_j4 h m u v z hm
theorem reduction9_6 : Reduction .first 9 6 967680 := by
  intro h m hm u z
  exact reduction_k9_j6 h m u z hm
theorem reduction9_5 : Reduction .second 9 5 483840 := by
  intro h m hm u v z
  exact reduction_k9_j5 h m u v z hm

#print axioms shape_cap_with_loss
end Waring.PolicyCompletionShapeCap
