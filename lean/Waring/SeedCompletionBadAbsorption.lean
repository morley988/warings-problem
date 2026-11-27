import Waring.SeedCompletionDiagonalCounts

/-!
# Finite absorption of the exceptional efficient-differencing branch

This elementary induction retains the zeroth-moment diagonal contribution.
The second sequence is the actual common-modulus count after weighting by
the coefficient block size; its successive diagonal embeddings supply the
growth inequality. Constants depend on the fixed number of smooth pairs.
-/

noncomputable section
namespace Waring.SeedCompletionBadAbsorption

/-- A finite recurrence with an actual diagonally growing second sequence.
This is used before any backward differencing or terminal Holder step. -/
theorem absorb_sequence (E J : ℕ → ℝ) {K a b ρ : ℝ}
    (hK : 1 ≤ K) (ha : 0 ≤ a) (hb : 0 ≤ b) (hρ : 1 ≤ ρ)
    (hE : ∀ n, 0 ≤ E n) (hJ : ∀ n, 0 ≤ J n) (n : ℕ)
    (hstep : ∀ i, i ≤ n → E (i+1) ≤ K*(a*E i+b*J (i+1)))
    (hgrowth : ∀ i, i < n → a*J (i+1) ≤ ρ*J (i+2)) :
    E (n+1) ≤ (K*a)^(n+1)*E 0+(2*K*ρ)^(n+1)*b*J (n+1) := by
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hρ0 : 0 ≤ ρ := zero_le_one.trans hρ
  have hbase : 1 ≤ 2*K*ρ := by nlinarith
  revert hstep hgrowth
  induction n with
  | zero =>
    intro hstep hgrowth
    have hc : K ≤ 2*K*ρ := by nlinarith
    calc
      E 1 ≤ K*(a*E 0+b*J 1) := hstep 0 le_rfl
      _ ≤ K*a*E 0+(2*K*ρ)*b*J 1 := by
        have hh := mul_le_mul_of_nonneg_right hc (mul_nonneg hb (hJ 1))
        nlinarith
      _ = _ := by norm_num
  | succ n ih =>
    intro hstep hgrowth
    have ih := ih (fun i hi => hstep i (hi.trans (Nat.le_succ _)))
      (fun i hi => hgrowth i (hi.trans (Nat.lt_succ_self _)))
    have hp : 1 ≤ (2*K*ρ)^(n+1) := one_le_pow₀ hbase
    have hcoef : K*((2*K*ρ)^(n+1)*ρ+1) ≤ (2*K*ρ)^(n+2) := by
      rw [show n+2=(n+1)+1 by omega,pow_succ (2*K*ρ) (n+1)]
      have hprod : 1 ≤ (2*K*ρ)^(n+1)*ρ := one_le_mul_of_one_le_of_one_le hp hρ
      nlinarith
    calc
      E (n+1+1) ≤ K*(a*E (n+1)+b*J (n+1+1)) := hstep (n+1) le_rfl
      _ ≤ K*(a*((K*a)^(n+1)*E 0+(2*K*ρ)^(n+1)*b*J (n+1))+
        b*J (n+1+1)) := by gcongr
      _ = (K*a)^(n+2)*E 0+
        K*((2*K*ρ)^(n+1)*b*(a*J (n+1))+b*J (n+2)) := by
          rw [show n+2=(n+1)+1 by omega,pow_succ (K*a) (n+1)]
          ring
      _ ≤ (K*a)^(n+2)*E 0+
        K*((2*K*ρ)^(n+1)*b*(ρ*J (n+2))+b*J (n+2)) := by
          apply add_le_add_left
          apply mul_le_mul_of_nonneg_left _ hK0
          apply add_le_add_right
          exact mul_le_mul_of_nonneg_left (hgrowth n (Nat.lt_succ_self _)) (by positivity)
      _ = (K*a)^(n+2)*E 0+K*((2*K*ρ)^(n+1)*ρ+1)*b*J (n+2) := by ring
      _ ≤ (K*a)^(n+2)*E 0+(2*K*ρ)^(n+2)*b*J (n+2) := by
        gcongr
        exact hJ _

/-- The exact coefficient exponents preserve the diagonal growth factor. -/
theorem weighted_count_growth (T : ℕ → ℝ) {a w d ρ : ℝ}
    (hw : 0 ≤ w) (hd : 0 ≤ d) (hρ : 0 ≤ ρ) (hT : ∀ n,0 ≤ T n)
    (hdensity : a ≤ ρ*w^2*d)
    (hdiag : ∀ n,d*T n ≤ T (n+1)) (n : ℕ) :
    a*(w^(2*(n+1)-1)*T (n+1)) ≤
      ρ*(w^(2*(n+2)-1)*T (n+2)) := by
  have he : 2*(n+2)-1=(2*(n+1)-1)+2 := by omega
  calc
    _ ≤ (ρ*w^2*d)*(w^(2*(n+1)-1)*T (n+1)) :=
      mul_le_mul_of_nonneg_right hdensity (mul_nonneg (pow_nonneg hw _) (hT _))
    _ = ρ*(w^(2*(n+1)-1)*w^2)*(d*T (n+1)) := by ring
    _ ≤ ρ*(w^(2*(n+1)-1)*w^2)*T (n+2) := by
      gcongr
      exact hdiag (n+1)
    _ = _ := by rw [he,pow_add]; ring

#print axioms absorb_sequence
#print axioms weighted_count_growth
end Waring.SeedCompletionBadAbsorption
