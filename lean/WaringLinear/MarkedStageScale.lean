import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-! # The fixed global scale and the terminal states in marked shortening -/
noncomputable section
open scoped BigOperators
namespace WaringLinear

/-- A loss measured at the parent P converts at any child X≥P^γ
without a scale-dependent constant. -/
theorem loss_on_child_scale (P X γ ε : ℝ) (hP : 0<P)
    (hγ : 0<γ) (hε : 0≤ε) (hX : P^γ≤X) :
    P^ε≤X^(ε/γ) := by
  have h := Real.rpow_le_rpow (Real.rpow_nonneg hP.le _) hX (div_nonneg hε hγ.le)
  rwa [←Real.rpow_mul hP.le,show γ*(ε/γ)=ε by field_simp] at h

/-- When the primary marks are exhausted, the trivial r-moment is
already admissible at P^ε precision. The bound covers all A≥0. -/
theorem short_cofactor_terminal (I P X r k A ν ε C : ℝ)
    (hP : 1≤P) (hX : 1≤X) (ht : X≤P^ν) (hk : 0≤k)
    (hA : 0≤A) (hε : ν*k≤ε) (hC : 0≤C) (hI : I≤C*X^r) :
    I≤C*P^ε*X^(r-k+A) := by
  have hPp := lt_of_lt_of_le zero_lt_one hP
  have hXp := lt_of_lt_of_le zero_lt_one hX
  have shift : X^(k-A)≤P^ε := by
    calc
      _ ≤ X^k := Real.rpow_le_rpow_of_exponent_le hX (by linarith)
      _ ≤ (P^ν)^k := Real.rpow_le_rpow hXp.le ht hk
      _ = P^(ν*k) := (Real.rpow_mul hPp.le ν k).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hP hε
  have reg : X^(k-A)*X^(r-k+A)=X^r := by rw [←Real.rpow_add hXp]; congr 1; ring
  have H := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right shift
    (Real.rpow_nonneg hXp.le (r-k+A))) hC
  rw [reg] at H
  exact hI.trans (by simpa only [mul_assoc] using H)

/-- Inner induction over the number of retained primary windows. The
cofactor state may vary with the removed primes. Its P^ε factor stays
fixed throughout this induction, and the zeta factor B only enlarges
the implied constant. -/
theorem bounded_state_induction {S : Type*} (depth : S→ℕ) (A B : ℝ)
    (hA : 0≤A) (hB : 0≤B) (mass scale : S→ℝ) (hs : ∀s,0≤scale s)
    (step : ∀s C, 0≤C →
      (∀t,depth t<depth s → mass t≤C*scale t) →
      mass s≤(A+B*C)*scale s) (s : S) :
    mass s≤A*(1+B)^(depth s+1)*scale s := by
  have Hb : 1≤1+B := by linarith
  suffices D : ∀ n,∀ t,depth t≤n → mass t≤A*(1+B)^(n+1)*scale t by
    exact D _ _ le_rfl
  intro n
  induction n with
  | zero =>
    intro t ht
    have H := step t 0 le_rfl (fun u hu => False.elim (by omega))
    simp only [mul_zero,add_zero] at H
    apply H.trans
    apply mul_le_mul_of_nonneg_right _ (hs t)
    simpa using (mul_le_mul_of_nonneg_left Hb hA)
  | succ n ih =>
    intro t ht
    let C := A*(1+B)^(n+1)
    have C0 : 0≤C := mul_nonneg hA (pow_nonneg (zero_le_one.trans Hb) _)
    have H := step t C C0 (fun u hu => ih u (by omega))
    have CA : A≤C := by
      simpa only [C,mul_one] using
        (mul_le_mul_of_nonneg_left (one_le_pow₀ Hb (n:=n+1)) hA)
    apply H.trans
    apply mul_le_mul_of_nonneg_right _ (hs t)
    change A+B*C≤A*(1+B)^(n+1+1)
    calc
      A+B*C ≤ C+B*C := by linarith only [CA]
      _ = A*(1+B)^(n+1+1) := by dsimp [C]; rw [pow_succ (1+B) (n+1)]; ring

#print axioms loss_on_child_scale
#print axioms short_cofactor_terminal
#print axioms bounded_state_induction
end WaringLinear
