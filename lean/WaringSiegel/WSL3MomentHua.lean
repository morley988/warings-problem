import WaringSiegel.WSL3MomentHuaGrowth

/-!
# The full number-field Hua family

For every 1 ≤ j ≤ k, the literal one-frequency Haar moment has exponent
2^j − j + ε in the volume X = P^[K:Q].  The induction uses the proved
all-order Weyl cubes and actual divisor bounds, with no analytic premise.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators NumberField Classical

namespace WaringSiegel.WSL3
open WSL2
variable {K : Type*} [Field K] [NumberField K]

/-- The full classical Hua estimate on every finite archimedean box. -/
theorem numberField_hua_moment_unweighted (k j : ℕ) (hj : 1 ≤ j) (hjk : j ≤ k)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P → ∀ S : Finset (𝓞 K),
      (∀ x ∈ S, ∀ v : NumberField.InfinitePlace K, v (x : K) ≤ P) →
      (∫ θ, ‖finiteFrequencySum S (fun x => integerCoordinates K (x^k)) θ‖^(2^j) ∂latticeHaar) ≤
        C * (P ^ Module.finrank ℚ K : ℝ)^((2^j-j : ℕ)+ε) := by
  induction j with
  | zero => omega
  | succ J ih =>
    by_cases hJ0 : J = 0
    · subst J
      obtain ⟨C, hC, hbound⟩ := numberField_second_moment_bound (K := K) k (by omega) hε
      refine ⟨C, hC, ?_⟩
      intro P hP S hS
      have h := hbound P hP (fun x : S => (x : 𝓞 K)) Subtype.val_injective
        (fun x v => hS x x.property v) (fun _ => (1 : ℂ)) 1 (by norm_num) (by intro x; simp)
      simpa only [← finiteFrequencySum_power_eq_subtype, one_pow, mul_one,
        Nat.zero_add, pow_one, show 2-1=1 by omega, Nat.cast_one] using h
    · have hJ : 1 ≤ J := by omega
      have hJk : J < k := by omega
      obtain ⟨A, hA, hprev⟩ := ih hJ (by omega)
      obtain ⟨M, hM, hnonzero⟩ := numberField_hua_nonzero_fibers (K := K) k J hJ hJk hε
      let d := Module.finrank ℚ K
      let CS : ℝ := 2 * (3 : ℝ)^d
      let CH : ℝ := CS * (2 : ℝ)^d
      let Z : ℝ := (J : ℝ)*CH^(J-1)*CS + (k-J : ℕ)*CH^J
      let e := 2^J-J-1
      let C : ℝ := CH^e * (A*Z + CS^(2^J)*M)
      have hCS : 0 < CS := by dsimp [CS]; positivity
      have hCH : 0 < CH := by dsimp [CH]; positivity
      have hJR : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
      have hZ : 0 < Z := by dsimp [Z]; positivity
      refine ⟨C, by dsimp [C]; positivity, ?_⟩
      intro P hP S hS
      let X : ℝ := P^d
      let H := additiveDifferences S
      have hPpos : 0 < P := lt_of_lt_of_le zero_lt_one hP
      have hX : 0 < X := by dsimp [X]; positivity
      have hN : (S.card : ℝ) ≤ CS*X := integer_box_card_bound S P hP hS
      have hH : (H.card : ℝ) ≤ CH*X := by
        have hh := integer_box_card_bound H (2*P) (by linarith) (by
          intro h hh v
          exact additiveDifferences_place_bound S hS hh v)
        rw [mul_pow] at hh
        convert hh using 1 <;> dsimp [CH, CS, X] <;> ring
      have hshift : ∀ x ∈ S, ∀ y ∈ S, x-y ∈ H :=
        fun _ hx _ hy => additiveDifferences_mem S hx hy
      have hI := hprev P hP S hS
      have hIpos : 0 ≤
          (∫ θ, ‖finiteFrequencySum S (fun x => integerCoordinates K (x^k)) θ‖^(2^J) ∂latticeHaar) :=
        integral_nonneg (fun _ => by positivity)
      have hJpow : X^(J-1)*X = X^J := by
        rw [← pow_succ]
        congr 1
        omega
      have hz : ((iteratedDifferenceFiber S H k J 0).card : ℝ) ≤ Z*X^J := by
        calc
          _ ≤ (J : ℝ)*(H.card : ℝ)^(J-1)*S.card + (k-J : ℕ)*(H.card : ℝ)^J := by
            exact_mod_cast iteratedDifference_zero_fiber_card_le S H k J hJk
          _ ≤ (J : ℝ)*(CH*X)^(J-1)*(CS*X) + (k-J : ℕ)*(CH*X)^J := by gcongr
          _ = (J : ℝ)*CH^(J-1)*CS*(X^(J-1)*X) + (k-J : ℕ)*CH^J*X^J := by
            simp only [mul_pow]
            ring
          _ = Z*X^J := by rw [hJpow]; dsimp [Z]; ring
      have hred := hua_induction_step (integerCoordinates K) (integerCoordinates_injective K)
        S H hshift k J hJ (Z*X^J) (M*X^ε) (by positivity) hz
        (hnonzero P hP S hS)
      have hJle : J ≤ 2^J := (Nat.le_succ J).trans (succ_le_two_pow J)
      have hsub : ((2^J-J : ℕ) : ℝ) + (J : ℝ) = (2^J : ℕ) := by
        exact_mod_cast Nat.sub_add_cancel hJle
      have hpow₁ : X^((2^J-J : ℕ)+ε)*X^J = X^((2^J : ℕ)+ε) := by
        rw [← Real.rpow_natCast X J, ← Real.rpow_add hX]
        congr 1
        linarith
      have hpow₂ : X^(2^J)*X^ε = X^((2^J : ℕ)+ε) := by
        rw [← Real.rpow_natCast X (2^J), ← Real.rpow_add hX]
      have hexp : e + 2^J = 2^(J+1)-(J+1) := by
        have h := succ_le_two_pow J
        dsimp [e]
        rw [pow_succ]
        omega
      have hpow₃ : X^e*X^((2^J : ℕ)+ε) = X^((2^(J+1)-(J+1) : ℕ)+ε) := by
        rw [← Real.rpow_natCast X e, ← Real.rpow_add hX]
        congr 1
        have he : (e : ℝ) + ((2^J : ℕ) : ℝ) = (2^(J+1)-(J+1) : ℕ) := by
          exact_mod_cast hexp
        linarith
      calc
        (∫ θ, ‖finiteFrequencySum S (fun x => integerCoordinates K (x^k)) θ‖^(2^(J+1)) ∂latticeHaar) ≤
            (H.card : ℝ)^e *
              ((∫ θ, ‖finiteFrequencySum S (fun x => integerCoordinates K (x^k)) θ‖^(2^J) ∂latticeHaar) *
                (Z*X^J) + (S.card : ℝ)^(2^J)*(M*X^ε)) := hred
        _ ≤ (CH*X)^e * (A*X^((2^J-J : ℕ)+ε)*(Z*X^J) + (CS*X)^(2^J)*(M*X^ε)) := by
          gcongr
        _ = CH^e * (A*Z*(X^((2^J-J : ℕ)+ε)*X^J) + CS^(2^J)*M*(X^(2^J)*X^ε))*X^e := by
          simp only [mul_pow]
          ring
        _ = C * (X^e*X^((2^J : ℕ)+ε)) := by rw [hpow₁, hpow₂]; dsimp [C]; ring
        _ = C * X^((2^(J+1)-(J+1) : ℕ)+ε) := by rw [hpow₃]

#print axioms numberField_hua_moment_unweighted

end WaringSiegel.WSL3
