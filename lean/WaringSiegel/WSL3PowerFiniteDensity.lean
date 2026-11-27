import WaringSiegel.WSL3LocalCharacterReduction

/-! # WSL3: degree-uniform pure-power residue counts

The pure-power Gauss estimate gives an explicit normalized count error for
every positive exponent and every even number of variables. These are actual
finite-field counts; there is no assumed finite-field estimate.
-/
noncomputable section
set_option maxHeartbeats 800000
open scoped BigOperators Classical
namespace WaringSiegel
variable {F : Type*} [Field F] [Fintype F]

theorem finite_field_power_character_term_even_bound
    (k s : ℕ) (hk : 0 < k) (b : F) (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) :
    ‖finiteRingPowerCharacterTerm k (2*s) b ψ‖ ≤
      ((k-1 : ℕ) : ℝ)^(2*s) / (Fintype.card F : ℝ)^s := by
  letI : Fintype (MulChar F ℂ) := Fintype.ofFinite _
  have h := finite_field_power_sum_norm_le ψ (AddChar.IsPrimitive.of_ne_one hψ) k hk
  have hpow := pow_le_pow_left₀ (norm_nonneg _) h (2*s)
  have hs : (Real.sqrt (Fintype.card F : ℝ))^(2*s) = (Fintype.card F : ℝ)^s := by
    rw [pow_mul, Real.sq_sqrt (Nat.cast_nonneg _)]
  have hq : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have he : (((k-1 : ℕ) : ℝ) * Real.sqrt (Fintype.card F : ℝ))^(2*s) /
      (Fintype.card F : ℝ)^(2*s) =
      ((k-1 : ℕ) : ℝ)^(2*s) / (Fintype.card F : ℝ)^s := by
    rw [mul_pow, hs, show 2*s=s+s by omega, pow_add]
    field_simp
    simp only [pow_add, pow_two]
  calc
    _ = ‖finiteRingPowerSum ψ k‖^(2*s) / (Fintype.card F : ℝ)^(2*s) := by
      simp only [finiteRingPowerCharacterTerm, norm_mul, norm_pow, norm_div,
        finite_addChar_norm_one, mul_one, Complex.norm_natCast, div_pow]
    _ ≤ _ := (div_le_div_of_nonneg_right hpow (by positivity)).trans_eq he

theorem finite_field_power_even_normalized_error
    (k s : ℕ) (hk : 0 < k) (hs : 1 ≤ s) (b : F) :
    |(Nat.card {x : Fin (2*s) → F // (∑ i, x i^k) = b} : ℝ) /
      (Fintype.card F : ℝ)^(2*s-1) - 1| ≤
      ((k-1 : ℕ) : ℝ)^(2*s) / (Fintype.card F : ℝ)^(s-1) := by
  have hq : (Fintype.card F : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hqR : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have h1 : finiteRingPowerCharacterTerm k (2*s) b (1 : AddChar F ℂ) = 1 := by
    simp [finiteRingPowerCharacterTerm, finiteRingPowerSum, hq]
  have hsum := Finset.sum_erase_add (Finset.univ : Finset (AddChar F ℂ))
    (finiteRingPowerCharacterTerm k (2*s) b) (Finset.mem_univ 1)
  have hcount := finite_ring_power_normalized_character_count k (2*s) (by omega) b
  change (∑ ψ : AddChar F ℂ, finiteRingPowerCharacterTerm k (2*s) b ψ) = _ at hcount
  rw [h1,hcount] at hsum
  have herr : (Nat.card {x : Fin (2*s) → F // (∑ i, x i^k) = b} : ℂ) /
      (Fintype.card F : ℂ)^(2*s-1) - 1 =
      ∑ ψ ∈ (Finset.univ.erase (1 : AddChar F ℂ)), finiteRingPowerCharacterTerm k (2*s) b ψ := by
    linear_combination -hsum
  have hbound : ‖(Nat.card {x : Fin (2*s) → F // (∑ i, x i^k) = b} : ℂ) /
      (Fintype.card F : ℂ)^(2*s-1) - 1‖ ≤
      ((k-1 : ℕ) : ℝ)^(2*s) / (Fintype.card F : ℝ)^(s-1) := by
    rw [herr]
    calc
      _ ≤ ∑ ψ ∈ (Finset.univ.erase (1 : AddChar F ℂ)),
          ‖finiteRingPowerCharacterTerm k (2*s) b ψ‖ := norm_sum_le _ _
      _ ≤ ∑ _ψ ∈ (Finset.univ.erase (1 : AddChar F ℂ)),
          ((k-1 : ℕ) : ℝ)^(2*s) / (Fintype.card F : ℝ)^s := by
        apply Finset.sum_le_sum
        intro ψ hψ
        exact finite_field_power_character_term_even_bound k s hk b ψ (Finset.mem_erase.mp hψ).1
      _ ≤ (Fintype.card F : ℝ) *
          (((k-1 : ℕ) : ℝ)^(2*s) / (Fintype.card F : ℝ)^s) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have hc := Finset.card_le_card (Finset.erase_subset (1 : AddChar F ℂ) Finset.univ)
        simpa only [Finset.card_univ, AddChar.card_eq] using (Nat.cast_le (α := ℝ)).mpr hc
      _ = _ := by
        rw [show s=(s-1)+1 by omega, pow_succ]
        simp only [Nat.add_sub_cancel]
        field_simp
  have he : (Nat.card {x : Fin (2*s) → F // (∑ i, x i^k) = b} : ℂ) /
      (Fintype.card F : ℂ)^(2*s-1) - 1 =
      (((Nat.card {x : Fin (2*s) → F // (∑ i, x i^k) = b} : ℝ) /
        (Fintype.card F : ℝ)^(2*s-1) - 1 : ℝ) : ℂ) := by push_cast; rfl
  simpa only [he, Complex.norm_real, Real.norm_eq_abs] using hbound

theorem finite_field_power_even_normalized_lower
    (k s : ℕ) (hk : 0 < k) (hs : 2 ≤ s)
    (hq : 2*(k-1)^(2*s) ≤ Fintype.card F) (b : F) :
    (1/2 : ℝ) ≤ (Nat.card {x : Fin (2*s) → F // (∑ i, x i^k) = b} : ℝ) /
      (Fintype.card F : ℝ)^(2*s-1) := by
  have hq0 : 0 < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  have hq1 : 1 ≤ (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  have hqpow : (Fintype.card F : ℝ) ≤ (Fintype.card F : ℝ)^(s-1) := by
    simpa only [pow_one] using pow_le_pow_right₀ hq1 (show 1 ≤ s-1 by omega)
  have hqR : 2*((k-1 : ℕ) : ℝ)^(2*s) ≤ (Fintype.card F : ℝ) := by
    exact_mod_cast hq
  have herr := (abs_le.mp (finite_field_power_even_normalized_error k s hk (by omega) b)).1
  have hsmall : ((k-1 : ℕ) : ℝ)^(2*s) / (Fintype.card F : ℝ)^(s-1) ≤ (1/2 : ℝ) := by
    apply (div_le_iff₀ (pow_pos hq0 _)).mpr
    linarith
  linarith

/-- Above an explicit residue-field cutoff, every target has a power-sum
solution with a unit coordinate. No condition on the characteristic is
needed for this finite-field statement. -/
theorem finite_field_power_even_unit_solution
    (k s : ℕ) (hk : 0 < k) (hs : 2 ≤ s)
    (hq : 2*(k-1)^(2*s) ≤ Fintype.card F) (b : F) :
    ∃ x : Fin (2*s) → F, (∑ i, x i^k) = b ∧ ∃ i, IsUnit (x i) := by
  let Sol := {x : Fin (2*s) → F // (∑ i, x i^k) = b}
  have hq0 : 0 < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  have hq2 : (2 : ℝ) ≤ Fintype.card F := by
    exact_mod_cast Fintype.one_lt_card
  have hpow : (8 : ℝ) ≤ (Fintype.card F : ℝ)^(2*s-1) := by
    calc
      _ = (2 : ℝ)^3 := by norm_num
      _ ≤ (Fintype.card F : ℝ)^3 := pow_le_pow_left₀ (by norm_num) hq2 _
      _ ≤ _ := pow_le_pow_right₀ (by linarith) (by omega)
  have hlow := (le_div_iff₀ (pow_pos hq0 (2*s-1))).mp
    (finite_field_power_even_normalized_lower k s hk hs hq b)
  have hcard : (1 : ℝ) < Nat.card Sol := by dsimp [Sol]; nlinarith
  by_contra hn
  have hz (x : Sol) : x.1 = 0 := by
    funext i
    by_contra hi
    exact hn ⟨x.1,x.2,i,isUnit_iff_ne_zero.mpr hi⟩
  letI : Subsingleton Sol := ⟨fun x y => Subtype.ext ((hz x).trans (hz y).symm)⟩
  have hcard' : Nat.card Sol ≤ 1 := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_le_one_iff_subsingleton.mpr inferInstance
  have hcardR : (Nat.card Sol : ℝ) ≤ 1 := by exact_mod_cast hcard'
  linarith

end WaringSiegel
#print axioms WaringSiegel.finite_field_power_even_normalized_error
#print axioms WaringSiegel.finite_field_power_even_unit_solution
