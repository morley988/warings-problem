import WaringSiegel.WSL3MomentLocalPowerVariableError

/-! # Eighth-moment finite-field error for arbitrary variable counts -/
noncomputable section
set_option maxHeartbeats 1200000
open IsLocalRing
open scoped BigOperators Classical
namespace WaringSiegel.WSL4Local
open WaringSiegel.WSL3
variable {F : Type*} [Field F] [Fintype F]

theorem finite_field_power_eight_normalized_error
    (k p : ℕ) (hk : 0<k) (hp : 8≤p) (b : F) :
    |(Nat.card {x : Fin p → F // (∑ i,x i^k)=b}:ℝ)/(Fintype.card F:ℝ)^(p-1)-1| ≤
      ((k-1:ℕ):ℝ)^8/(Fintype.card F:ℝ)^3 := by
  have hq : (Fintype.card F:ℂ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  have hqR : (Fintype.card F:ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  have h1 : finiteRingPowerCharacterTerm k p b (1:AddChar F ℂ)=1 := by
    simp [finiteRingPowerCharacterTerm,finiteRingPowerSum,hq]
  have hsum := Finset.sum_erase_add (Finset.univ:Finset (AddChar F ℂ))
    (finiteRingPowerCharacterTerm k p b) (Finset.mem_univ 1)
  have hcount := finite_ring_power_normalized_character_count k p (by omega) b
  change (∑ ψ : AddChar F ℂ,finiteRingPowerCharacterTerm k p b ψ)=_ at hcount
  rw [h1,hcount] at hsum
  have herr : (Nat.card {x : Fin p → F // (∑ i,x i^k)=b}:ℂ)/(Fintype.card F:ℂ)^(p-1)-1=
      ∑ ψ∈Finset.univ.erase (1:AddChar F ℂ),finiteRingPowerCharacterTerm k p b ψ := by
    linear_combination -hsum
  have hterm (ψ : AddChar F ℂ) (hψ : ψ≠1) :
      ‖finiteRingPowerCharacterTerm k p b ψ‖≤((k-1:ℕ):ℝ)^8/(Fintype.card F:ℝ)^4 := by
    apply (finite_field_power_term_order_mono k 8 p hp b ψ).trans
    simpa only [show 2*4=8 from rfl] using finite_field_power_character_term_even_bound k 4 hk b ψ hψ
  have hb : ‖(Nat.card {x : Fin p → F // (∑ i,x i^k)=b}:ℂ)/(Fintype.card F:ℂ)^(p-1)-1‖≤
      ((k-1:ℕ):ℝ)^8/(Fintype.card F:ℝ)^3 := by
    rw [herr]
    calc
      _ ≤ ∑ ψ∈Finset.univ.erase (1:AddChar F ℂ),‖finiteRingPowerCharacterTerm k p b ψ‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _ψ∈Finset.univ.erase (1:AddChar F ℂ),((k-1:ℕ):ℝ)^8/(Fintype.card F:ℝ)^4 :=
        Finset.sum_le_sum (fun ψ hψ => hterm ψ (Finset.mem_erase.mp hψ).1)
      _ ≤ (Fintype.card F:ℝ)*(((k-1:ℕ):ℝ)^8/(Fintype.card F:ℝ)^4) := by
        rw [Finset.sum_const,nsmul_eq_mul]
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have hc := Finset.card_le_card (Finset.erase_subset (1:AddChar F ℂ) Finset.univ)
        simpa only [Finset.card_univ,AddChar.card_eq] using (Nat.cast_le (α:=ℝ)).mpr hc
      _ = _ := by field_simp
  have he : (Nat.card {x : Fin p → F // (∑ i,x i^k)=b}:ℂ)/(Fintype.card F:ℂ)^(p-1)-1=
      (((Nat.card {x : Fin p → F // (∑ i,x i^k)=b}:ℝ)/(Fintype.card F:ℝ)^(p-1)-1:ℝ):ℂ) := by
    push_cast
    rfl
  simpa only [he,Complex.norm_real,Real.norm_eq_abs] using hb

theorem normalized_local_power_eight_good_tail
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [Finite (ResidueField R)]
    (k p : ℕ) (hk : 0<k) (hp : 8≤p) (hku : IsUnit (k:R)) (n : ℕ) (a : R) :
    1-(((k-1:ℕ):ℝ)^8+1)/(Nat.card (ResidueField R):ℝ)^3 ≤
      normalizedLocalPowerCount R k p (n+1) a := by
  letI := Fintype.ofFinite (ResidueField R)
  have herr := (abs_le.mp (finite_field_power_eight_normalized_error k p hk hp (residue R a))).1
  simp only [← Nat.card_eq_fintype_card] at herr
  have hcard : (Nat.card {x : Fin p → ResidueField R // (∑ i,x i^k)=residue R a}:ℝ) ≤
      (Nat.card (PrimitivePowerResidues k R p a):ℝ)+1 := by
    exact_mod_cast residue_power_count_le_primitive_add_one k p a
  have hq : 0<(Nat.card (ResidueField R):ℝ) := by exact_mod_cast Nat.card_pos
  have hq1 : 1≤(Nat.card (ResidueField R):ℝ) := by exact_mod_cast Nat.card_pos
  have hdiv := div_le_div_of_nonneg_right hcard (pow_pos hq (p-1)).le
  rw [add_div] at hdiv
  have hpow : (Nat.card (ResidueField R):ℝ)^3≤(Nat.card (ResidueField R):ℝ)^(p-1) :=
    pow_le_pow_right₀ hq1 (by omega)
  have hsmall := div_le_div_of_nonneg_left (show (0:ℝ)≤1 by norm_num) (pow_pos hq 3) hpow
  have hres : 1-(((k-1:ℕ):ℝ)^8+1)/(Nat.card (ResidueField R):ℝ)^3 ≤
      (Nat.card (PrimitivePowerResidues k R p a):ℝ)/(Nat.card (ResidueField R):ℝ)^(p-1) := by
    rw [add_div]
    linarith
  have he := normalized_primitive_local_power_count_eq k hk hku (p-1) n a
  rw [Nat.sub_add_cancel (show 1≤p by omega)] at he
  apply hres.trans
  rw [← he]
  exact primitive_normalized_power_le_full k p n a

#print axioms finite_field_power_eight_normalized_error
#print axioms normalized_local_power_eight_good_tail
end WaringSiegel.WSL4Local
