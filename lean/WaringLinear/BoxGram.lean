import WaringLinear.IdealGram
import WaringSiegel.WSL2MomentProgressions

/-! # The small-conductor block on a box of algebraic integers

For a balanced archimedean box the small-conductor Gram bound is explicit.
The field degree occurs only in its constant and the conversion to volume.
-/
noncomputable section
open scoped BigOperators Classical NumberField nonZeroDivisors
open NumberField Module UniqueFactorizationMonoid
open WaringSiegel WaringSiegel.WSL2

namespace WaringLinear
variable {K X J : Type*} [Field K] [NumberField K] [Fintype X] [Fintype J]

theorem unit_residue_box_card
    (I : Ideal (𝓞 K)) (hI : I ≠ 0) (P : ℝ) (hP : 0 < P)
    (n : X → 𝓞 K) (hn : Function.Injective n)
    (hbox : ∀ x, ∀ v : InfinitePlace K, v (n x : K) ≤ P)
    (r : X → (𝓞 K ⧸ I)ˣ) (hr : ∀ x, (r x : 𝓞 K ⧸ I) = Ideal.Quotient.mk I (n x))
    (z : (𝓞 K ⧸ I)ˣ) :
    (Nat.card {x // r x=z} : ℝ) ≤ (3:ℝ)^finrank ℚ K *
      (1 + P^finrank ℚ K / (Ideal.absNorm I:ℝ)) := by
  obtain ⟨b,hb⟩ := Ideal.Quotient.mk_surjective (z : 𝓞 K ⧸ I)
  let A : FractionalIdeal (𝓞 K)⁰ K := I
  have hA : A ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr hI
  let nodes : {x // r x=z} → 𝓞 K := fun x => n x.1
  have hmem (x : {x // r x=z}) : (nodes x : K)-(b:K) ∈ A := by
    have he : Ideal.Quotient.mk I (nodes x) = Ideal.Quotient.mk I b := by
      change Ideal.Quotient.mk I (n x.1) = _
      rw [← hr, x.2,hb]
    have hm := FractionalIdeal.mem_coeIdeal_of_mem (𝓞 K)⁰ (P := K) (Ideal.Quotient.eq.mp he)
    simpa only [map_sub] using hm
  have h := indexed_integer_coset_card_bound A hA (b:K) P hP nodes
    (hn.comp Subtype.val_injective) hmem (fun x => hbox x.1)
  simpa only [Nat.card_eq_fintype_card,A,FractionalIdeal.coeIdeal_absNorm,Rat.cast_natCast] using h

/-- For NI ≤ box volume V the coefficient is at most 2 ⋅ 3^[K:Q] ⋅ k^ω(I) ⋅ V. -/
theorem boxed_ideal_gram (I : Ideal (𝓞 K)) (hI : I ≠ 0) (k : ℕ) (hk : 0 < k)
    (hgood : ∀ Q ∈ (normalizedFactors I).toFinset, (k : 𝓞 K) ∉ Q)
    (P : ℝ) (hP : 0 < P) (hsmall : (Ideal.absNorm I : ℝ) ≤ P^finrank ℚ K)
    (n : X → 𝓞 K) (hn : Function.Injective n)
    (hbox : ∀ x, ∀ v : InfinitePlace K, v (n x : K) ≤ P)
    (r : X → (𝓞 K ⧸ I)ˣ) (hr : ∀ x, (r x : 𝓞 K ⧸ I) = Ideal.Quotient.mk I (n x))
    (χ : J → AddChar (𝓞 K ⧸ I) ℂ) (hχ : Function.Injective χ) (w : J → ℂ) :
    (∑ x, ‖∑ j, w j * χ j (Ideal.Quotient.mk I (n x^k))‖^2) ≤
      2*(3:ℝ)^finrank ℚ K*(k:ℝ)^(normalizedFactors I).toFinset.card *
        P^finrank ℚ K * ∑ j, ‖w j‖^2 := by
  let V : ℝ := P^finrank ℚ K
  let N : ℝ := Ideal.absNorm I
  let U : ℝ := (k:ℝ)^(normalizedFactors I).toFinset.card
  let C : ℝ := (3:ℝ)^finrank ℚ K
  let L : ℕ := ⌊C*(1+V/N)⌋₊
  have hN : 0 < N := by
    unfold N
    exact_mod_cast Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.mp hI)
  have hV : 0 < V := pow_pos hP _
  have hU : 0 ≤ U := by unfold U; positivity
  have hC : 0 ≤ C := by unfold C; positivity
  have hL (z) : Nat.card {x // r x=z} ≤ L :=
    Nat.le_floor (unit_residue_box_card I hI P hP n hn hbox r hr z)
  have hg := ideal_sampled_character_synthesis I hI k L hk hgood r hL χ hχ w
  simp_rw [hr, ← map_pow] at hg
  push_cast at hg
  apply hg.trans
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  change (L:ℝ)*U*N ≤ 2*C*U*V
  have hfloor : (L:ℝ) ≤ C*(1+V/N) := Nat.floor_le (by positivity)
  calc
    _ ≤ (C*(1+V/N))*U*N :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hfloor hU) hN.le
    _ = C*U*(N+V) := by field_simp
    _ ≤ C*U*(V+V) := mul_le_mul_of_nonneg_left (add_le_add_right hsmall _) (mul_nonneg hC hU)
    _ = _ := by ring

#print axioms boxed_ideal_gram

end WaringLinear
