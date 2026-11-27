import WaringSiegel.WSL3MomentPointwiseInsertion

/-! # A positive-density corollary of a loss-free even moment

The counted targets are the integers between 1 and N that have a
representation by exactly t positive kth powers.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
open WaringSiegel WaringSiegel.WSL2 WaringSiegel.WSL3

namespace WaringLinear

def representedUpTo (k t N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun n => ∃ x : Fin t → ℕ,
    (∀ i, 0 < x i) ∧ ∑ i, (x i)^k = n)

theorem representedUpTo_mono {k t N N' : ℕ} (h : N ≤ N') :
    representedUpTo k t N ⊆ representedUpTo k t N' := by
  intro n hn
  obtain ⟨hn,hr⟩ := Finset.mem_filter.mp hn
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
    ⟨(Finset.mem_Icc.mp hn).1, (Finset.mem_Icc.mp hn).2.trans h⟩, hr⟩

/-- The mass, moment and actual represented targets at one scale. -/
theorem mass_le_card_mul_moment
    {α : Type*} [Fintype α] (k t P : ℕ) (ht : 0 < t)
    (x : α → ℕ) (hx : ∀ i, 0 < x i) (hP : ∀ i, x i ≤ P) (w : α → ℂ) :
    ‖∑ i, w i‖^(2*t) ≤ ((representedUpTo k t (t*P^k)).card : ℝ) *
      ∫ θ, ‖frequencySum (fun i : α => fun _ : Unit => ((x i)^k : ℤ)) w θ‖^(2*t) ∂latticeHaar := by
  let v : α → Unit → ℤ := fun i _ => ((x i)^k : ℤ)
  let N (u : Fin t → α) : ℕ := ∑ i, (x (u i))^k
  let E : ℕ → Unit → ℤ := fun m _ => (m : ℤ)
  have hv (u : Fin t → α) : (∑ i, v (u i)) = E (N u) := by
    ext _
    simp [v, E, N, Finset.sum_apply]
  have hN : (Finset.univ.image N) ⊆ representedUpTo k t (t*P^k) := by
    intro n hn
    obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp hn
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_Icc.mpr
      constructor
      · let i : Fin t := ⟨0,ht⟩
        have hi := Finset.single_le_sum (f := fun i : Fin t => (x (u i))^k)
          (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
        exact (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (hx _).ne')).trans hi
      · calc
          N u ≤ ∑ _i : Fin t, P^k := Finset.sum_le_sum (fun j _ => Nat.pow_le_pow_left (hP _) _)
          _ = t*P^k := by simp
    · exact ⟨fun i => x (u i),fun _ => hx _,rfl⟩
  have hcard : (Finset.univ.image (fun u : Fin t → α => ∑ i, v (u i))).card ≤
      (representedUpTo k t (t*P^k)).card := by
    simp_rw [hv]
    have he : (Finset.univ.image (fun u => E (N u))) = (Finset.univ.image N).image E := by
      rw [Finset.image_image]
      rfl
    rw [he]
    exact Finset.card_image_le.trans (Finset.card_le_card hN)
  have h := norm_sum_even_le_inserted_moment v w t
  exact h.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
    (integral_nonneg (fun _ => by positivity)))

/-- A pointwise bound along the scale t P^k extends to every sufficiently
large N with the explicit loss t 2^k. -/
theorem positive_density_from_scales (k t P₀ : ℕ) (hk : 0 < k) (ht : 0 < t)
    (c : ℝ) (hc : 0 < c)
    (h : ∀ P : ℕ, P₀ ≤ P → c*(P : ℝ)^k ≤ (representedUpTo k t (t*P^k)).card) :
    ∃ c' : ℝ, 0 < c' ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      c' * N ≤ (representedUpTo k t N).card := by
  refine ⟨c / ((t:ℝ)*2^k), by positivity, t*(max 1 P₀)^k, ?_⟩
  intro N hN
  have hb : ∃ p : ℕ, N < t*(p+1)^k := by
    refine ⟨N, ?_⟩
    exact (Nat.lt_succ_self N).trans_le ((Nat.le_self_pow hk.ne' _).trans
      (Nat.le_mul_of_pos_left _ ht))
  let p := Nat.find hb
  have hup : N < t*(p+1)^k := Nat.find_spec hb
  have hlo : max 1 P₀ ≤ p := by
    apply Nat.le_of_not_gt
    intro hn
    have hh := Nat.mul_le_mul_left t (Nat.pow_le_pow_left (Nat.succ_le_of_lt hn) k)
    exact (not_lt_of_ge (hh.trans hN)) hup
  have hp : 1 ≤ p := (le_max_left _ _).trans hlo
  have hnear : t*p^k ≤ N := by
    have hprev := Nat.find_min hb (m := p-1) (by change p-1 < p; omega)
    simpa only [show p-1+1 = p by omega, not_lt] using hprev
  have hcard : ((representedUpTo k t (t*p^k)).card : ℝ) ≤ (representedUpTo k t N).card := by
    exact_mod_cast (Finset.card_le_card (representedUpTo_mono (k := k) (t := t) hnear))
  have hscale := (h p ((le_max_right _ _).trans hlo)).trans hcard
  have hsmall : N ≤ t*(2*p)^k := hup.le.trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
  have hreal : (N:ℝ) ≤ (t:ℝ)*2^k*(p:ℝ)^k := by
    rw [mul_assoc, ← mul_pow]
    exact_mod_cast hsmall
  have hd : 0 < (t:ℝ)*2^k := by positivity
  calc
    c / ((t:ℝ)*2^k) * N ≤ c / ((t:ℝ)*2^k) * ((t:ℝ)*2^k*(p:ℝ)^k) :=
      mul_le_mul_of_nonneg_left hreal (by positivity)
    _ = c*(p:ℝ)^k := by field_simp
    _ ≤ _ := hscale

/-- Uniform mass and a sharp 2t-th moment give positive lower density for
the actual positive-power representation set. The indexing types, weights
and finite supports may all change with the height. -/
theorem positive_density_of_moment {α : ℕ → Type*} [∀ P, Fintype (α P)]
    (k t P₀ : ℕ) (hk : 0 < k) (ht : 0 < t)
    (x : (P : ℕ) → α P → ℕ) (w : (P : ℕ) → α P → ℂ) (c D : ℝ)
    (hc : 0 < c) (hD : 0 < D)
    (hpos : ∀ P ≥ P₀, ∀ i, 0 < x P i) (hbox : ∀ P ≥ P₀, ∀ i, x P i ≤ P)
    (hMass : ∀ P ≥ P₀, c*(P : ℝ) ≤ ‖∑ i, w P i‖)
    (hMoment : ∀ P ≥ P₀, (∫ θ, ‖frequencySum (fun i : α P => fun _ : Unit =>
        ((x P i)^k : ℤ)) (w P) θ‖^(2*t) ∂latticeHaar) ≤ D*(P:ℝ)^((2*t:ℕ)- (k:ℝ))) :
    ∃ c' : ℝ, 0 < c' ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      c'*N ≤ (representedUpTo k t N).card := by
  apply positive_density_from_scales k t (max 1 P₀) hk ht (c^(2*t)/D) (by positivity)
  intro P hP
  have hpositive : 0 < (P:ℝ) := by
    exact_mod_cast ((le_max_left 1 P₀).trans hP : 1 ≤ P)
  have hp₀ := (le_max_right 1 P₀).trans hP
  let R : ℝ := (representedUpTo k t (t*P^k)).card
  have hR : 0 ≤ R := Nat.cast_nonneg _
  have h :=
    (pow_le_pow_left₀ (a := c*(P:ℝ)) (by positivity) (hMass P hp₀) (2*t)).trans
      ((mass_le_card_mul_moment k t P ht (x P) (hpos P hp₀) (hbox P hp₀) (w P)).trans
      (mul_le_mul_of_nonneg_left (hMoment P hp₀) hR))
  have hprod : (P:ℝ)^((2*t:ℕ)-(k:ℝ)) * (P:ℝ)^k = (P:ℝ)^(2*t) := by
    rw [← Real.rpow_natCast (P:ℝ) k, ← Real.rpow_add hpositive, sub_add_cancel,
      Real.rpow_natCast]
  have h' := mul_le_mul_of_nonneg_right h (pow_nonneg hpositive.le k)
  rw [mul_pow] at h'
  change c^(2*t) * (P:ℝ)^(2*t) * (P:ℝ)^k ≤
      R * (D * (P:ℝ)^((2*t:ℕ) - (k:ℝ))) * (P:ℝ)^k at h'
  have hcancel : (c^(2*t)*(P:ℝ)^k) * (P:ℝ)^(2*t) ≤
      (R*D) * (P:ℝ)^(2*t) := by
    calc
      _ = c^(2*t) * (P:ℝ)^(2*t) * (P:ℝ)^k := by ring
      _ ≤ _ := h'
      _ = (R*D) * ((P:ℝ)^((2*t:ℕ) - (k:ℝ)) * (P:ℝ)^k) := by ring
      _ = _ := by rw [hprod]
  have hfinal := le_of_mul_le_mul_right hcancel (pow_pos hpositive _)
  change c^(2*t)/D * (P:ℝ)^k ≤ R
  rw [div_mul_eq_mul_div, div_le_iff₀ hD]
  exact hfinal

#print axioms mass_le_card_mul_moment
#print axioms positive_density_from_scales
#print axioms positive_density_of_moment

end WaringLinear
