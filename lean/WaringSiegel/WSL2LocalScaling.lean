import WaringSiegel.WSL2LocalPrimitive

/-!
# Precision fibers and scaling singular cubic solutions

Multiplication by a uniformizer identifies the lower-precision quotient with
the zero-residue fiber. These equivalences make singular solution counts
reducible to lower-precision cubic counts.
-/

noncomputable section

open IsLocalRing
open scoped BigOperators

namespace WaringSiegel

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- Uniformizer multiplication on finite quotients, with one digit of shift. -/
def uniformizerMulQuotient {π : R} (hπ : Irreducible π) (n : ℕ) :
    R ⧸ maximalIdeal R ^ n → R ⧸ maximalIdeal R ^ (n + 1) :=
  Quotient.map' (fun x => π * x) (by
    intro x y h
    rw [Submodule.quotientRel_def] at h ⊢
    rw [← mul_sub]
    simpa only [pow_one] using (uniformizer_power_cancel_mem hπ 1 n).mpr h)

@[simp] theorem uniformizerMulQuotient_mk {π : R} (hπ : Irreducible π) (n : ℕ) (x : R) :
    uniformizerMulQuotient hπ n (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (π * x) := rfl

theorem uniformizerMulQuotient_injective {π : R} (hπ : Irreducible π) (n : ℕ) :
    Function.Injective (uniformizerMulQuotient hπ n) := by
  intro x y h
  obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective y
  apply Ideal.Quotient.eq.mpr
  have hd := Ideal.Quotient.eq.mp h
  rw [← mul_sub] at hd
  exact (uniformizer_power_cancel_mem hπ 1 n).mp (by simpa only [pow_one] using hd)

theorem uniformizerMulQuotient_residue_zero {π : R} (hπ : Irreducible π)
    (n : ℕ) (x : R ⧸ maximalIdeal R ^ n) :
    localResidueReduction _ (Ideal.pow_le_self (Nat.succ_ne_zero n))
      (uniformizerMulQuotient hπ n x) = 0 := by
  obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [uniformizerMulQuotient_mk, localResidueReduction_mk, map_mul]
  have hπm : π ∈ maximalIdeal R := hπ.maximalIdeal_eq.symm ▸ Ideal.subset_span (by simp)
  rw [(residue_eq_zero_iff π).mpr hπm, zero_mul]

def uniformizerZeroResidueEquiv {π : R} (hπ : Irreducible π) (n : ℕ) :
    (R ⧸ maximalIdeal R ^ n) ≃
      {z : R ⧸ maximalIdeal R ^ (n + 1) //
        localResidueReduction _ (Ideal.pow_le_self (Nat.succ_ne_zero n)) z = 0} :=
  Equiv.ofBijective (fun x => ⟨uniformizerMulQuotient hπ n x,
    uniformizerMulQuotient_residue_zero hπ n x⟩) (by
    constructor
    · intro x y h
      exact uniformizerMulQuotient_injective hπ n (congrArg Subtype.val h)
    · intro z
      obtain ⟨u, hu⟩ := Ideal.Quotient.mk_surjective z.val
      have hum : u ∈ maximalIdeal R := by
        apply (residue_eq_zero_iff u).mp
        rw [← localResidueReduction_mk _ (Ideal.pow_le_self (Nat.succ_ne_zero n)), hu]
        exact z.property
      rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hum
      obtain ⟨v, rfl⟩ := hum
      exact ⟨Ideal.Quotient.mk _ v, Subtype.ext hu⟩)

/-- Every reduction fiber between DVR quotient levels has the expected size. -/
theorem dvr_reduction_fiber_card [Finite (ResidueField R)] (n r : ℕ)
    (z : R ⧸ maximalIdeal R ^ n) :
    Nat.card {x : R ⧸ maximalIdeal R ^ (n + r) //
      Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_add_right n r)) x = z} =
      Nat.card (ResidueField R) ^ r := by
  let f := (Ideal.Quotient.factor
    (Ideal.pow_le_pow_right (I := maximalIdeal R) (Nat.le_add_right n r))).toAddMonoidHom
  have hf : Function.Surjective f := Ideal.Quotient.factor_surjective
    (Ideal.pow_le_pow_right (Nat.le_add_right n r))
  change Nat.card {x : R ⧸ maximalIdeal R ^ (n + r) // f x = z} = _
  have he : Nat.card {x : R ⧸ maximalIdeal R ^ (n + r) // f x = z} =
      Nat.card f.ker := Nat.card_congr (AddMonoidHom.fiberEquivKerOfSurjective hf z)
  rw [he]
  have hq : 0 < Nat.card (ResidueField R) := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_right (pow_pos hq n)
  have hk := f.ker.card_mul_index
  rw [AddSubgroup.index_ker, AddMonoidHom.range_eq_top.mpr hf,
    AddSubgroup.card_top, dvr_power_quotient_card, dvr_power_quotient_card] at hk
  exact hk.trans (by rw [pow_add, Nat.mul_comm])

theorem dvr_reduction_fiber_card_of_le [Finite (ResidueField R)]
    (n e : ℕ) (hne : n ≤ e) (z : R ⧸ maximalIdeal R ^ n) :
    Nat.card {x : R ⧸ maximalIdeal R ^ e //
      Ideal.Quotient.factor (Ideal.pow_le_pow_right hne) x = z} =
      Nat.card (ResidueField R) ^ (e - n) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hne
  simpa only [Nat.add_sub_cancel_left] using dvr_reduction_fiber_card n r z

def CubicCongruenceTuples (R : Type*) [CommRing R] [IsLocalRing R]
    (n r s : ℕ) (a : R) :=
  {x : Fin s → R ⧸ maximalIdeal R ^ (n + r) //
    (∑ i, (Ideal.Quotient.factor
      (Ideal.pow_le_pow_right (Nat.le_add_right n r)) (x i)) ^ 3) =
        Ideal.Quotient.mk (maximalIdeal R ^ n) a}

instance cubicCongruenceTuples_finite [Finite (ResidueField R)]
    (n r s : ℕ) (a : R) : Finite (CubicCongruenceTuples R n r s a) := by
  letI := dvr_power_quotient_finite (R := R) (n + r)
  unfold CubicCongruenceTuples
  infer_instance

def cubicCongruenceTuplesEquiv (n r s : ℕ) (a : R) :
    CubicCongruenceTuples R n r s a ≃
      (Σ b : LocalCubicSolutions R (maximalIdeal R ^ n) s a,
        ∀ i : Fin s, {x : R ⧸ maximalIdeal R ^ (n + r) //
          Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_add_right n r)) x = b.val i}) where
  toFun x := ⟨⟨fun i => Ideal.Quotient.factor
    (Ideal.pow_le_pow_right (Nat.le_add_right n r)) (x.val i), x.property⟩,
      fun i => ⟨x.val i, rfl⟩⟩
  invFun x := ⟨fun i => (x.2 i).val, by
    simpa only [(x.2 _).property] using x.1.property⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv x := by
    rcases x with ⟨⟨b, hb⟩, x⟩
    have he : (fun i => Ideal.Quotient.factor
        (Ideal.pow_le_pow_right (Nat.le_add_right n r)) (x i).val) = b :=
      funext (fun i => (x i).property)
    apply Sigma.ext (Subtype.ext he)
    apply Function.hfunext rfl
    intro i j hij
    cases eq_of_heq hij
    apply (Subtype.heq_iff_coe_eq (fun z => by dsimp; rw [(x i).property])).mpr
    rfl

/-- Requiring a congruence at a lower precision leaves `r` free digits in
all `s` coordinates. -/
theorem cubic_congruence_tuples_card [Finite (ResidueField R)]
    (n r s : ℕ) (a : R) :
    Nat.card (CubicCongruenceTuples R n r s a) =
      localCubicSolutionCount R (maximalIdeal R ^ n) s a *
        Nat.card (ResidueField R) ^ (s * r) := by
  classical
  letI := dvr_power_quotient_finite (R := R) n
  letI := dvr_power_quotient_finite (R := R) (n + r)
  letI := Fintype.ofFinite (LocalCubicSolutions R (maximalIdeal R ^ n) s a)
  rw [Nat.card_congr (cubicCongruenceTuplesEquiv n r s a), Nat.card_sigma]
  simp only [Nat.card_pi, dvr_reduction_fiber_card, Finset.prod_const,
    Finset.card_univ, Nat.card_fin, ← pow_mul, Nat.mul_comm r s,
    Finset.sum_const, nsmul_eq_mul, ← Nat.card_eq_fintype_card,
    localCubicSolutionCount, Nat.cast_id]

end WaringSiegel

#print axioms WaringSiegel.uniformizerZeroResidueEquiv
#print axioms WaringSiegel.dvr_reduction_fiber_card
