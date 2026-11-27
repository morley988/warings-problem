import WaringSiegel.WSL2LocalOriginalModified

/-!
# The ordinary local factors away from the auxiliary prime

When the auxiliary coefficient is a unit in a prime-power quotient,
multiplication in the four y coordinates is a bijection. The unrestricted
scaled congruence count therefore equals the ordinary eight-cube count.
-/

noncomputable section
open IsLocalRing
open scoped NumberField BigOperators Classical

namespace WaringSiegel

def scaledCubicTupleEquiv {A : Type*} [CommRing A] (u : Aˣ) :
    ((Fin 4 → A) × (Fin 4 → A)) ≃ (Fin 8 → A) where
  toFun z := Fin.append z.2 (fun i => u.val * z.1 i)
  invFun z := (fun (i : Fin 4) => u.inv * z (Fin.natAdd 4 i),
    fun (i : Fin 4) => z (Fin.castAdd 4 i))
  left_inv z := by
    apply Prod.ext <;> funext i
    · simp only [Fin.append_right, ← mul_assoc, u.inv_val, one_mul]
    · simp only [Fin.append_left]
  right_inv z := by
    change Fin.append (fun (i : Fin 4) => z (Fin.castAdd 4 i))
      (fun (i : Fin 4) => u.val * (u.inv * z (Fin.natAdd 4 i))) = z
    simp only [← mul_assoc, u.val_inv, one_mul, Fin.append_castAdd_natAdd]

theorem scaledCubicTupleEquiv_sum {A : Type*} [CommRing A] (u : Aˣ)
    (z : (Fin 4 → A) × (Fin 4 → A)) :
    (∑ i, scaledCubicTupleEquiv u z i ^ 3) =
      (∑ i, z.2 i ^ 3) + (∑ i, (u.val * z.1 i) ^ 3) := by
  change (∑ i : Fin (4 + 4), (Fin.append z.2 (fun j => u.val * z.1 j)) i ^ 3) = _
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]

def ScaledLocalCubicSolutions
    (R : Type*) [CommRing R] (I : Ideal R) (p a : R) :=
  {z : (Fin 4 → R ⧸ I) × (Fin 4 → R ⧸ I) //
    (∑ i, z.2 i ^ 3) + (∑ i, (Ideal.Quotient.mk I p * z.1 i) ^ 3) =
      Ideal.Quotient.mk I a}

theorem scaled_local_cubic_count_eq_of_isUnit
    {R : Type*} [CommRing R] (I : Ideal R) (p a : R)
    (hp : IsUnit (Ideal.Quotient.mk I p)) :
    Nat.card (ScaledLocalCubicSolutions R I p a) = localCubicSolutionCount R I 8 a := by
  obtain ⟨u, hu⟩ := hp
  unfold localCubicSolutionCount
  apply Nat.card_congr
  exact (scaledCubicTupleEquiv u).subtypeEquiv (fun z => by
    change ((∑ i, z.2 i ^ 3) + (∑ i, (Ideal.Quotient.mk I p * z.1 i) ^ 3) =
      Ideal.Quotient.mk I a) ↔ (∑ i, scaledCubicTupleEquiv u z i ^ 3) = Ideal.Quotient.mk I a
    rw [scaledCubicTupleEquiv_sum, hu])

variable {K : Type*} [Field K] [NumberField K]

theorem original_prime_power_isUnit_of_not_mem
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) {p : 𝓞 K}
    (hp : p ∉ v.asIdeal) (e : ℕ) :
    IsUnit (Ideal.Quotient.mk (v.asIdeal ^ e) p) := by
  let f := primePowerCompletionEquiv v e
  have hp' : IsUnit (algebraMap (𝓞 K) (v.adicCompletionIntegers K) p) := by
    apply (residue_ne_zero_iff_isUnit _).mp
    intro h
    apply hp
    have hm : algebraMap (𝓞 K) (v.adicCompletionIntegers K) p ∈
        maximalIdeal (v.adicCompletionIntegers K) := (residue_eq_zero_iff _).mp h
    simpa only [pow_one] using (completion_mem_maximalIdeal_pow_iff v p 1).mp
      (by simpa only [pow_one] using hm)
  have hu : IsUnit (f (Ideal.Quotient.mk (v.asIdeal ^ e) p)) := by
    change IsUnit (Ideal.Quotient.mk (maximalIdeal (v.adicCompletionIntegers K) ^ e)
      (algebraMap (𝓞 K) (v.adicCompletionIntegers K) p))
    exact hp'.map (Ideal.Quotient.mk (maximalIdeal (v.adicCompletionIntegers K) ^ e))
  have hu' := hu.map f.symm.toRingHom
  change IsUnit (f.symm (f (Ideal.Quotient.mk (v.asIdeal ^ e) p))) at hu'
  simpa only [f.symm_apply_apply] using hu' 

/-- At primes avoiding p, the actual original scaled congruence count is the
ordinary eight-cube count, at every prime-power exponent. -/
theorem original_scaled_cubic_count_eq_ordinary
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) {p : 𝓞 K}
    (hp : p ∉ v.asIdeal) (ν : 𝓞 K) (e : ℕ) :
    Nat.card (ScaledLocalCubicSolutions (𝓞 K) (v.asIdeal ^ e) p ν) =
      localCubicSolutionCount (𝓞 K) (v.asIdeal ^ e) 8 ν :=
  scaled_local_cubic_count_eq_of_isUnit _ _ _ (original_prime_power_isUnit_of_not_mem v hp e)

end WaringSiegel

#print axioms WaringSiegel.original_scaled_cubic_count_eq_ordinary
