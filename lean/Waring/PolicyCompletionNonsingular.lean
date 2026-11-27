import Waring.PolicyCompletionCongruence
import Waring.PolicyCompletionRoots
import Mathlib.Data.Int.ModEq

/-!
# The source nonsingular common-residue bound

The exact finite Cauchy grouping is combined here with the proved uniform
root estimate. For every bounded-degree integer polynomial family, all
parameter pairs with derivative coprime to w, and any finite tuple-frequency
family, collisions of `Psi(c,z)+w^k*U(u)` are bounded by

  `C * (number of parameters) * w^epsilon`

times the count with the same parameter and `z=z' (mod w^k)`.

The constants are uniform in every polynomial coefficient and every tuple
frequency. The root bound is discharged, rather than retained as an input.
This is the last nonsingular reduction in the fundamental lemma, printed
pages 239--240 of Wooley's 1990 thesis, Part III.
-/

noncomputable section
open scoped BigOperators

namespace Waring.PolicyCompletionCongruence
open AuxiliaryL2Grouping SeedCompletion PolicyCompletionRoots

/-- Polynomial residue classes inject into the actual nonsingular root sets
for each parameter. Integer representatives may have either sign. -/
theorem residueKeys_card_le_root_sum {κ : Type*} [DecidableEq κ]
    (A : Finset (κ × ℤ)) (F : κ → Polynomial ℤ) {q : ℕ} (hq : 0 < q)
    (hgood : ∀ x ∈ A, IsCoprime (q : ℤ) ((F x.1).derivative.eval x.2))
    (n : ℤ) :
    (residueKeys A (fun c z => (F c).eval z) (q : ℤ) n).card ≤
      ∑ c ∈ A.image Prod.fst, (nonsingularResidueRoots (F c) n q 1).card := by
  classical
  let roots := fun c => (nonsingularResidueRoots (F c) n q 1).image
    (fun r : ℕ => (c,(r : ℤ)))
  have hsub : residueKeys A (fun c z => (F c).eval z) (q : ℤ) n ⊆
      (A.image Prod.fst).biUnion roots := by
    intro key hkey
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hkey
    rcases Finset.mem_filter.mp hx with ⟨hx,hmod⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨x.1,Finset.mem_image_of_mem Prod.fst hx,?_⟩
    apply Finset.mem_image.mpr
    refine ⟨(x.2 % (q : ℤ)).toNat,?_,?_⟩
    · apply integer_residue_mem_roots (F x.1) n x.2 hq _ (hgood x hx)
      exact Int.modEq_iff_dvd.mp hmod.symm
    · congr 1
      exact Int.toNat_of_nonneg
        (Int.emod_nonneg x.2 (by exact_mod_cast hq.ne'))
  calc
    _ ≤ ((A.image Prod.fst).biUnion roots).card := Finset.card_le_card hsub
    _ ≤ ∑ c ∈ A.image Prod.fst, (roots c).card := Finset.card_biUnion_le
    _ ≤ ∑ c ∈ A.image Prod.fst, (nonsingularResidueRoots (F c) n q 1).card := by
      apply Finset.sum_le_sum
      intro c hc
      exact Finset.card_image_le

/-- A uniform real bound on all actual residue fibers bounds their finite
maximum, including an empty parameter domain. -/
theorem residueCapacity_le_of_bound {κ : Type*} [DecidableEq κ]
    (A : Finset (κ × ℤ)) (Ψ : κ → ℤ → ℤ) (q : ℤ)
    {D : ℝ} (hD : 0 ≤ D)
    (hbound : ∀ n : ℤ, ((residueKeys A Ψ q n).card : ℝ) ≤ D) :
    (residueCapacity A Ψ q : ℝ) ≤ D := by
  classical
  by_cases hA : A.Nonempty
  · have hN := hA.image (fun x => Ψ x.1 x.2 % q)
    obtain ⟨n,hn,hmax⟩ := Finset.exists_mem_eq_sup _ hN
      (fun n => (residueKeys A Ψ q n).card)
    unfold residueCapacity
    rw [hmax]
    exact hbound n
  · rw [Finset.not_nonempty_iff_eq_empty.mp hA]
    simpa [residueCapacity] using hD

/-- The complete uniform nonsingular residue multiplier w^epsilon. -/
theorem nonsingular_residueCapacity_le {κ : Type*} [DecidableEq κ]
    (d k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : Finset (κ × ℤ)) (F : κ → Polynomial ℤ),
      (∀ c ∈ A.image Prod.fst, (F c).natDegree ≤ d) →
      ∀ w : ℕ, 0 < w →
      (∀ x ∈ A, IsCoprime (w : ℤ) ((F x.1).derivative.eval x.2)) →
      (residueCapacity A (fun c z => (F c).eval z) ((w : ℤ)^k) : ℝ) ≤
        C*((A.image Prod.fst).card : ℝ)*(w : ℝ)^ε := by
  obtain ⟨C,hC,hroot⟩ := nonsingular_power_roots_card_le_rpow d k hε
  refine ⟨C,hC,?_⟩
  intro A F hdeg w hw hgood
  have hq : 0 < w^k := pow_pos hw k
  have hgoodq : ∀ x ∈ A, IsCoprime ((w^k : ℕ) : ℤ)
      ((F x.1).derivative.eval x.2) := by
    intro x hx
    simpa only [Nat.cast_pow] using (hgood x hx).pow_left (m := k)
  apply residueCapacity_le_of_bound A (fun c z => (F c).eval z) ((w : ℤ)^k)
    (by positivity)
  intro n
  have hcount : ((residueKeys A (fun c z => (F c).eval z) ((w^k : ℕ) : ℤ) n).card : ℝ) ≤
      ∑ c ∈ A.image Prod.fst, ((nonsingularResidueRoots (F c) n (w^k) 1).card : ℝ) := by
    exact_mod_cast residueKeys_card_le_root_sum A F hq hgoodq n
  calc
    _ = ((residueKeys A (fun c z => (F c).eval z) ((w^k : ℕ) : ℤ) n).card : ℝ) := by
      rw [Nat.cast_pow]
    _ ≤ ∑ c ∈ A.image Prod.fst, ((nonsingularResidueRoots (F c) n (w^k) 1).card : ℝ) := hcount
    _ ≤ ∑ _c ∈ A.image Prod.fst, C*(w : ℝ)^ε :=
      Finset.sum_le_sum (fun c hc => hroot (F c) (hdeg c hc) n w hw)
    _ = C*((A.image Prod.fst).card : ℝ)*(w : ℝ)^ε := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      ring

/-- The actual source common-modulus reduction, with all root-count premises
discharged and the full solution count preserved. -/
theorem nonsingular_common_residue_collision_bound {κ ι : Type*} [DecidableEq κ]
    (d k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : Finset (κ × ℤ)) (B : Finset ι)
      (F : κ → Polynomial ℤ) (U : ι → ℤ),
      (∀ c ∈ A.image Prod.fst, (F c).natDegree ≤ d) →
      ∀ w : ℕ, 0 < w →
      (∀ x ∈ A, IsCoprime (w : ℤ) ((F x.1).derivative.eval x.2)) →
      ((collisionPairs (A ×ˢ B)
        (liftedFrequency (fun c z => (F c).eval z) U ((w : ℤ)^k))).card : ℝ) ≤
      (C*((A.image Prod.fst).card : ℝ)*(w : ℝ)^ε) *
        ((sameClassCollisions (A ×ˢ B)
          (liftedFrequency (fun c z => (F c).eval z) U ((w : ℤ)^k))
          (residueKey ((w : ℤ)^k))).card : ℝ) := by
  obtain ⟨C,hC,hcapacity⟩ := nonsingular_residueCapacity_le (κ := κ) d k hε
  refine ⟨C,hC,?_⟩
  intro A B F U hdeg w hw hgood
  exact (common_residue_collision_bound A B (fun c z => (F c).eval z) U ((w : ℤ)^k)).trans
    (mul_le_mul_of_nonneg_right (hcapacity A F hdeg w hw hgood) (by positivity))

#print axioms residueKeys_card_le_root_sum
#print axioms nonsingular_residueCapacity_le
#print axioms nonsingular_common_residue_collision_bound

end Waring.PolicyCompletionCongruence
