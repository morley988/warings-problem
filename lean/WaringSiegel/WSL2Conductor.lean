import WaringSiegel.WSL2ClosePairs
import WaringSiegel.InverseDifferentCoordinates

/-!
# WSL2: actual conductor ideals and affine-line congruences

For a fractional ideal I and γ in K, the conductor is the integral ideal
{a ∈ O_K : aγ ∈ I}. For I equal to the inverse different this is the
conductor ideal used to define the manuscript's rational major arcs.
-/

noncomputable section
open scoped NumberField nonZeroDivisors BigOperators Classical
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module

namespace WaringSiegel
variable {K : Type*} [Field K] [NumberField K]

def conductorIdeal (I : FractionalIdeal (𝓞 K)⁰ K) (γ : K) : Ideal (𝓞 K) where
  carrier := {a | (a : K) * γ ∈ I}
  zero_mem' := by
    simp only [Set.mem_setOf_eq, RingOfIntegers.coe_eq_algebraMap, map_zero, zero_mul]
    exact I.zero_mem
  add_mem' := by
    intro a b ha hb
    change (((a + b : 𝓞 K) : K) * γ) ∈ I
    simpa only [RingOfIntegers.coe_eq_algebraMap, map_add, add_mul] using
      (I : Submodule (𝓞 K) K).add_mem ha hb
  smul_mem' := by
    intro a b hb
    have h := (I : Submodule (𝓞 K) K).smul_mem a hb
    change (((a * b : 𝓞 K) : K) * γ) ∈ I
    simpa only [Algebra.smul_def, map_mul, ← RingOfIntegers.coe_eq_algebraMap, mul_assoc] using h

@[simp] theorem mem_conductorIdeal (I : FractionalIdeal (𝓞 K)⁰ K) (γ : K) (a : 𝓞 K) :
    a ∈ conductorIdeal I γ ↔ (a : K) * γ ∈ I := Iff.rfl

theorem conductorIdeal_ne_zero (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0) (γ : K) :
    conductorIdeal I γ ≠ ⊥ := by
  obtain ⟨c, hc, hcI⟩ := FractionalIdeal.exists_ne_zero_mem_isInteger hI
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := 𝓞 K) γ
  have hb0 : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  have hbK : (b : K) ≠ 0 := by exact_mod_cast hb0
  have hbc : b * c ∈ conductorIdeal I γ := by
    change ((b * c : 𝓞 K) : K) * γ ∈ I
    have hm := (I : Submodule (𝓞 K) K).smul_mem a hcI
    have heq : ((b * c : 𝓞 K) : K) * γ = (a : K) * (c : K) := by
      rw [← hab]
      push_cast
      field_simp
    rw [heq]
    simpa only [Algebra.smul_def, ← RingOfIntegers.coe_eq_algebraMap] using hm
  intro hz
  have hzero : b * c = 0 := by simpa only [hz, Ideal.mem_bot] using hbc
  exact mul_ne_zero hb0 hc hzero

theorem conductorIdeal_absNorm_pos (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0) (γ : K) :
    0 < Ideal.absNorm (conductorIdeal I γ) :=
  Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.mp (conductorIdeal_ne_zero I hI γ))

theorem conductorIdeal_add_lattice (I : FractionalIdeal (𝓞 K)⁰ K) (γ δ : K) (hδ : δ ∈ I) :
    conductorIdeal I (γ + δ) = conductorIdeal I γ := by
  ext a
  have haδ : (a : K) * δ ∈ I := by
    simpa only [Algebra.smul_def, ← RingOfIntegers.coe_eq_algebraMap] using
      (I : Submodule (𝓞 K) K).smul_mem a hδ
  simp only [mem_conductorIdeal, mul_add]
  constructor
  · intro h
    simpa only [add_sub_cancel_right] using (I : Submodule (𝓞 K) K).sub_mem h haδ
  · intro h
    exact (I : Submodule (𝓞 K) K).add_mem h haδ

theorem conductorIdeal_zero (I : FractionalIdeal (𝓞 K)⁰ K) :
    conductorIdeal I 0 = ⊤ := by
  ext a
  simp only [mem_conductorIdeal, mul_zero, Submodule.mem_top, iff_true]
  exact I.zero_mem

/-- The inverse different is nonzero because it contains each nonzero
trace-dual basis vector. -/
theorem inverseDifferent_ne_zero : inverseDifferent K ≠ 0 := by
  let i : NumberFieldCoordinateIndex K := Classical.choice inferInstance
  have hi := integralTraceDualBasis_mem_inverseDifferent K i
  intro hz
  have hzero : integralTraceDualBasis K i = 0 := by
    simpa only [hz, FractionalIdeal.mem_zero_iff] using hi
  exact (integralTraceDualBasis K).ne_zero i hzero

def traceConductor (γ : K) : Ideal (𝓞 K) := conductorIdeal (inverseDifferent K) γ

theorem traceConductor_ne_zero (γ : K) : traceConductor γ ≠ ⊥ :=
  conductorIdeal_ne_zero _ inverseDifferent_ne_zero γ

/-- Points on the affine line have their integer coordinates in one
actual conductor-ideal coset. -/
theorem closePairs_mem_conductor_coset
    (I : FractionalIdeal (𝓞 K)⁰ K) (p r : 𝓞 K × K) (γ : K)
    (hp : p.2 ∈ I) (hr : r.2 ∈ I)
    (hline : p.2 = r.2 + γ * ((p.1 : K) - (r.1 : K))) :
    p.1 - r.1 ∈ conductorIdeal I γ := by
  change (((p.1 - r.1 : 𝓞 K) : K) * γ) ∈ I
  have heq : (((p.1 - r.1 : 𝓞 K) : K) * γ) = p.2 - r.2 := by
    push_cast
    rw [hline]
    ring
  rw [heq]
  exact (I : Submodule (𝓞 K) K).sub_mem hp hr

end WaringSiegel
