import WaringSiegel.WSL2IntegerBox
import WaringSiegel.TraceCoordinates

/-! # WSL3: integral-basis boxes provide uniformly many translations -/
noncomputable section
set_option maxHeartbeats 300000
open scoped NumberField BigOperators Classical
open NumberField
namespace WaringSiegel
variable {K : Type*} [Field K] [NumberField K]

def integralBasisBoxConstant (K : Type*) [Field K] [NumberField K] : ℝ :=
  1 + ∑ v : InfinitePlace K, ∑ i : NumberFieldCoordinateIndex K,
    v ((RingOfIntegers.basis K i : 𝓞 K) : K)

theorem integralBasisBoxConstant_pos : 0 < integralBasisBoxConstant K := by
  unfold integralBasisBoxConstant
  have h : 0 ≤ ∑ v : InfinitePlace K, ∑ i : NumberFieldCoordinateIndex K,
      v ((RingOfIntegers.basis K i : 𝓞 K) : K) :=
    Finset.sum_nonneg (fun v _ => Finset.sum_nonneg (fun i _ => apply_nonneg v _))
  linarith

def integralBasisGridPoint (N : ℕ) (a : NumberFieldCoordinateIndex K → Fin (N+1)) : 𝓞 K :=
  (RingOfIntegers.basis K).equivFun.symm (fun i => (a i : ℕ))

theorem integralBasisGridPoint_injective (N : ℕ) :
    Function.Injective (integralBasisGridPoint (K := K) N) := by
  intro a b hab
  have he := (RingOfIntegers.basis K).equivFun.symm.injective hab
  funext i
  apply Fin.ext
  exact_mod_cast congrFun he i

theorem integralBasisGridPoint_place_le (N : ℕ)
    (a : NumberFieldCoordinateIndex K → Fin (N+1)) (v : InfinitePlace K) :
    v (integralBasisGridPoint N a : K) ≤ (N : ℝ) * integralBasisBoxConstant K := by
  have hterm (i : NumberFieldCoordinateIndex K) :
      v (((a i : ℕ) : K) * ((RingOfIntegers.basis K i : 𝓞 K) : K)) =
      (a i : ℕ) * v ((RingOfIntegers.basis K i : 𝓞 K) : K) := by
    rw [← InfinitePlace.norm_embedding_eq, map_mul, map_natCast, norm_mul,
      Complex.norm_natCast, InfinitePlace.norm_embedding_eq]
  have hsum : (∑ i : NumberFieldCoordinateIndex K,
      v ((RingOfIntegers.basis K i : 𝓞 K) : K)) ≤ integralBasisBoxConstant K := by
    have h : (∑ i : NumberFieldCoordinateIndex K,
        v ((RingOfIntegers.basis K i : 𝓞 K) : K)) ≤
        ∑ w : InfinitePlace K, ∑ i : NumberFieldCoordinateIndex K,
          w ((RingOfIntegers.basis K i : 𝓞 K) : K) := Finset.single_le_sum
      (fun w (_ : w ∈ (Finset.univ : Finset (InfinitePlace K))) =>
        Finset.sum_nonneg (fun i _ => apply_nonneg w (((RingOfIntegers.basis K) i : 𝓞 K) : K)))
      (Finset.mem_univ v)
    unfold integralBasisBoxConstant
    linarith
  unfold integralBasisGridPoint
  rw [Module.Basis.equivFun_symm_apply]
  simp only [map_sum, map_smul, Int.cast_natCast, zsmul_eq_mul, Nat.cast_smul_eq_nsmul,
    nsmul_eq_mul, map_natCast]
  calc
    v (∑ i : NumberFieldCoordinateIndex K,
        ((a i : ℕ) : K) * ((RingOfIntegers.basis K i : 𝓞 K) : K)) ≤
      ∑ i : NumberFieldCoordinateIndex K,
        v (((a i : ℕ) : K) * ((RingOfIntegers.basis K i : 𝓞 K) : K)) := v.val.sum_le _ _
    _ = ∑ i : NumberFieldCoordinateIndex K,
        (a i : ℕ) * v ((RingOfIntegers.basis K i : 𝓞 K) : K) := by simp only [hterm]
    _ ≤ ∑ i : NumberFieldCoordinateIndex K,
        (N : ℝ) * v ((RingOfIntegers.basis K i : 𝓞 K) : K) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast (Nat.le_of_lt_succ (a i).isLt))
        (apply_nonneg v _)
    _ = (N : ℝ) * ∑ i : NumberFieldCoordinateIndex K,
        v ((RingOfIntegers.basis K i : 𝓞 K) : K) := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _)

def integralBasisGrid (N : ℕ) : Finset (𝓞 K) :=
  Finset.univ.image (integralBasisGridPoint (K := K) N)

theorem integralBasisGrid_card (N : ℕ) :
    (integralBasisGrid (K := K) N).card = (N+1)^Module.finrank ℚ K := by
  rw [integralBasisGrid, Finset.card_image_of_injective _ (integralBasisGridPoint_injective N)]
  simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, NumberFieldCoordinateIndex]
  rw [← Module.finrank_eq_card_basis (NumberField.integralBasis K)]

/-- A concrete finite set inside every archimedean box contains at least a
field-dependent positive multiple of its volume. -/
theorem exists_integer_translation_set :
    ∃ c : ℝ, 0 < c ∧ ∀ P : ℝ, 1 ≤ P → ∃ Y : Finset (𝓞 K),
      (∀ y ∈ Y, ∀ v : InfinitePlace K, v (y : K) ≤ P) ∧
      c * P^Module.finrank ℚ K ≤ (Y.card : ℝ) := by
  let B := integralBasisBoxConstant K
  have hB : 0 < B := integralBasisBoxConstant_pos
  refine ⟨1 / B^Module.finrank ℚ K, by positivity, ?_⟩
  intro P hP
  have hP0 : 0 ≤ P := by linarith
  let N := ⌊P/B⌋₊
  refine ⟨integralBasisGrid N, ?_, ?_⟩
  · intro y hy v
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hy
    exact (integralBasisGridPoint_place_le N a v).trans (by
      exact (mul_le_mul_of_nonneg_right (Nat.floor_le (div_nonneg hP0 hB.le)) hB.le).trans_eq
        (div_mul_cancel₀ P hB.ne'))
  · rw [integralBasisGrid_card, Nat.cast_pow, Nat.cast_add, Nat.cast_one]
    have hfloor : P/B ≤ (N : ℝ)+1 := (Nat.lt_floor_add_one (P/B)).le
    have hpow := pow_le_pow_left₀ (div_nonneg hP0 hB.le) hfloor (Module.finrank ℚ K)
    rw [div_pow] at hpow
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using hpow

end WaringSiegel
#print axioms WaringSiegel.exists_integer_translation_set
