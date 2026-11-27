import WaringSiegel.WSL2UnitCompact

/-!
# Reduction of the literal global targets to one compact normalized region

The restricted analytic assertions below remain explicit hypotheses. The
closed result here proves that the actual positive-unit normalization loses
neither eligible targets nor the local unit-coordinate hypothesis, and that
it preserves the root norm constant when the normalization is undone.
-/

noncomputable section
open scoped NumberField BigOperators Classical
open NumberField

namespace WaringSiegel.WSL2
variable {K : Type*} [Field K] [NumberField K]

theorem normalizedTarget_one_unit_pow (k : ℕ) (u : (𝓞 K)ˣ) (ν : 𝓞 K) :
    normalizedTarget k 1 ((u : 𝓞 K) ^ k * ν) = normalizedTarget k u ν := by
  simp [normalizedTarget, normScale, absNorm_unit_pow_mul]

/-- The analytic assertion only for targets whose own normalized image lies
in the fixed compact region. This is a definition, not an analytic proof. -/
def CompactLocalConditionalBound (K : Type*) [Field K] [NumberField K]
    (k s : ℕ) (B : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℝ, 0 < N₀ ∧ ∀ ν : 𝓞 K,
    TotallyPositive ν → LocalUnitSolvable k s ν → N₀ < absNorm ν →
    normalizedTarget k 1 ν ∈ compactTargetSet K B →
      RepresentableByAtMost k s C ν

/-- The eligible-target assertion restricted to the compact normalized
region. It is kept separate from the local-conditional analytic assertion. -/
def CompactWaringSiegelBound (K : Type*) [Field K] [NumberField K]
    (k s : ℕ) (B : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℝ, 0 < N₀ ∧ ∀ ν : 𝓞 K,
    TotallyPositive ν → Eligible k ν → N₀ < absNorm ν →
    normalizedTarget k 1 ν ∈ compactTargetSet K B →
      RepresentableByAtMost k s C ν

/-- A fixed compact region suffices for the literal all-target local-conditional
theorem, simultaneously for every number of variables. -/
theorem exists_compact_local_reduction (K : Type*) [Field K] [NumberField K]
    (k : ℕ) (hk : 0 < k) :
    ∃ B : ℝ, 1 ≤ B ∧ IsCompact (compactTargetSet K B) ∧ ∀ s : ℕ,
      CompactLocalConditionalBound K k s B ↔ LocalConditionalBound K k s := by
  obtain ⟨B, hB, hcompact, hbalance⟩ := exists_compact_normalized_targets K k hk
  refine ⟨B, hB, hcompact, ?_⟩
  intro s
  constructor
  · rintro ⟨C, hC, N₀, hN₀, h⟩
    refine ⟨C, hC, N₀, hN₀, ?_⟩
    intro ν hp hlocal hN
    have hν : ν ≠ 0 := by
      intro hz
      have hpos := hN₀.trans hN
      simpa [hz, absNorm] using hpos
    obtain ⟨u, hu, hnormalized⟩ := hbalance ν hν hp
    apply (representable_unit_pow_iff u hu k s C ν).mp
    apply h ((u : 𝓞 K) ^ k * ν)
    · exact totallyPositive_mul (totallyPositive_pow hu k) hp
    · exact (localUnitSolvable_unit_pow_iff u k s ν).mpr hlocal
    · simpa only [absNorm_unit_pow_mul] using hN
    · rwa [normalizedTarget_one_unit_pow]
  · rintro ⟨C, hC, N₀, hN₀, h⟩
    exact ⟨C, hC, N₀, hN₀, fun ν hp hl hN _ => h ν hp hl hN⟩

/-- The same fixed-region reduction for the unconditional eligible-target
theorem. This does not discharge the restricted analytic assertion. -/
theorem exists_compact_waring_reduction (K : Type*) [Field K] [NumberField K]
    (k : ℕ) (hk : 0 < k) :
    ∃ B : ℝ, 1 ≤ B ∧ IsCompact (compactTargetSet K B) ∧ ∀ s : ℕ,
      CompactWaringSiegelBound K k s B ↔ WaringSiegelBound K k s := by
  obtain ⟨B, hB, hcompact, hbalance⟩ := exists_compact_normalized_targets K k hk
  refine ⟨B, hB, hcompact, ?_⟩
  intro s
  constructor
  · rintro ⟨C, hC, N₀, hN₀, h⟩
    refine ⟨C, hC, N₀, hN₀, ?_⟩
    intro ν hp heligible hN
    have hν : ν ≠ 0 := by
      intro hz
      have hpos := hN₀.trans hN
      simpa [hz, absNorm] using hpos
    obtain ⟨u, hu, hnormalized⟩ := hbalance ν hν hp
    apply (representable_unit_pow_iff u hu k s C ν).mp
    apply h ((u : 𝓞 K) ^ k * ν)
    · exact totallyPositive_mul (totallyPositive_pow hu k) hp
    · exact (eligible_unit_pow_iff u k ν).mpr heligible
    · simpa only [absNorm_unit_pow_mul] using hN
    · rwa [normalizedTarget_one_unit_pow]
  · rintro ⟨C, hC, N₀, hN₀, h⟩
    exact ⟨C, hC, N₀, hN₀, fun ν hp he hN _ => h ν hp he hN⟩

end WaringSiegel.WSL2

#print axioms WaringSiegel.WSL2.exists_compact_local_reduction
#print axioms WaringSiegel.WSL2.exists_compact_waring_reduction
