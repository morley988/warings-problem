import Waring.RestrictedSmoothHolder

/-! # Exact shorter smooth sums after commuting prime support -/

noncomputable section
open scoped BigOperators
namespace Waring.RestrictedSmoothFactorization
open SmoothMoments PrimeSupportedCount

def roughSupportedNumbers (q π : ℕ) (X R : ℝ) : Finset ℕ := by
  classical
  exact (smoothNumbers X R).filter (fun z =>
    IsPrimeSupported z q ∧ PrimeRestricted (fun l => π < l) z)

def shorterPrimeDomain (q π : ℕ) (X R : ℝ) : Finset (Σ _ : ℕ, ℕ) := by
  classical
  exact (roughSupportedNumbers q π X R).sigma (fun z => smoothNumbers (X/(z : ℝ)) π)

def shorterPrimeDecode (t : Σ _ : ℕ, ℕ) : ℕ × ℕ := (t.2,t.1)

theorem shorterPrimeDecode_mem {q π : ℕ} {X R : ℝ} (hX : 0 ≤ X) (hπR : (π : ℝ) ≤ R)
    {t : Σ _ : ℕ, ℕ} (ht : t ∈ shorterPrimeDomain q π X R) :
    shorterPrimeDecode t ∈ mixedPrimeDomain X R (fun l => l ≤ π) (fun l => l ∣ q) := by
  classical
  rcases Finset.mem_sigma.mp ht with ⟨hz,hx⟩
  rcases Finset.mem_filter.mp hz with ⟨hz,hzq,hrough⟩
  have hz' := mem_smoothNumbers.mp hz
  have hx' := mem_smoothNumbers.mp hx
  have hprod : t.1*t.2 ≤ ⌊X⌋₊ := (mul_le_floor_div_iff hX hz'.1.1).mpr hx'.1.2
  have hxX : t.2 ≤ ⌊X⌋₊ := (Nat.le_mul_of_pos_left _ hz'.1.1).trans hprod
  have hxR : IsSmooth t.2 R := fun l hl hld => (hx'.2 l hl hld).trans hπR
  refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
    ⟨mem_smoothNumbers.mpr ⟨⟨hx'.1.1,hxX⟩,hxR⟩,hz⟩,?_,?_,?_⟩,hzq⟩
  · change t.2*t.1 ≤ ⌊X⌋₊
    simpa only [mul_comm] using hprod
  · intro l hl hld
    exact_mod_cast hx'.2 l hl hld
  · intro l hl hld
    exact not_le.mpr (hrough l hl hld)

theorem shorterPrimeDecode_injective : Function.Injective shorterPrimeDecode := by
  intro t u he
  rcases t with ⟨z,x⟩
  rcases u with ⟨w,y⟩
  have hz := congrArg Prod.snd he
  have hx := congrArg Prod.fst he
  dsimp [shorterPrimeDecode] at hz hx
  subst w; subst y
  rfl

theorem shorterPrimeDecode_surjective {q π : ℕ} {X R : ℝ} (hX : 0 ≤ X)
    {p : ℕ × ℕ}
    (hp : p ∈ mixedPrimeDomain X R (fun l => l ≤ π) (fun l => l ∣ q)) :
    ∃ t ∈ shorterPrimeDomain q π X R, shorterPrimeDecode t=p := by
  classical
  rcases Finset.mem_filter.mp hp with ⟨hp,hzq⟩
  rcases Finset.mem_filter.mp hp with ⟨hp,hprod,hsmall,hrough⟩
  rcases Finset.mem_product.mp hp with ⟨hx,hz⟩
  have hx' := mem_smoothNumbers.mp hx
  have hz' := mem_smoothNumbers.mp hz
  have hxdiv : p.1 ≤ ⌊X/(p.2 : ℝ)⌋₊ := by
    apply (mul_le_floor_div_iff hX hz'.1.1).mp
    simpa only [mul_comm] using hprod
  refine ⟨⟨p.2,p.1⟩,Finset.mem_sigma.mpr
    ⟨Finset.mem_filter.mpr ⟨hz,hzq,?_⟩,mem_smoothNumbers.mpr ⟨⟨hx'.1.1,hxdiv⟩,?_⟩⟩,rfl⟩
  · intro l hl hld
    exact lt_of_not_ge (hrough l hl hld)
  · intro l hl hld
    exact_mod_cast hsmall l hl hld

theorem mixedPrime_sum_shorter {A : Type*} [AddCommMonoid A]
    {q π : ℕ} {X R : ℝ} (hX : 0 ≤ X) (hπR : (π : ℝ) ≤ R) (f : ℕ → A) :
    (∑ p ∈ mixedPrimeDomain X R (fun l => l ≤ π) (fun l => l ∣ q),f (p.1*p.2)) =
      ∑ z ∈ roughSupportedNumbers q π X R,
        ∑ x ∈ smoothNumbers (X/(z : ℝ)) π,f (x*z) := by
  classical
  calc
    _ = ∑ t ∈ shorterPrimeDomain q π X R,f ((shorterPrimeDecode t).1*(shorterPrimeDecode t).2) := by
      symm
      apply Finset.sum_bij (fun t _ => shorterPrimeDecode t)
      · exact fun _ ht => shorterPrimeDecode_mem hX hπR ht
      · exact fun _ _ _ _ he => shorterPrimeDecode_injective he
      · intro p hp
        obtain ⟨t,ht,he⟩ := shorterPrimeDecode_surjective hX hp
        exact ⟨t,ht,he⟩
      · exact fun _ _ => rfl
    _ = _ := by simp only [shorterPrimeDomain,Finset.sum_sigma,shorterPrimeDecode]

/-- The original mixed-prime sum equals a sum of literal smaller smooth
Weyl sums, not a pointwise enlargement of its original oscillatory domain. -/
theorem mixedPrimeWeyl_eq_shorter (k q π : ℕ) {X R : ℝ}
    (hX : 0 ≤ X) (hπR : (π : ℝ) ≤ R) (α : ℝ) :
    mixedPrimeWeyl k q π X R α =
      ∑ z ∈ roughSupportedNumbers q π X R,
        smoothWeyl k (X/(z : ℝ)) π ((z : ℝ)^k*α) := by
  rw [mixedPrimeWeyl,supported_threshold_weyl_identity,
    mixedPrime_sum_shorter (q := q) hX hπR (fun n => phase k n α)]
  apply Finset.sum_congr rfl
  intro z hz
  unfold smoothWeyl
  apply Finset.sum_congr rfl
  intro x hx
  rw [mul_comm x z,phase_mul_scale]

theorem roughSupported_subset (q π : ℕ) (X R : ℝ) :
    roughSupportedNumbers q π X R ⊆ supportedNumbers ⌊X⌋₊ q := by
  classical
  intro z hz
  rcases Finset.mem_filter.mp hz with ⟨hz,hzq,_⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr (mem_smoothNumbers.mp hz).1,hzq⟩

theorem mixedPrimeWeyl_holder (k q π : ℕ) {s : ℕ} (hs : 1 ≤ s)
    {X R : ℝ} (hX : 0 ≤ X) (hπR : (π : ℝ) ≤ R) (α : ℝ) :
    ‖mixedPrimeWeyl k q π X R α‖^s ≤
      ((supportedNumbers ⌊X⌋₊ q).card : ℝ)^(s-1)*
        ∑ z ∈ smoothNumbers X R, ‖smoothWeyl k (X/(z : ℝ)) π ((z : ℝ)^k*α)‖^s := by
  classical
  rw [mixedPrimeWeyl_eq_shorter k q π hX hπR]
  apply (norm_sum_pow_le_card _ _ hs).trans
  have hc : ((roughSupportedNumbers q π X R).card : ℝ) ≤
      ((supportedNumbers ⌊X⌋₊ q).card : ℝ) :=
    Nat.cast_le.mpr (Finset.card_le_card (roughSupported_subset q π X R))
  apply mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) hc _)
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => by positivity))
    (Finset.sum_nonneg (fun _ _ => by positivity)) (by positivity)

#print axioms mixedPrimeWeyl_eq_shorter
#print axioms mixedPrimeWeyl_holder
end Waring.RestrictedSmoothFactorization
