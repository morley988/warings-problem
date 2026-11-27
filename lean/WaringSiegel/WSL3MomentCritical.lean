import WaringSiegel.WSL3MomentPrimeSelection
import WaringSiegel.WSL3MomentNativeSource

/-!
# A genuine number-field monomial critical Vinogradov bound

The prime is constructed for every number field.  Its prime-power quotients
are identified with integer residue rings, the native critical congruence
bound is applied to literal integer representatives, and the depth is chosen
with a proved upper bound.  Constants are uniform in the boxed finite set.
-/

noncomputable section
open MeasureTheory GafniTao
open scoped BigOperators Classical NumberField WithZero

namespace WaringSiegel.WSL3
open WSL2

variable {K : Type*} [Field K] [NumberField K]

/-- Exact number-field transfer at a specified depth.  The local prime
hypotheses are discharged by `exists_large_unramified_degreeOne_prime` in
the final box-size theorem below. -/
theorem numberField_critical_count_at_depth (k p : ℕ)
    (hp : p.Prime) (hk : 1 ≤ k) (hkp : k < p)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (hnorm : Ideal.absNorm v.asIdeal = p)
    (hval : v.intValuation (p : 𝓞 K) = WithZero.exp (-1 : ℤ))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ B0 : ℕ,
      ∀ (H : ℕ) (P : ℝ), 0 ≤ P → B0 ≤ k * H →
        (2 * P) ^ Module.finrank ℚ K < (p : ℝ) ^ H →
        ∀ {α : Type*} [Fintype α] (nodes : α → 𝓞 K),
          Function.Injective nodes →
          (∀ x, ∀ w : NumberField.InfinitePlace K, w (nodes x : K) ≤ P) →
          (vinogradovCount k (wooleyTriangular k) nodes : ℝ) ≤
            C * (p ^ (k * H) : ℝ) ^ δ * (Fintype.card α : ℝ) ^ (wooleyTriangular k) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨C, hC, B0, hmain⟩ := native_monomial_modular_count_bound k p hp hk hkp hδ
  refine ⟨C, hC, B0, ?_⟩
  intro H P hP hB hdeep α inst nodes hinj hbox
  let e := degreeOne_primePower_quotient_equiv v p hp hnorm hval (k * H)
  let f := degreeOne_primePower_quotient_equiv v p hp hnorm hval H
  let labels : α → ℤ := fun x => quotientIntegerRepresentative (v.asIdeal ^ (k * H)) e (nodes x)
  have hIJ : v.asIdeal ^ (k * H) ≤ v.asIdeal ^ H :=
    Ideal.pow_le_pow_right (by nlinarith : H ≤ k * H)
  have hdeep' : (2 * P) ^ Module.finrank ℚ K < (Ideal.absNorm (v.asIdeal ^ H) : ℝ) := by
    simpa only [map_pow, hnorm, Nat.cast_pow] using hdeep
  have hlabels : Function.Injective (fun x => (labels x : ZMod (p ^ H))) :=
    integer_representatives_lower_residue_injective _ _ hIJ e f P hP hdeep' nodes hinj hbox
  calc
    (vinogradovCount k (wooleyTriangular k) nodes : ℝ) ≤
        (vinogradovCount k (wooleyTriangular k)
          (fun x => (labels x : ZMod (p ^ (k * H)))) : ℝ) := by
      exact_mod_cast vinogradovCount_le_integer_modular_count _ e k (wooleyTriangular k) nodes
    _ ≤ _ := hmain H labels hB hlabels

/-- A prime-power depth both above a given threshold and within a fixed
multiple of the requested scale. -/
theorem exists_depth_with_power_control (p B0 : ℕ) (hp : 1 < p)
    (X : ℝ) (hX : 1 ≤ X) :
    ∃ H : ℕ, B0 ≤ H ∧ X < (p : ℝ) ^ H ∧
      (p : ℝ) ^ H ≤ (p : ℝ) ^ (B0 + 1) * X := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  obtain ⟨n, hnlo, hnhi⟩ := exists_nat_pow_near hX hpR
  refine ⟨B0 + (n + 1), by omega, ?_, ?_⟩
  · exact hnhi.trans_le (pow_le_pow_right₀ hpR.le (by omega))
  · calc
      (p : ℝ) ^ (B0 + (n + 1)) = (p : ℝ) ^ (B0 + 1) * (p : ℝ) ^ n := by
        rw [← pow_add]
        congr 1
        omega
      _ ≤ _ := mul_le_mul_of_nonneg_left hnlo (by positivity)

/-- Critical monomial VMVT for boxed algebraic integers, with its epsilon
loss measured in the actual number-field volume and its main term in the
cardinality of the node set.  No prime-existence or analytic hypothesis
remains. -/
theorem numberField_critical_count_card_bound (k : ℕ) (hk : 1 ≤ k)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P →
      ∀ {α : Type*} [Fintype α] (nodes : α → 𝓞 K),
        Function.Injective nodes →
        (∀ x, ∀ w : NumberField.InfinitePlace K, w (nodes x : K) ≤ P) →
        (vinogradovCount k (wooleyTriangular k) nodes : ℝ) ≤
          C * (P ^ Module.finrank ℚ K : ℝ) ^ ε *
            (Fintype.card α : ℝ) ^ (wooleyTriangular k) := by
  obtain ⟨p, hp, hkp, v, hnorm, hval⟩ := exists_large_unramified_degreeOne_prime (K := K) k
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  obtain ⟨A, hA, B0, hmain⟩ := numberField_critical_count_at_depth k p hp hk hkp v hnorm hval
    (show 0 < ε / (k : ℝ) from div_pos hε hkR)
  let d := Module.finrank ℚ K
  let D : ℝ := (p : ℝ) ^ (B0 + 1) * (2 : ℝ) ^ d
  refine ⟨A * D ^ ε, by dsimp [D]; positivity, ?_⟩
  intro P hP α inst nodes hinj hbox
  have hP0 : 0 < P := lt_of_lt_of_le zero_lt_one hP
  have hX : 1 ≤ (2 * P) ^ d := one_le_pow₀ (by linarith)
  obtain ⟨H, hHB, hHlo, hHhi⟩ := exists_depth_with_power_control p B0 hp.one_lt ((2 * P) ^ d) hX
  have hB : B0 ≤ k * H := hHB.trans (by nlinarith)
  have hbase : (p : ℝ) ^ H ≤ D * P ^ d := by
    simpa only [D, mul_pow, mul_assoc] using hHhi
  have he : (p ^ (k * H) : ℝ) ^ (ε / (k : ℝ)) = ((p : ℝ) ^ H) ^ ε := by
    rw [Nat.mul_comm k H, pow_mul, ← Real.rpow_natCast _ k,
      ← Real.rpow_mul (by positivity)]
    congr 1
    field_simp
  have hpower : (p ^ (k * H) : ℝ) ^ (ε / (k : ℝ)) ≤ D ^ ε * (P ^ d : ℝ) ^ ε := by
    rw [he, ← Real.mul_rpow (by dsimp [D]; positivity) (by positivity)]
    exact Real.rpow_le_rpow (by positivity) hbase hε.le
  calc
    (vinogradovCount k (wooleyTriangular k) nodes : ℝ) ≤
        A * (p ^ (k * H) : ℝ) ^ (ε / (k : ℝ)) *
          (Fintype.card α : ℝ) ^ (wooleyTriangular k) :=
      hmain H P hP0.le hB hHlo nodes hinj hbox
    _ ≤ A * (D ^ ε * (P ^ d : ℝ) ^ ε) *
          (Fintype.card α : ℝ) ^ (wooleyTriangular k) := by gcongr
    _ = _ := by ring

/-- The classical critical exponent, expressed in number-field volume
`X = P^[K:ℚ]`, for the literal full system of power-sum equations. -/
theorem numberField_critical_count_bound (k : ℕ) (hk : 1 ≤ k)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P →
      ∀ {α : Type*} [Fintype α] (nodes : α → 𝓞 K),
        Function.Injective nodes →
        (∀ x, ∀ w : NumberField.InfinitePlace K, w (nodes x : K) ≤ P) →
        (vinogradovCount k (wooleyTriangular k) nodes : ℝ) ≤
          C * (P ^ Module.finrank ℚ K : ℝ) ^ ((wooleyTriangular k : ℝ) + ε) := by
  obtain ⟨A, hA, hmain⟩ := numberField_critical_count_card_bound (K := K) k hk hε
  let d := Module.finrank ℚ K
  let B : ℝ := 2 * (3 : ℝ) ^ d
  refine ⟨A * B ^ wooleyTriangular k, by dsimp [B]; positivity, ?_⟩
  intro P hP α inst nodes hinj hbox
  have hP0 : 0 < P := lt_of_lt_of_le zero_lt_one hP
  have hN : (Fintype.card α : ℝ) ≤ B * P ^ d := by
    have h := integer_box_card_bound (Finset.univ.image nodes) P hP (by
      intro x hx v
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
      exact hbox a v)
    simpa only [Finset.card_image_of_injective _ hinj, Finset.card_univ] using h
  calc
    (vinogradovCount k (wooleyTriangular k) nodes : ℝ) ≤
        A * (P ^ d : ℝ) ^ ε * (Fintype.card α : ℝ) ^ wooleyTriangular k :=
      hmain P hP nodes hinj hbox
    _ ≤ A * (P ^ d : ℝ) ^ ε * (B * P ^ d) ^ wooleyTriangular k := by gcongr
    _ = (A * B ^ wooleyTriangular k) *
        ((P ^ d : ℝ) ^ (wooleyTriangular k : ℝ) * (P ^ d : ℝ) ^ ε) := by
      rw [Real.rpow_natCast, mul_pow]
      ring
    _ = _ := by rw [← Real.rpow_add (by positivity)]

/-- The actual weighted critical Haar moment over the full k-fold
number-field torus.  Coefficients are arbitrary complex numbers with the
stated common bound. -/
theorem numberField_critical_moment_bound (k : ℕ) (hk : 1 ≤ k)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P →
      ∀ {α : Type*} [Fintype α] (nodes : α → 𝓞 K),
        Function.Injective nodes →
        (∀ x, ∀ v : NumberField.InfinitePlace K, v (nodes x : K) ≤ P) →
        ∀ (w : α → ℂ) (W : ℝ), 0 ≤ W → (∀ x, ‖w x‖ ≤ W) →
        (∫ θ, ‖frequencySum (vinogradovFrequency (integerCoordinates K) k nodes) w θ‖ ^
          (2 * wooleyTriangular k) ∂latticeHaar) ≤
          C * (P ^ Module.finrank ℚ K : ℝ) ^ ((wooleyTriangular k : ℝ) + ε) *
            W ^ (2 * wooleyTriangular k) := by
  obtain ⟨C, hC, hcount⟩ := numberField_critical_count_bound (K := K) k hk hε
  refine ⟨C, hC, ?_⟩
  intro P hP α inst nodes hinj hbox w W hW hw
  exact (numberField_vinogradov_moment_le_count K k (wooleyTriangular k) nodes w W hW hw).trans
    (mul_le_mul_of_nonneg_right (hcount P hP nodes hinj hbox) (by positivity))

#print axioms numberField_critical_count_card_bound
#print axioms numberField_critical_count_bound
#print axioms numberField_critical_moment_bound

end WaringSiegel.WSL3
