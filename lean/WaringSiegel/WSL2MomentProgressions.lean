import WaringSiegel.WSL2MomentFourthGrowth

/-!
# Uniform actual moments in fractional-ideal progressions

The lattice packing theorem is combined with the proved arithmetic fourth
moment.  The constants are uniform in the ideal, its coset, and the box size.
The factor `1 + X / N(I)` retains the sparse-progression regime.
-/

noncomputable section
open MeasureTheory NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module
open scoped BigOperators NumberField nonZeroDivisors Classical

namespace WaringSiegel.WSL2

variable {K : Type*} [Field K] [NumberField K]

theorem integer_coset_box_card_bound (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I≠0)
    (S : Finset (𝓞 K)) (a : K) (P : ℝ) (hP : 0<P)
    (hmem : ∀ x∈S, (x:K)-a∈I)
    (hbox : ∀ x∈S, ∀ v : InfinitePlace K, v (x:K)≤P) :
    (S.card:ℝ) ≤ (3:ℝ)^(finrank ℚ K) *
      (1 + P^(finrank ℚ K)/(FractionalIdeal.absNorm I:ℝ)) := by
  let T : Finset K := S.image (fun x : 𝓞 K => (x:K))
  have hinj : Function.Injective (fun x : 𝓞 K => (x:K)) :=
    FaithfulSMul.algebraMap_injective (𝓞 K) K
  have hcard : T.card=S.card := Finset.card_image_of_injective S hinj
  have h := fractionalIdeal_anisotropic_packing I hI T a 0 (fun _=>P) (fun _=>hP)
    (by
      intro z hz
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
      exact hmem x hx)
    (by
      intro z hz v
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
      simpa only [sub_zero, normAtPlace_apply] using hbox x hx v)
  rw [hcard, Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq] at h
  exact h

theorem indexed_integer_coset_card_bound {α : Type*} [Fintype α]
    (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I≠0) (a : K) (P : ℝ) (hP : 0<P)
    (nodes : α → 𝓞 K) (hinj : Function.Injective nodes)
    (hmem : ∀ x, (nodes x:K)-a∈I)
    (hbox : ∀ x, ∀ v : InfinitePlace K, v (nodes x:K)≤P) :
    (Fintype.card α:ℝ) ≤ (3:ℝ)^(finrank ℚ K) *
      (1 + P^(finrank ℚ K)/(FractionalIdeal.absNorm I:ℝ)) := by
  have h := integer_coset_box_card_bound I hI (Finset.univ.image nodes) a P hP
    (by
      intro y hy
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
      exact hmem x)
    (by
      intro y hy v
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
      exact hbox x v)
  simpa only [Finset.card_image_of_injective _ hinj, Finset.card_univ] using h

/-- A literal second moment, uniform even for progressions sparser than the box. -/
theorem numberField_progression_second_moment_bound (k : ℕ) (hk : 0<k)
    {α : Type*} [Fintype α] (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I≠0)
    (a : K) (P : ℝ) (hP : 0<P) (nodes : α → 𝓞 K) (hinj : Function.Injective nodes)
    (hmem : ∀ x, (nodes x:K)-a∈I)
    (hbox : ∀ x, ∀ v : InfinitePlace K, v (nodes x:K)≤P)
    (w : α → ℂ) (W : ℝ) (hW : 0≤W) (hw : ∀x, ‖w x‖≤W) :
    (∫ θ, ‖finiteWeylSum (integerCoordinates K) k nodes w θ‖^2 ∂latticeHaar) ≤
      (k:ℝ) * (3:ℝ)^(finrank ℚ K) *
        (1 + P^(finrank ℚ K)/(FractionalIdeal.absNorm I:ℝ)) * W^2 := by
  have hmoment := numberField_monomial_second_moment_le K nodes hinj k hk w
  have hcard := indexed_integer_coset_card_bound I hI a P hP nodes hinj hmem hbox
  have hweights : (∑x, ‖w x‖^2) ≤ (Fintype.card α:ℝ)*W^2 := by
    calc
      _ ≤ ∑ _x : α, W^2 := Finset.sum_le_sum (fun x _ => pow_le_pow_left₀ (norm_nonneg _) (hw x) 2)
      _ = _ := by simp [nsmul_eq_mul]
  calc
    _ ≤ (k:ℝ) * ∑x, ‖w x‖^2 := hmoment
    _ ≤ (k:ℝ) * ((Fintype.card α:ℝ)*W^2) := mul_le_mul_of_nonneg_left hweights (by positivity)
    _ ≤ (k:ℝ) * (((3:ℝ)^(finrank ℚ K) *
        (1 + P^(finrank ℚ K)/(FractionalIdeal.absNorm I:ℝ)))*W^2) := by gcongr
    _ = _ := by ring

/-- The fourth moment inside an arbitrary fractional-ideal coset.  The epsilon
loss is measured in the ambient volume and the main term in the actual
progression density. -/
theorem numberField_progression_fourth_moment_bound (k : ℕ) (hk : 2≤k)
    {ε : ℝ} (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ I : FractionalIdeal (𝓞 K)⁰ K, I≠0 →
      ∀ a : K, ∀ P : ℝ, 1≤P → ∀ {α : Type*} [Fintype α],
      ∀ nodes : α → 𝓞 K, Function.Injective nodes →
      (∀x, (nodes x:K)-a∈I) →
      (∀x, ∀v : InfinitePlace K, v (nodes x:K)≤P) →
      ∀w : α → ℂ, ∀W : ℝ, 0≤W → (∀x, ‖w x‖≤W) →
      (∫ θ, ‖finiteWeylSum (integerCoordinates K) k nodes w θ‖^4 ∂latticeHaar) ≤
        C * (1 + P^(finrank ℚ K)/(FractionalIdeal.absNorm I:ℝ))^2 *
          (P^(finrank ℚ K):ℝ)^ε * W^4 := by
  let d : ℕ := finrank ℚ K
  have hd : (0:ℝ)<d := by exact_mod_cast (Module.finrank_pos (R:=ℚ) (M:=K))
  obtain ⟨A,hA,hmoment⟩ := numberField_fourth_moment_card_bound (K:=K) k hk
    (show 0<(d:ℝ)*ε from mul_pos hd hε)
  refine ⟨A*((3:ℝ)^d)^2, by positivity, ?_⟩
  intro I hI a P hP α inst nodes hinj hmem hbox w W hW hw
  have hPpos : 0<P := lt_of_lt_of_le zero_lt_one hP
  have hcard := indexed_integer_coset_card_bound I hI a P hPpos nodes hinj hmem hbox
  have hp : P^((d:ℝ)*ε) = (P^d:ℝ)^ε := by
    rw [← Real.rpow_natCast P d, ← Real.rpow_mul hPpos.le]
  calc
    _ ≤ A*(Fintype.card α:ℝ)^2*P^((d:ℝ)*ε)*W^4 :=
      hmoment P hP nodes hinj hbox w W hW hw
    _ ≤ A*((3:ℝ)^d*(1+P^d/(FractionalIdeal.absNorm I:ℝ)))^2*P^((d:ℝ)*ε)*W^4 := by
      gcongr
    _ = _ := by rw [hp]; ring

end WaringSiegel.WSL2
