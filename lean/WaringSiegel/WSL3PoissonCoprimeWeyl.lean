import WaringSiegel.WSL3PoissonMixedTorus
import WaringSiegel.WSL3TraceIdealDuality
import WaringSiegel.WSL2LocalAuxiliaryPrime
import Mathlib.RingTheory.Ideal.Nonunits

/-! # Exact finite-character averaging for coprime cubic Weyl sums

The exact unit-mask transfer is proved for every rational prime, including
ramified primes. Its numerical cubic-Weyl specialization is a separate
composition step; this file proves the generic transfer with cost2^degree.
-/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory NumberField NumberField.mixedEmbedding Module WaringSiegel.WSL2
open scoped NumberField BigOperators Classical
namespace WaringSiegel.WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

def finiteLinearTraceSum (S : Finset (𝓞 K)) (f : 𝓞 K → ℂ)
    (q : ArchimedeanTraceTorus K) : ℂ :=
  ∑ x ∈ S, f x * traceTorusCharacter x q

theorem finiteLinearTraceSum_ideal_bound (S : Finset (𝓞 K)) (f : 𝓞 K → ℂ)
    (B : ℝ) (hB : ∀ q, ‖finiteLinearTraceSum S f q‖ ≤ B)
    (I : Ideal (𝓞 K)) (hI : I ≠ 0) (q : ArchimedeanTraceTorus K) :
    ‖finiteLinearTraceSum (S.filter (fun x => x ∈ I)) f q‖ ≤ B := by
  letI := Ideal.finiteQuotientOfFreeOfNeBot I hI
  letI := Fintype.ofFinite (𝓞 K ⧸ I)
  let n := Fintype.card (𝓞 K ⧸ I)
  have hn : 0 < (n:ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  let F : AddChar (𝓞 K ⧸ I) ℂ → ℂ := fun ψ =>
    ∑ x ∈ S, f x*traceTorusCharacter x q*ψ (Ideal.Quotient.mk I x)
  have he : (∑ ψ, F ψ) = (n:ℂ)*finiteLinearTraceSum (S.filter (fun x => x ∈ I)) f q := by
    dsimp only [F,finiteLinearTraceSum]
    rw [Finset.sum_comm,Finset.sum_filter,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    rw [← Finset.mul_sum,AddChar.sum_apply_eq_ite]
    by_cases h : x ∈ I
    · simp only [Ideal.Quotient.eq_zero_iff_mem.mpr h,if_pos,h,n]
      ring
    · have hz : Ideal.Quotient.mk I x ≠ 0 := mt Ideal.Quotient.eq_zero_iff_mem.mp h
      simp [hz,h]
  have hF (ψ : AddChar (𝓞 K ⧸ I) ℂ) : ‖F ψ‖ ≤ B := by
    obtain ⟨γ,-,hγ⟩ := ideal_character_has_rational_trace_representative I hI ψ
    have he : F ψ = finiteLinearTraceSum S f (q+traceRationalPoint γ) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [hγ,traceTorusCharacter_add]
      ring
    rw [he]
    exact hB _
  have hb : ‖∑ ψ, F ψ‖ ≤ (n:ℝ)*B := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _ψ : AddChar (𝓞 K ⧸ I) ℂ, B := Finset.sum_le_sum (fun ψ _ => hF ψ)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,AddChar.card_eq,n]
  rw [he,norm_mul,Complex.norm_natCast] at hb
  exact (mul_le_mul_left hn).mp hb

theorem finiteLinearTraceSum_avoid_ideals_bound
    (J : Finset (Ideal (𝓞 K))) (hJ : ∀ I ∈ J, I ≠ 0)
    (S : Finset (𝓞 K)) (f : 𝓞 K → ℂ) (B : ℝ)
    (hB : ∀ q, ‖finiteLinearTraceSum S f q‖ ≤ B) :
    ∀ q, ‖finiteLinearTraceSum (S.filter (fun x => ∀ I ∈ J, x ∉ I)) f q‖ ≤
      (2:ℝ)^J.card*B := by
  induction J using Finset.induction_on with
  | empty => simpa using hB
  | @insert I J hIJ ih =>
    have hJ' : ∀ A ∈ J, A ≠ 0 := fun A hA => hJ A (Finset.mem_insert_of_mem hA)
    have hI : I ≠ 0 := hJ I (Finset.mem_insert_self _ _)
    have hh := ih hJ'
    let T := S.filter (fun x => ∀ A ∈ J, x ∉ A)
    have he : S.filter (fun x => ∀ A ∈ insert I J, x ∉ A) = T.filter (fun x => x ∉ I) := by
      ext x
      simp only [T,Finset.mem_filter,Finset.mem_insert,forall_eq_or_imp]
      tauto
    intro q
    rw [he]
    have hpart : finiteLinearTraceSum (T.filter (fun x => x ∉ I)) f q =
        finiteLinearTraceSum T f q-finiteLinearTraceSum (T.filter (fun x => x ∈ I)) f q := by
      apply eq_sub_iff_add_eq.mpr
      unfold finiteLinearTraceSum
      rw [← Finset.sum_filter_add_sum_filter_not T (fun x => x ∈ I)]
      ring
    rw [hpart]
    apply (norm_sub_le _ _).trans
    apply (add_le_add (hh q) (finiteLinearTraceSum_ideal_bound T f _ hh I hI q)).trans_eq
    rw [Finset.card_insert_of_notMem hIJ,pow_succ]
    ring

theorem quotient_unit_iff_avoid_auxiliary_primes (p : ℕ) (hp : p.Prime) (x : 𝓞 K) :
    IsUnit (Ideal.Quotient.mk (Ideal.span ({(p:𝓞 K)} : Set (𝓞 K))) x) ↔
      ∀ v ∈ cubicAuxiliaryPrimeSet (K:=K) p hp, x ∉ v.asIdeal := by
  let I : Ideal (𝓞 K) := Ideal.span ({(p:𝓞 K)} : Set (𝓞 K))
  constructor
  · intro hx v hv hxv
    have hIv : I ≤ v.asIdeal := by
      rw [Ideal.span_singleton_le_iff_mem]
      exact (mem_cubicAuxiliaryPrimeSet hp v).mp hv
    have hu := hx.map (Ideal.Quotient.factor hIv)
    have hz : Ideal.Quotient.mk v.asIdeal x = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hxv
    exact hu.ne_zero (by simpa only [Ideal.Quotient.factor_mk] using hz)
  · intro hx
    by_contra hn
    obtain ⟨J,hJ,hxJ⟩ := exists_max_ideal_of_mem_nonunits hn
    let J0 := J.comap (Ideal.Quotient.mk I)
    have hpJ : (p:𝓞 K) ∈ J0 := by
      change Ideal.Quotient.mk I (p:𝓞 K) ∈ J
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))]
      exact J.zero_mem
    have hJ0 : J0 ≠ ⊥ := by
      intro hz
      have hp0 : (p:𝓞 K) = 0 := by simpa only [hz,Ideal.mem_bot] using hpJ
      exact hp.ne_zero (by exact_mod_cast hp0)
    let v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) :=
      ⟨J0,hJ.isPrime.comap (Ideal.Quotient.mk I),hJ0⟩
    exact hx v ((mem_cubicAuxiliaryPrimeSet hp v).mpr hpJ) hxJ

/-- Exact mask transfer: a uniform bound for all linear trace twists loses
at most2^degree when the source is restricted to units modulo a rational prime. -/
theorem finiteLinearTraceSum_coprime_prime_bound
    (S : Finset (𝓞 K)) (f : 𝓞 K → ℂ) (B : ℝ)
    (hB : ∀ q, ‖finiteLinearTraceSum S f q‖ ≤ B)
    (p : ℕ) (hp : p.Prime) (q : ArchimedeanTraceTorus K) :
    ‖finiteLinearTraceSum (S.filter (fun x =>
      IsUnit (Ideal.Quotient.mk (Ideal.span ({(p:𝓞 K)} : Set (𝓞 K))) x))) f q‖ ≤
      (2:ℝ)^finrank ℚ K*B := by
  let V := cubicAuxiliaryPrimeSet (K:=K) p hp
  let J := V.image (fun v => v.asIdeal)
  have hJ : ∀ I ∈ J, I ≠ 0 := by
    intro I hI
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hI
    exact v.ne_bot
  have he : S.filter (fun x => IsUnit
      (Ideal.Quotient.mk (Ideal.span ({(p:𝓞 K)} : Set (𝓞 K))) x)) =
      S.filter (fun x => ∀ I ∈ J, x ∉ I) := by
    ext x
    simp only [Finset.mem_filter,quotient_unit_iff_avoid_auxiliary_primes p hp x,J,
      Finset.mem_image,forall_exists_index,and_imp,forall_apply_eq_imp_iff₂,V]
  rw [he]
  apply (finiteLinearTraceSum_avoid_ideals_bound J hJ S f B hB q).trans
  have hcard : J.card ≤ finrank ℚ K := (Finset.card_image_le).trans
    (prime_ideals_above_rational_prime_card_le hp V
      (fun v hv => (mem_cubicAuxiliaryPrimeSet hp v).mp hv))
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hcard)
    ((norm_nonneg _).trans (hB 0))

#print axioms finiteLinearTraceSum_ideal_bound
#print axioms finiteLinearTraceSum_avoid_ideals_bound
#print axioms finiteLinearTraceSum_coprime_prime_bound
end WaringSiegel.WSL3Poisson
