import WaringSiegel.WSL2MomentResidueTransport

/-!
# Literal finite integer sources for the residue-degree-one VMVT route

The coefficients below really have type `ℤ →₀ ℂ`, exactly the coefficient
space in the recovered native integer source theorem.  Their support, mass,
phase sums, and singleton residue classes are proved without a VMVT input.
-/

noncomputable section
open scoped BigOperators Classical NumberField

namespace WaringSiegel.WSL2

variable {α : Type*} [Fintype α]

def integerNodeSource (labels : α → ℤ) : ℤ →₀ ℂ :=
  Finsupp.indicator (Finset.univ.image labels) (fun _ _ => 1)

@[simp] theorem integerNodeSource_support (labels : α → ℤ) :
    (integerNodeSource labels).support = Finset.univ.image labels := by
  ext n
  simp only [Finsupp.mem_support_iff,integerNodeSource,Finsupp.indicator_apply]
  split_ifs <;> simp_all

theorem integerNodeSource_apply (labels : α → ℤ) (n : ℤ) :
    integerNodeSource labels n = if n∈Finset.univ.image labels then 1 else 0 := by
  simp [integerNodeSource,Finsupp.indicator_apply]

@[simp] theorem integerNodeSource_at_label (labels : α → ℤ) (x : α) :
    integerNodeSource labels (labels x)=1 := by
  rw [integerNodeSource_apply,if_pos]
  exact Finset.mem_image.mpr ⟨x,Finset.mem_univ _,rfl⟩

theorem integerNodeSource_admissible (labels : α → ℤ) (n : ℤ) :
    ‖integerNodeSource labels n‖≤1 := by
  rw [integerNodeSource_apply]
  split_ifs <;> norm_num

theorem integerNodeSource_eq_one_of_mem (labels : α → ℤ) (n : ℤ)
    (hn : n∈(integerNodeSource labels).support) : integerNodeSource labels n=1 := by
  rw [integerNodeSource_support] at hn
  exact (integerNodeSource_apply labels n).trans (if_pos hn)

theorem integerNodeSource_sum (labels : α → ℤ) (hlabels : Function.Injective labels)
    (phase : ℤ → ℂ) :
    (∑n∈(integerNodeSource labels).support, integerNodeSource labels n * phase n) =
      ∑x, phase (labels x) := by
  rw [integerNodeSource_support,Finset.sum_image]
  · simp
  · exact fun x hx y hy heq => hlabels heq

theorem integerNodeSource_mass (labels : α → ℤ) (hlabels : Function.Injective labels) :
    (∑n∈(integerNodeSource labels).support, ‖integerNodeSource labels n‖^2) =
      (Fintype.card α : ℝ) := by
  rw [integerNodeSource_support,Finset.sum_image]
  · simp
  · exact fun x hx y hy heq => hlabels heq

theorem integerNodeSource_residue_subsingleton (labels : α → ℤ) {q : ℕ}
    (hinj : Function.Injective (fun x=>(labels x : ZMod q))) (b : ZMod q) :
    ∀n∈(integerNodeSource labels).support.filter (fun n : ℤ =>(n:ZMod q)=b),
      ∀m∈(integerNodeSource labels).support.filter (fun n : ℤ =>(n:ZMod q)=b), n=m := by
  intro n hn m hm
  obtain ⟨hn,hnmod⟩ := Finset.mem_filter.mp hn
  obtain ⟨hm,hmmod⟩ := Finset.mem_filter.mp hm
  rw [integerNodeSource_support] at hn hm
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hm
  exact congrArg labels (hinj (hnmod.trans hmmod.symm))

theorem integerNodeSource_residue_card_le_one (labels : α → ℤ) {q : ℕ}
    (hinj : Function.Injective (fun x=>(labels x : ZMod q))) (b : ZMod q) :
    ((integerNodeSource labels).support.filter (fun n : ℤ =>(n:ZMod q)=b)).card≤1 :=
  Finset.card_le_one.mpr (integerNodeSource_residue_subsingleton labels hinj b)

/-- Exact mass of each residue class for the actual integer coefficient source. -/
theorem integerNodeSource_residue_mass (labels : α → ℤ) {q : ℕ} (b : ZMod q) :
    (∑n∈(integerNodeSource labels).support.filter (fun n : ℤ =>(n:ZMod q)=b),
      ‖integerNodeSource labels n‖^2) =
    (((integerNodeSource labels).support.filter (fun n : ℤ =>(n:ZMod q)=b)).card : ℝ) := by
  calc
    _ = ∑n∈(integerNodeSource labels).support.filter (fun n : ℤ =>(n:ZMod q)=b), (1:ℝ) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [integerNodeSource_eq_one_of_mem labels n (Finset.mem_filter.mp hn).1]
      norm_num
    _ = _ := by simp

/-- Every nonempty conditioned residue sum is literally a single phase. -/
theorem integerNodeSource_residue_sum_norm (labels : α → ℤ) {q : ℕ}
    (hinj : Function.Injective (fun x=>(labels x : ZMod q))) (b : ZMod q)
    (phase : ℤ → ℂ) (hphase : ∀n, ‖phase n‖=1) :
    ‖∑n∈(integerNodeSource labels).support.filter (fun n : ℤ =>(n:ZMod q)=b),
      integerNodeSource labels n * phase n‖ =
      (((integerNodeSource labels).support.filter (fun n : ℤ =>(n:ZMod q)=b)).card : ℝ) := by
  let S := (integerNodeSource labels).support.filter (fun n : ℤ =>(n:ZMod q)=b)
  have hS : ∀n∈S, ∀m∈S, n=m := integerNodeSource_residue_subsingleton labels hinj b
  by_cases hne : S.Nonempty
  · obtain ⟨n,hn⟩ := hne
    have heq : S={n} := by
      ext m
      constructor
      · intro hm
        exact Finset.mem_singleton.mpr (hS m hm n hn)
      · intro hm
        simpa only [Finset.mem_singleton.mp hm] using hn
    change ‖∑n∈S, integerNodeSource labels n * phase n‖=(S.card:ℝ)
    rw [heq]
    simp only [Finset.sum_singleton,Finset.card_singleton,Nat.cast_one]
    rw [integerNodeSource_eq_one_of_mem labels n (Finset.mem_filter.mp hn).1,one_mul,hphase]
  · have heq : S=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    change ‖∑n∈S, integerNodeSource labels n * phase n‖=(S.card:ℝ)
    simp [heq]

/-- The complete normalized contribution of a singleton residue class is
exactly its mass, uniformly in every finite unit-modulus phase family. -/
theorem integerNodeSource_conditioned_residue_mean
    {β : Type*} [Fintype β] [Nonempty β]
    (labels : α → ℤ) {q : ℕ}
    (hinj : Function.Injective (fun x=>(labels x : ZMod q))) (b : ZMod q)
    (phase : β → ℤ → ℂ) (hphase : ∀t n, ‖phase t n‖=1) (s : ℕ) :
    let γ := integerNodeSource labels
    let ρ := ∑n∈γ.support.filter (fun n : ℤ =>(n:ZMod q)=b), ‖γ n‖^2
    ρ * ((Fintype.card β : ℝ)⁻¹ * ∑t : β,
      ‖if ρ=0 then 0 else ((Real.sqrt ρ : ℂ)⁻¹) *
        (∑n∈γ.support.filter (fun n : ℤ =>(n:ZMod q)=b), γ n * phase t n)‖^(2*s)) = ρ := by
  dsimp only
  rw [integerNodeSource_residue_mass]
  let c := ((integerNodeSource labels).support.filter (fun n : ℤ =>(n:ZMod q)=b)).card
  have hc : c≤1 := integerNodeSource_residue_card_le_one labels hinj b
  by_cases hc0 : c=0
  · simp only [show (((integerNodeSource labels).support.filter (fun n : ℤ =>(n:ZMod q)=b)).card : ℝ)=0 by exact_mod_cast hc0,zero_mul]
  · have hc1 : c=1 := by omega
    have hc1R : (((integerNodeSource labels).support.filter (fun n : ℤ =>(n:ZMod q)=b)).card : ℝ)=1 := by exact_mod_cast hc1
    simp only [hc1R,one_ne_zero,if_false,Real.sqrt_one,Complex.ofReal_one,inv_one,one_mul]
    have hn (t : β) : ‖∑n∈(integerNodeSource labels).support.filter (fun n : ℤ =>(n:ZMod q)=b),
        integerNodeSource labels n * phase t n‖=1 :=
      (integerNodeSource_residue_sum_norm labels hinj b (phase t) (hphase t)).trans hc1R
    simp only [hn,one_pow,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
    exact inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero)

/-- The lower residue masses partition the literal source mass. -/
theorem integerNodeSource_sum_residue_mass (labels : α → ℤ) (q : ℕ) [NeZero q] :
    (∑b : ZMod q, ∑n∈(integerNodeSource labels).support.filter (fun n : ℤ =>(n:ZMod q)=b),
      ‖integerNodeSource labels n‖^2) =
      ∑n∈(integerNodeSource labels).support, ‖integerNodeSource labels n‖^2 := by
  exact Finset.sum_fiberwise (integerNodeSource labels).support (fun n : ℤ =>(n:ZMod q))
    (fun n=>‖integerNodeSource labels n‖^2)

/-- Exact evaluation of the normalized conditioned mean used in the proposed
native source transfer.  This is an identity, not an assumed mean-value bound. -/
theorem integerNodeSource_conditioned_mean
    {β : Type*} [Fintype β] [Nonempty β]
    (labels : α → ℤ) {q : ℕ} [NeZero q]
    (hinj : Function.Injective (fun x=>(labels x : ZMod q)))
    (phase : β → ℤ → ℂ) (hphase : ∀t n, ‖phase t n‖=1) (s : ℕ) :
    let γ := integerNodeSource labels
    let mass := ∑n∈γ.support, ‖γ n‖^2
    let ρ := fun b : ZMod q => ∑n∈γ.support.filter (fun n : ℤ =>(n:ZMod q)=b), ‖γ n‖^2
    (if mass=0 then 0 else mass⁻¹ * ∑b : ZMod q, ρ b *
      ((Fintype.card β : ℝ)⁻¹ * ∑t : β,
        ‖if ρ b=0 then 0 else ((Real.sqrt (ρ b) : ℂ)⁻¹) *
          (∑n∈γ.support.filter (fun n : ℤ =>(n:ZMod q)=b), γ n * phase t n)‖^(2*s))) =
      if mass=0 then 0 else 1 := by
  dsimp only
  split_ifs with hm
  · rfl
  · have hmean := integerNodeSource_conditioned_residue_mean (β := β) labels hinj
    simp_rw [hmean _ phase hphase s,integerNodeSource_sum_residue_mass]
    exact inv_mul_cancel₀ hm

/-- Actual boxed algebraic integers give singleton lower-residue source fibers,
provided the explicitly supplied ideal quotient equivalences exist. -/
theorem numberField_integer_source_residue_card_le_one
    {K : Type*} [Field K] [NumberField K]
    (I J : Ideal (𝓞 K)) (hIJ : I≤J)
    {q r : ℕ} [NeZero q] [NeZero r]
    (e : ((𝓞 K)⧸I)≃+*ZMod q) (f : ((𝓞 K)⧸J)≃+*ZMod r)
    (P : ℝ) (hP : 0≤P) (hdeep : (2*P)^(Module.finrank ℚ K)<(Ideal.absNorm J:ℝ))
    (nodes : α→𝓞 K) (hnodes : Function.Injective nodes)
    (hbox : ∀x, ∀v : NumberField.InfinitePlace K, v (nodes x:K)≤P) (b : ZMod r) :
    ((integerNodeSource (fun x=>quotientIntegerRepresentative I e (nodes x))).support.filter
      (fun n : ℤ =>(n:ZMod r)=b)).card≤1 :=
  integerNodeSource_residue_card_le_one _
    (integer_representatives_lower_residue_injective I J hIJ e f P hP hdeep nodes hnodes hbox) b

end WaringSiegel.WSL2
