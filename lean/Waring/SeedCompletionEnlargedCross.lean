import Waring.SeedCompletionSharpBackward

/-!
# Enlarge the signed next solution count before taking an absolute value

A finite injective embedding transports the actual equation. Only after
enlargement do orthogonality and the triangle inequality produce the full
family cross integral. No comparison between absolute values of subsums
is used.
-/
noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionEnlargedCross
open SeedCompletionBackwardCount SeedCompletionBackwardMoments SeedCompletionBackwardAggregate
open SeedCompletionSharpBackward SeedCompletionSmall PolicyCompletionHolder
open IntegerDifferencePolynomial

def crossIntegral {ι κ : Type*} (A : Finset ι) (f : ι → ℤ) (B : Finset κ) (U : κ → ℤ) : ℝ :=
  ∫ x in (0 : ℝ)..1, ‖frequencySum A f x‖*‖frequencySum B U x‖^2

theorem crossIntegral_nonneg {ι κ : Type*} (A : Finset ι) (f : ι → ℤ)
    (B : Finset κ) (U : κ → ℤ) : 0 ≤ crossIntegral A f B U := by
  apply intervalIntegral.integral_nonneg zero_le_one
  intro x hx
  positivity

theorem cross_product_count_le_integral {ι κ : Type*} (A : Finset ι) (B : Finset κ)
    (f : ι → ℤ) (U : κ → ℤ) :
    ((crossFrequencyPairs (A ×ˢ B) B (fun p => f p.1+U p.2) U).card : ℝ) ≤
      crossIntegral A f B U := by
  have H := cross_count_le_integral_norm (A ×ˢ B) B (fun p => f p.1+U p.2) U
  have heq (x : ℝ) : ‖frequencySum (A ×ˢ B) (fun p => f p.1+U p.2) x‖ *
      ‖frequencySum B U x‖ = ‖frequencySum A f x‖*‖frequencySum B U x‖^2 := by
    rw [frequencySum_product,norm_mul]
    ring
  simpa only [heq] using H

theorem cross_product_count_le_of_injections {ι κ ι' κ' : Type*}
    (A : Finset ι) (B : Finset κ) (A' : Finset ι') (B' : Finset κ')
    (f : ι → ℤ) (U : κ → ℤ) (f' : ι' → ℤ) (U' : κ' → ℤ)
    (e : ι → ι') (d : κ → κ')
    (he : Set.InjOn e (↑A : Set ι)) (hd : Set.InjOn d (↑B : Set κ))
    (heA : ∀ a ∈ A,e a ∈ A') (hdB : ∀ b ∈ B,d b ∈ B')
    (hef : ∀ a ∈ A,f' (e a)=f a) (hdU : ∀ b ∈ B,U' (d b)=U b) :
    (crossFrequencyPairs (A ×ˢ B) B (fun p => f p.1+U p.2) U).card ≤
      (crossFrequencyPairs (A' ×ˢ B') B' (fun p => f' p.1+U' p.2) U').card := by
  classical
  apply Finset.card_le_card_of_injOn (fun p : (ι × κ) × κ => ((e p.1.1,d p.1.2),d p.2))
  · intro p hp
    change p ∈ crossFrequencyPairs (A ×ˢ B) B (fun p => f p.1+U p.2) U at hp
    change ((e p.1.1,d p.1.2),d p.2) ∈
      crossFrequencyPairs (A' ×ˢ B') B' (fun p => f' p.1+U' p.2) U'
    simp only [crossFrequencyPairs,Finset.mem_filter,Finset.mem_product] at hp ⊢
    obtain ⟨⟨⟨ha,hb⟩,hc⟩,heq⟩ := hp
    refine ⟨⟨⟨heA _ ha,hdB _ hb⟩,hdB _ hc⟩,?_⟩
    simpa only [hef _ ha,hdU _ hb,hdU _ hc] using heq
  · intro p hp q hq hpq
    change p ∈ crossFrequencyPairs (A ×ˢ B) B (fun p => f p.1+U p.2) U at hp
    change q ∈ crossFrequencyPairs (A ×ˢ B) B (fun p => f p.1+U p.2) U at hq
    simp only [crossFrequencyPairs,Finset.mem_filter,Finset.mem_product] at hp hq
    obtain ⟨⟨⟨hpa,hpb⟩,hpc⟩,hpe⟩ := hp
    obtain ⟨⟨⟨hqa,hqb⟩,hqc⟩,hqe⟩ := hq
    exact Prod.ext (Prod.ext
      (he hpa hqa (congrArg (fun x : (ι' × κ') × κ' => x.1.1) hpq))
      (hd hpb hqb (congrArg (fun x : (ι' × κ') × κ' => x.1.2) hpq)))
      (hd hpc hqc (congrArg Prod.snd hpq))

/-- The complete tagged next count can be enlarged into independently
chosen full auxiliary and tuple domains, provided the literal integer
frequencies agree on the injective images. -/
theorem sum_next_step_count_le_enlarged {κ ι ν τ : Type*}
    (k : ℕ) (C : Finset κ) (params : κ → List (ℤ × ℤ)) (w : κ → ℤ)
    (N : ℤ) (B : Finset ι) (U : ι → ℤ)
    (A' : Finset ν) (B' : Finset τ) (f' : ν → ℤ) (U' : τ → ℤ)
    (e : (Σ _ : κ,ℤ × ℤ) → ν) (d : ι → τ)
    (hm : ∀ c ∈ C,∀ p ∈ params c,p.2≠0) (hw : ∀ c ∈ C,w c≠0)
    (he : Set.InjOn e (↑(aggregateNextDomain C w N k) : Set (Σ _ : κ,ℤ × ℤ)))
    (hd : Set.InjOn d (↑B : Set ι))
    (heA : ∀ a ∈ aggregateNextDomain C w N k,e a∈A')
    (hdB : ∀ b∈B,d b∈B')
    (hef : ∀ a∈aggregateNextDomain C w N k,f' (e a)=aggregateNextPhase k params w a)
    (hdU : ∀ b∈B,U' (d b)=(2:ℤ)^k*U b) :
    (∑ c ∈ C,((SeedCompletionBackward.nextStepSolutions k (realParameters (params c))
      (w c) N B (fun u => (U u:ℝ))).card : ℝ)) ≤ crossIntegral A' f' B' U' := by
  have heq := sum_nextStepSolutions_card_eq_cross k C params w N B U hm hw
  have hle := cross_product_count_le_of_injections
    (aggregateNextDomain C w N k) B A' B' (aggregateNextPhase k params w)
    (fun u => (2:ℤ)^k*U u) f' U' e d he hd heA hdB hef hdU
  apply (show (∑ c ∈ C,((SeedCompletionBackward.nextStepSolutions k (realParameters (params c))
      (w c) N B (fun u => (U u:ℝ))).card : ℝ)) ≤
      ((crossFrequencyPairs (A' ×ˢ B') B' (fun p => f' p.1+U' p.2) U').card : ℝ) from ?_).trans
      (cross_product_count_le_integral A' B' f' U')
  exact_mod_cast heq ▸ hle

#print axioms cross_product_count_le_of_injections
#print axioms sum_next_step_count_le_enlarged
end Waring.SeedCompletionEnlargedCross
