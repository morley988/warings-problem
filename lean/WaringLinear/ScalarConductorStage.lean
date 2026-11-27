import WaringLinear.ConductorMomentStep
import WaringLinear.ScalarArithmeticCover

/-! # Concrete conductor recursion for classical marked roots -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace WaringLinear

/-- Remove the unique designated mark i from the parent roots marked by i. -/
def scalarChild (s : Finset ℕ) (mark : ℕ→ℕ) (i : ℕ) :=
  dividedState (s.filter (fun n => mark n=i)) i

/-- The roots left after all primes in this mask have been removed. -/
def scalarCoprime (s P : Finset ℕ) := s.filter fun n => ∀q∈P,¬q∣n

/-- Squared tail on the finite q-th multiplication fibre at x. -/
noncomputable def scalarFibreMass (q : ℕ) (hq : 0<q) (X z : ℝ)
    (H : ScalarTorus → ℂ) (x : ScalarTorus) : ℝ := by
  classical
  letI := circleKernelFintype q hq
  exact ∑ a : (circleCover q).ker,
    {u:ScalarTorus | X^(1-z)≤2*‖H u‖}.indicator (fun u => ‖H u‖^2) (x+a.1)

/-- For an arbitrary finite set of positive integer roots with a divisor
mark assigned to each root, suitably controlled large fibres and moments of
the actual shortened root sets give the stated two-branch excess. All masks
consist of primes and each distinct exceptional divisor is counted once.
No orthogonality or Haar-cover identities are left as hypotheses. -/
theorem classical_marked_conductor_step
    (s marks bad : Finset ℕ) (mark : ℕ→ℕ) (mask : marks→Finset ℕ)
    (k : ℕ) (hc : ∀ n∈s,mark n∈marks) (hdv : ∀n∈s,mark n∣n)
    (hm : ∀ i ∈ marks, 0 < i) (hd : ∀ j ∈ bad, 0 < j) (hpMask : ∀ i q, q ∈ mask i → q.Prime)
    (hbadSet : ∀ i t, t ⊆ mask i → t.Nonempty → (∏q∈t,q)∈bad)
    (X p h z θ D E A L P B C D₀ Z : ℝ)
    (hX : 1≤X) (hp : 1≤p) (hh : 0<h) (hhp : h<p+2)
    (hD : 0≤D) (hL : 0≤L) (hP : 0≤P) (hB : 0≤B) (hC : 0≤C) (hD₀ : 0≤D₀)
    (hmass : (∑i∈marks,(i:ℝ)⁻¹)≤1) (hsize : ∀i∈marks,X^θ≤(i:ℝ))
    (hmask : ∀i,2*(2:ℝ)^(mask i).card≤D₀)
    (hfibre : ∀i:marks,∀x,scalarFibreMass (i.val^k) (pow_pos (hm _ i.property) _)
      X z (scalarPowerSum (scalarCoprime s (mask i)) k) x ≤ B*X^2)
    (hlow : (∫x,‖scalarPowerSum s k x‖^h)≤L*X^(h-(k:ℝ)+E))
    (hshort : ∀i∈marks,(∫x,‖scalarPowerSum (scalarChild s mark i) k x‖^p)
      ≤C*(X/i)^(p-(k:ℝ)+D))
    (hexcept : ∀j∈bad,(∫x,‖scalarPowerSum (dividedState s j) k x‖^(p+2))
      ≤P*(X/j)^(p+2-(k:ℝ)+A))
    (hZ : (∑j∈bad,((j:ℝ)^(p+2-(k:ℝ)+A))⁻¹)≤Z)
    (hAh : E-(p+2-h)*z≤A) (hAD : (1-θ)*D≤A) :
    (∫x,‖scalarPowerSum s k x‖^(p+2))≤(L+4*B*C+D₀^(p+2)*(P*Z))*X^(p+2-(k:ℝ)+A) := by
  classical
  let π (i : marks) := circleCover (i.val^k)
  let ψ (j : bad) := circleCover (j.val^k)
  letI kerFintype (i : marks) := circleKernelFintype (i.val^k) (pow_pos (hm _ i.property) _)
  have hcard (i : marks) : (Fintype.card (π i).ker : ℝ)=(i.val:ℝ)^(k:ℝ) := by
    rw [Real.rpow_natCast]
    exact_mod_cast scalar_kernel_card (i.val^k) (pow_pos (hm _ i.property) _)
  apply conductor_fourier_moment_step volume π ψ
    (fun i => measurePreserving_circleCover _ (pow_pos (hm _ i.property) _))
    (fun j => measurePreserving_circleCover _ (pow_pos (hd _ j.property) _))
    (fun i => continuous_circleCover _) (fun j => continuous_circleCover _)
    (scalarPowerSum s k) (fun i => scalarPowerSum (scalarChild s mark i) k)
    (fun i => scalarPowerSum (scalarCoprime s (mask i)) k)
    (fun j => scalarPowerSum (dividedState s j) k)
    (scalarPowerSum_continuous ..) (fun _ => scalarPowerSum_continuous ..)
    (fun _ => scalarPowerSum_continuous ..) (fun _ => scalarPowerSum_continuous ..)
    (fun i => (i.val:ℝ)) (fun j => (j.val:ℝ)) X p k h z θ D E A L P B C D₀ Z
    hX hp hh hhp hD hL hP hB hC hD₀
    (fun i => by change 0<(i.val:ℝ); exact_mod_cast hm _ i.property)
    (fun j => by change 0<(j.val:ℝ); exact_mod_cast hd _ j.property)
    (by exact (Finset.sum_coe_sort marks (fun n:ℕ => (n:ℝ)⁻¹)).le.trans hmass) (fun i => hsize _ i.property)
    hcard _ _ hfibre hlow (fun i => hshort _ i.property) (fun j => hexcept _ j.property)
    (by exact (Finset.sum_coe_sort bad (fun n:ℕ => ((n:ℝ)^(p+2-(k:ℝ)+A))⁻¹)).le.trans hZ) hAh hAD
  · intro x
    exact (scalar_parent_states s marks mark k hc hdv x).trans
      (Finset.sum_coe_sort marks (fun i => scalarPowerSum (scalarChild s mark i) k (i^k • x))).symm
  · rintro x ⟨i,hi⟩
    obtain ⟨t,ht,he,_,h⟩ := scalar_exceptional_child s (mask i) k x (hpMask i) hi
    let d := ∏q∈t,q
    refine ⟨⟨d,hbadSet i t ht he⟩,h.trans ?_⟩
    apply mul_le_mul_of_nonneg_right (hmask i) (norm_nonneg _)

#print axioms classical_marked_conductor_step
end WaringLinear
