import WaringSiegel.WSL2MomentLinearBox

/-!
# A concrete cubic Weyl kernel bound in an integral-coordinate box

The theorem combines proved Cauchy differencing with proved geometric-sum
cancellation. The resulting finite kernel depends only on the product of
the two shifts, which is the input required for divisor compression.
-/

noncomputable section
open scoped BigOperators Classical NumberField

namespace WaringSiegel.WSL2
variable {R ι κ : Type*} [CommRing R] [Fintype ι] [Fintype κ]

def cubicBoxKernel (e : R ≃+ (κ → ℤ)) (coord : R →+ (ι → ℤ))
    (a : R) (lo hi : κ → ℤ) (θ : ι → AddCircle (1 : ℝ)) (z : R) : ℝ :=
  ∏ i, characterIntervalBound (hi i+1-lo i).toNat
    (latticeCharacter (coord (6*a*z*e.symm (Pi.single i 1))) θ)

theorem cubicBoxKernel_nonneg (e : R ≃+ (κ → ℤ)) (coord : R →+ (ι → ℤ))
    (a : R) (lo hi : κ → ℤ) (θ : ι → AddCircle (1 : ℝ)) (z : R) :
    0 ≤ cubicBoxKernel e coord a lo hi θ z :=
  Finset.prod_nonneg (fun i _ => characterIntervalBound_nonneg _ _)

theorem coordinateLatticeBox_card (e : R ≃+ (κ → ℤ)) (lo hi : κ → ℤ) :
    (coordinateLatticeBox e lo hi).card = ∏ i, (hi i+1-lo i).toNat := by
  rw [coordinateLatticeBox, Finset.card_image_of_injective _ e.symm.injective]
  simp only [coordinateIntervalBox, Fintype.card_piFinset, Int.card_Icc]

theorem cubicBoxKernel_zero (e : R ≃+ (κ → ℤ)) (coord : R →+ (ι → ℤ))
    (a : R) (lo hi : κ → ℤ) (θ : ι → AddCircle (1 : ℝ)) :
    cubicBoxKernel e coord a lo hi θ 0 = (coordinateLatticeBox e lo hi).card := by
  rw [coordinateLatticeBox_card]
  simp [cubicBoxKernel, WaringSiegel.latticeCharacter_zero, characterIntervalBound]

theorem cubic_lattice_box_fourth_bound (e : R ≃+ (κ → ℤ)) (coord : R →+ (ι → ℤ))
    (lo hi : κ → ℤ) (H : Finset R)
    (hH : ∀ x ∈ coordinateLatticeBox e lo hi,
      ∀ y ∈ coordinateLatticeBox e lo hi, x-y ∈ H)
    (a b c d : R) (θ : ι → AddCircle (1 : ℝ)) :
    ‖finitePolynomialSum (coordinateLatticeBox e lo hi) coord (cubicPolynomial a b c d)
      (fun _ => 1) θ‖^4 ≤ (H.card : ℝ) *
        ∑ h ∈ H, ∑ j ∈ H, cubicBoxKernel e coord a lo hi θ (h*j) := by
  have h := cubic_fourth_le_linear_sums (coordinateLatticeBox e lo hi) H hH coord
    a b c d (fun _ => 1) θ
  simp only [doubleShiftedWeight, shiftedWeight, map_one, mul_one, one_mul] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro h hh
  apply Finset.sum_le_sum
  intro j hj
  have hlinear := norm_addChar_doubleOverlap_le e (linearLatticeCharacter coord (6*a*h*j) θ)
    (fun x => linearLatticeCharacter_norm coord _ x θ) lo hi h j
  simpa only [linearLatticeCharacter, AddChar.coe_mk, cubicBoxKernel, mul_assoc] using hlinear

/-- The actual integral-basis additive equivalence of the algebraic-integer ring. -/
def integerCoordinateAddEquiv (K : Type*) [Field K] [NumberField K] :
    (𝓞 K) ≃+ (NumberFieldCoordinateIndex K → ℤ) :=
  (NumberField.RingOfIntegers.basis K).equivFun.toAddEquiv

/-- Number-field cubic Weyl inequality with no abstract coordinate premises. -/
theorem numberField_cubic_box_fourth_bound (K : Type*) [Field K] [NumberField K]
    (lo hi : NumberFieldCoordinateIndex K → ℤ) (a b c d : 𝓞 K)
    (θ : NumberFieldCoordinateIndex K → AddCircle (1 : ℝ)) :
    let S := coordinateLatticeBox (integerCoordinateAddEquiv K) lo hi
    let H := additiveDifferences S
    ‖finitePolynomialSum S (integerCoordinates K) (cubicPolynomial a b c d)
      (fun _ => 1) θ‖^4 ≤ (H.card : ℝ) *
        ∑ h ∈ H, ∑ j ∈ H,
          cubicBoxKernel (integerCoordinateAddEquiv K) (integerCoordinates K) a lo hi θ (h*j) := by
  dsimp
  apply cubic_lattice_box_fourth_bound
  exact fun x hx y hy => additiveDifferences_mem _ hx hy

end WaringSiegel.WSL2
