# Limiting arithmetic exponent-pair menu

The theorem `WaringLimit.limiting_real_budget` constructs a finite path whose total real charge is at most
`34360293397827451 / 5000000000000000`. It includes the initial logarithm, the 11,775 successive height-interval charges, the final plateau, and the continuous tail up to infinite modulus. All logarithms in the theorem are Mathlib real logarithms.

The source contains 184 arithmetic A/B words selected from the 987 candidate pairs up to length 14. `WaringLimit.Words` checks each pair against its actual transformations and validates all nonvanishing conditions for degrees at least 21. The 19 section files record the 11,776 height levels. Each transition uses an exponent pair followed by a chain of at most two Weyl intervals. The order of the entries and their integer encodings are specified in `WaringLimit.Check`. Each finite computation is checked by the Lean kernel with `decide +kernel`.

`WaringLimit.endpoint_covers` proves the continuous conductor inequalities on all the finite intervals. `WaringLimit.endpoint_stable` gives strict savings with the actual finite-degree radical losses. `WaringLimit.tail_weyl` proves the Weyl coverage beyond modulus 300 up to the cap √k/8. The coarse sufficient degree in `WaringLimit.endpoint_at_degree` comes from the rounding unit 10⁻³² used for the limiting computation. The separate finite-degree certificates use degree-specific grids and estimates.

`WaringLimit.Envelope` joins the two covers in `joined_tail`, proves the real conductor and cost conclusion in `effective_budget`, and evaluates the continuous tail as an improper Lebesgue integral in `tail_integral`.

The module `WaringLimit.SecondaryTail` proves that the conductor can extend to `9 * sqrt k / 20` when the marked pointwise estimate supplies the terminal saving. It also proves the negative sign and size of the normalized secondary charge. The pointwise estimate and its trace-torus application have additional analytic hypotheses beyond this calculation.

With the project's pinned Lean and Mathlib versions, run

```sh
lake build WaringLimit.Envelope WaringLimit.SecondaryTail
```

The archived proofs print their axiom sets. The integer path uses only propositional extensionality. The real analysis uses propositional extensionality, classical choice and quotient soundness. The implication from the conductor savings and real budget to the Waring bound also requires the analytic moment and representation theorems in the manuscripts.
