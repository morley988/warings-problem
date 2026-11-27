# Conditional Waring–Siegel bounds from degree eleven

Apply this source supplement to an extracted copy of the pinned WaringLean project. Its base archive SHA-256 is `1c1d4e3de404656939296e45ec5704031e89cb3ac8c07c79a08e09c60c65e4b0`. The supplement uses Lean 4.24.0 and the same mathlib revision.

For every integer degree at least eleven, `field_marked_orders_eleven` and `field_loss_free_eleven` establish the conditional marked order and trace-moment bound. The theorem `field_waring_eleven_of_differencing_and_arcs` concludes the actual bounded totally positive representation predicate, with an order s satisfying (s+1)/k < 6.873. The premises concern algebraic power-equality counts, the shortening estimate, finite conductor coverage between degrees 21 and 2500, and arc estimates at the chosen order.

From the supplement directory run the following command after obtaining the base project's mathlib cache. The script builds the frozen base and adds the source modules to the extracted copy.

```sh
sh replay.sh /path/to/extracted/WaringLean
```

The axiom transcript records the kernel output for these endpoints. SHA256SUMS covers each supplied file.
