# Numerical certificates for the classical Waring bounds

The programs in this directory accompany M. Davidson, *Linear bounds and restricted moments in Waring’s problem*. Run them with Python 3.10 or newer from this directory. They use the Python standard library. Comparisons, rational exponents, conductor endpoints and final enclosures use integer arithmetic or `fractions.Fraction`. Decimal values in the output are for display.

| Command | Verified numerical statement |
| --- | --- |
| `python small_verify.py` | Publishes each positive minor-arc margin for the bounds at degrees 8 through 20. |
| `python linear_verify.py` | The elementary conductor menu supplies an upper coefficient below 6.919 for all degrees. |
| `python dual_verify.py` | Arithmetic exponent pairs supply an upper coefficient below 6.874 for all degrees. The same coefficient permits one extra unrestricted summand at every degree at least 21. |
| `python uniform_verify.py` | The sharper local Fourier transform gives a uniform coefficient below 6.873, with the additional summand for every degree at least 21. |
| `python asymptotic_verify.py` | The limiting arithmetic exponent-pair menu has coefficient at most 34360293397827451/5000000000000000, strictly below 6.873. |

The three compressed JSON files are data inputs. The corresponding `*-check.txt` files contain the results of a run. The asymptotic program generates its finite menu directly. No floating-point search or optimization package is required to validate a certificate.

## Small degrees

In `small_witness.json.gz` the seed arrays give the permissible mean-value exponents `lambda` for even orders 6, 8, ... in order, from the tables in R. C. Vaughan and T. D. Wooley, *Acta Arith.* **94** (2000), 203–285. The fourth-moment excess is `k-2`. Each subsequent seed excess is `lambda + k - order`. The loss-free smooth orders at degrees 8–16 are those of T. D. Wooley, *Acta Arith.* **176** (2016), 241–247, Table 2. For degrees 17–20 the terminal zero-excess orders follow by the ordinary minor-arc criterion proved in the manuscript. The checker verifies its strict inequalities.

Each certificate row stores the output order, the comparison order, the upper shortening parameter, the amplitude exponent and the resulting permissible excess. The certificate fields `shift` and `room` specify the difference between the upper and lower shortening parameters and the strict Gram margin above twice the amplitude exponent. The verifier interpolates the even seeds, constructs the stated rational mesh, checks conductor coverage and accepts an improved excess only after both branches of the recurrence pass. The last two tests cover minor arcs and the major-arc annulus.

## Linear coefficients

In `linear_witness.json.gz` the finite degree bands are adjacent and cover 21 through 999999999999. A list of moduli follows each pair of endpoints. A final band begins at 1000000000000 and has no upper endpoint. Moduli are in units of 1/10000. Heights have scale 10^32. Each row shortens by a factor using 99999/100000 of the certified modulus. The programs verify unions of intervals over the entire real conductor range; endpoint checks on a sampling grid alone would not suffice.

The pair-augmented witness `dual_witness.json.gz` has the same degree bands. Its rows specify either a union of classical conductor intervals or one of the words in `exponent_words.txt`. The empty word is encoded by a hyphen. To test the Taylor orders of the local phases the verifier processes the word from right to left. To compute the exponent pair and radical loss it processes the same word from left to right. The limiting verifier generates all distinct pairs through fourteen steps and checks 11776 height levels.

Logarithms are enclosed above by a rational series with a proven tail bound. The final infinite interval uses the continuous choice of height 1/(14 M²), up to a cap of size √k/8. The manuscript gives the calculus inequality bounding its contribution for every larger degree. These numerical certificates check the arithmetic deductions from the analytic estimates in the paper.

The uniform verifier uses the finite-degree witness through the band containing 180000² and builds a new depth-fourteen menu for every higher degree. In the local Fourier transform, conductor primes of exponent at most one contribute a single linear phase. After removing it, the remaining prime-power transforms survive on one residue class. Consequently the B-process preserves its input radical exponent, and every word used in the last degree band costs at most two powers of the radical after summing the initial classes.
