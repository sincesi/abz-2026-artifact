# ABZ 2026 — Identity-disclosure verification

[Research Hub](https://github.com/sincesi/research-hub) · [Repository](https://github.com/sincesi/abz-2026-artifact)

Related paper: *Relational Verification of Identity Disclosure Using Alloy*, Seungil Yang, Peter Rivière, and Toshiaki Aoki. This repository contains a later executable reconstruction for Table 2, with explicitly strengthened assumptions.

Zenodo DOI: not yet assigned to this artifact. The IEEE Access DOI belongs to a different artifact and must not be used here.

## Table 2 reproduction

Open **models/ABZ_Table2_corrected.als** in Alloy and execute the four `case*` commands. This complete ABZ-style executable reconstruction includes the original/external/released schemas, generalization map, all three transformation families, exact/approximate matching, disclosure queries, and a non-disclosure assertion.

| Command | Transformation + matching | Expected / observed |
|---|---|---|
| case1_gen_exact | Generalization + Exact | SAT |
| case2_del_exact | Deletion + Exact | SAT |
| case3_noise_approx | Noise + Approx | SAT |
| case4_noise_exact | Noise + Exact | UNSAT |

## Why the two fixes are required

1. **Non-zero bounded noise:** `DeIdentified_noise` uses the bound `n = 2` and `r.age != o.age`. The paper's zero-inclusive interval alone permits unchanged age and therefore an exact-match disclosure witness.
2. **ExternalConsistentWithOriginal:** equal `name` values require equal original/external age, zip, DOB, sex, price, drug name, and the corresponding generalized drug code. Alloy does not infer those equalities from equal names. Without this fact, even non-zero noise can match an inconsistent external age.

Together, disclosure requires `o.name = e.name`, consistency gives `o.age = e.age`, non-zero noise gives `r.age != o.age`, and exact matching requires `r.age = e.age`: a contradiction. Approximate matching permits an age difference up to `k = 2`, so disclosure remains satisfiable.

These are explicit strengthened assumptions for reproducing **Table 2's outcomes**. This is not a claim that the paper's original Listing 4, unchanged, implies Noise+Exact UNSAT, nor a recovery of the exact executable used for publication. The basis is the earlier integrated conversation model, cross-checked against the locally supplied ABZ manuscript listings and Table 2. Generalization and deletion have equivalent constraints in this shared schema: `name` is omitted and `drugName` is represented by `drugCode` in both.

## Original / diagnostic version

`diagnostics/ABZ_original_bounded_noise.als` preserves the previous integrated file byte-for-byte. It allows zero noise, lacks external consistency, and also includes a non-zero-noise variant. Its old comments claiming non-zero noise alone gives UNSAT are **incorrect**; both exact-noise queries actually return SAT, and both non-disclosure assertions have counterexamples. Use the corrected file above for Table 2.

The corrected file also retains `DeIdentified_noise_original` and two diagnostics:

- `diagnostic_zero_noise_exact`: SAT even with consistency, demonstrating why excluding zero is necessary.
- `diagnostic_nonzero_noise_feasible`: SAT, showing the corrected transformation is feasible.

## Reproduce the verification

Verified with Alloy 6.1.0.202111031525, SAT4J, Java 15.0.1, and **Prevent overflows enabled** (`noOverflow=true`). Every command uses `for 3 but 1 D_orig, 1 D_rel, 1 D_ext, 6 Int`. Record scopes are upper bounds; the witness queries require a record in each dataset. Six-bit integers range from -32 through 31; age is an abstract numeric value here, not a realistic population-age range. Do not use age 40 with these scopes. Wider integer scopes or concrete datasets are separate experiments.

In the GUI, enable Prevent overflows and execute each command. For an automated regression run with a JDK and the tested Alloy JAR:

```sh
python3 validation/verify.py /path/to/org.alloytools.alloy.dist.jar
```

The runner checks all seven corrected commands and all twelve original diagnostics, fails on any unexpected result, and writes logs and witness XML files to `validation/`. Checked-in `results.tsv` files record the actual run. A `check` result of UNSAT means no counterexample within the stated bounds; SAT means a counterexample. These results do not establish universal real-world anonymity or unique identification, which this reachability model does not require.

## Reuse and citation

No open-source license has been selected for this reconstructed artifact yet. Contact the authors before reuse requiring permission. Cite the paper for its research contribution and the specific archived artifact version for reproducibility once its DOI is available.
