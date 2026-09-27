# Nested-defer compilation

`DeferCompile.hs` measures construction of IC templates, excluding reduction
and readback. Each run builds nested defers with distinct bodies and forces
the completed template table. The arguments are depth and repeat count;
reported CPU time is the total across those repetitions.

Build against the library revision being measured:

```sh
cabal build lib:telomare --offline
cabal exec --offline -- ghc -O2 -package telomare bench/DeferCompile.hs \
  -outputdir /tmp/telomare-defer-bench -o /tmp/telomare-defer-bench-run
/tmp/telomare-defer-bench-run 100 3
/tmp/telomare-defer-bench-run 200 3
/tmp/telomare-defer-bench-run 400 3
```

On 2026-09-23, with GHC 9.10.3, the library built by Cabal at `-O1`,
and the harness at `-O2`:

| Depth | Repetitions | Before (`bc3d2828`), CPU ms | Bottom-up hashes, CPU ms |
| ---: | ---: | ---: | ---: |
| 100 | 3 | 124.647 | 4.820 |
| 200 | 3 | 522.421 | 8.997 |
| 400 | 3 | 2415.672 | 19.059 |

These are single local measurements of a synthetic worst case for repeated
lifting, not a general application speedup. Other compilation costs, including
exact-body comparisons within a hash bucket, remain.
