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

# IC logical storage and full sessions

`ICSpace.hs` sizes each program and prepares it once, under its EAL capture
layouts as the CLI does; asks for the all-input bound; runs a complete
session (simpleplus `3 4`; tic-tac-toe `1,4,2,5,3`, which plays through to
`Player 2 wins!`); prints whether the transcript equals the reference
evaluator's (`Transcript equality`; it does not fail on a mismatch); and
prints CPU seconds for "prepare" (which includes sizing: the clock starts
before `compileModules`), analysis and execution. Session peaks combine by
maximum, interactions by addition. The `Static:` line is the templates'
agents and ports.

```sh
cabal build lib:telomare --offline
cabal exec --offline -- ghc -O2 -package telomare bench/ICSpace.hs \
  -outputdir /tmp/telomare-ic-bench -o /tmp/telomare-ic-space-bench
/tmp/telomare-ic-space-bench [program.tel ...]     # from the repo root (reads Prelude.tel)
```

On 2026-09-28, with GHC 9.10.3, the library at `-O1` and the harness at
`-O2`, all three transcripts equal the reference's. Peaks and interactions
are deterministic:

| Session | Outcome | Peak agents | Peak ports | Peak pending | Interactions | Static agents / ports |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| simpleplus | Established | 18,579 | 38,826 | 82 | 1,517,868 | 14,924 / 30,960 |
| tc_ultra_minimal | Established | 559 | 1,140 | 10 | 524 | 660 / 1,348 |
| tic-tac-toe | Unknown (20 M-transition budget) | 265,483 | 579,888 | 342 | 15,168,230 | 45,801 / 94,592 |

Tic-tac-toe has no capture layouts (the program-level EAL solve gives up),
so it prepares generically. CPU times are one run each on an Intel Core
i7-1160G7 laptop that was not idle (load average about 6), so expect them
to vary between runs:

| Program | prepare (incl. sizing) | analyze | execute |
| --- | ---: | ---: | ---: |
| simpleplus | 1.53 s | 44.9 s | 3.22 s |
| tc_ultra_minimal | 0.016 s | 0.039 s | 0.001 s |
| tic-tac-toe | 20.3 s | 69.7 s | 44.6 s |

The bounds themselves, and what they mean, are in the README's
"IC logical storage" section; run `--ic --certificate` to reproduce them.
