# Handoff

Branch: `hhefesto/simplification-review` (PR #150). Updated 2026-08-26.

## Where things stand

sfultong's review (CHANGES_REQUESTED) had two inline comments; both are
addressed, and his sizing-speed question is answered with measurements.

1. **"Leave Machine.hs alone"** — done: `Restore Machine.hs to its master
   state` puts the file back byte-for-byte, including the pure step family
   the branch had deleted (knock-ons: Meter.hs regains its local
   `truncateToData`, Reference.hs/Size.hs use Machine's `debugTrace` again).
2. **"Finer-grained debug switches are better"** — done: `Restore the
   per-module debug switches` returns the local `debug`/`debugTrace` blocks
   to Size, Size.IR (primed), Resolve, TypeCheck and Driver;
   `Telomare.Util` keeps only `padRight`/`plural`.

## The sizing-speed question (benchmark: `telomare --compile tictactoe.tel`)

Five optimization commits sit on top of the reverts, each measured, output
byte-identical, all test suites green:

| state | elapsed | allocated |
|---|---|---|
| baseline (post-revert) | ~122s | 159 GB |
| + drop dead ReaderT layer | ~81s | 89 GB |
| + INLINABLE step tower (specialisation) | ~31s | 45 GB |
| + SizedRecursion `<>` fast path | ~28s | 45 GB |
| + hand-written INLINE Traversable instances | ~14s | 9.8 GB |

The ReaderT layer was provably dead: no `local` anywhere, its only reader
(`failAndPrintStack`) had no call sites (both now deleted, commit
`Finish the dead ReaderT excision`).

Round 2 was profile-driven (`-fprof-late`): the first profile showed ~75%
of runtime in the *derived* Traversable methods for BasicExprF/UnsizedExprF
plus the StrictAccum fmap/liftA2 boxes they forced — derived methods carry
no unfoldings, so the INLINABLE step tower still called them unspecialised.
Hand-writing `traverse` with INLINE (IR/Base.hs + Size/IR.hs) fixed that:
28s → 13.7s, 45 GB → 9.8 GB. A second profile now shows 81% of time inside
the single specialised interpreter worker (`$s$wstuckStepM`) with the
SizedRecursion merge at 3.7% and nothing else above 2% — the monadic
implementation is at its practical floor short of algorithmic changes
(e.g. environment-passing instead of substitution per defer application).
Also measured and rejected: `-O2` on the library (no effect) and
`-fexpose-all-unfoldings`/`-fspecialise-aggressively` (~8%, allocation
unchanged — superseded by the hand-written instances).

Overall: ~122s → ~14s, an 8.7x speedup, all sound.

**Non-monadic experiment** (`sizeTermPure`, kept OFF this branch on the
local-only branch `nonmonadic-sizing-prototype`, not wired into the
driver): ~20x faster still (1.6s on tictactoe) but unsound — laziness
drops sizes recorded in undemanded branches; it recovers 8 of 12
recursion sites and under-counts 3. Small programs compile
byte-identically. The two leak points are documented in its haddock.
Machine.hs was not touched for the prototype.

## Not done / open

- Pushed (PR #150): the reverts plus the first three monadic optimization
  commits. NOT pushed (local only, standing instruction): the round-2
  commits `Hand-write the sizing IR's Traversable instances` and `Finish
  the dead ReaderT excision`. The non-monadic prototype is also deliberately
  unpushed (local-only branch `nonmonadic-sizing-prototype`): the branch
  carries one candidate solution (monadic) until the monadic-vs-non-monadic
  decision is made with sfultong.
- No replies posted on the PR; drafting them is the user's call.
