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

Three proposal commits sit on top of the reverts, each measured, output
byte-identical, all test suites green:

| state | elapsed | allocated |
|---|---|---|
| baseline (post-revert) | ~122s | 159 GB |
| + drop dead ReaderT layer | ~81s | 89 GB |
| + INLINABLE step tower (specialisation) | ~31s | 45 GB |
| + SizedRecursion `<>` fast path | ~28s | 45 GB |

The ReaderT layer was provably dead: no `local` anywhere, its only reader
(`failAndPrintStack`) has no call sites.

**Non-monadic experiment** (`sizeTermPure`, kept OFF this branch on the
local-only branch `nonmonadic-sizing-prototype`, not wired into the
driver): ~20x faster still (1.6s on tictactoe) but unsound — laziness
drops sizes recorded in undemanded branches; it recovers 8 of 12
recursion sites and under-counts 3. Small programs compile
byte-identically. The two leak points are documented in its haddock.
Machine.hs was not touched for the prototype.

## Not done / open

- The reverts plus the three monadic optimization commits are pushed
  (PR #150). The non-monadic prototype is deliberately not pushed: the
  branch carries one candidate solution (monadic) until the
  monadic-vs-non-monadic decision is made with sfultong.
- No replies posted on the PR; drafting them is the user's call.
