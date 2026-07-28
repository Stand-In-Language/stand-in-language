# Programs that show where sizing stops

Telomare is total because every `{test, recursion, last}` in a program is
compiled into a loop with a fixed iteration count, and that count is *inferred*
rather than declared. The compiler finds it by unrolling the recursion
abstractly over a symbolic input until the test stops. A program whose count
cannot be found does not compile at all — there is no third outcome where an
under-counted program is accepted and might diverge.

These programs are the two ways that inference fails. Each one states what it
demonstrates, what the compiler says, and how to fix it, with the fix commented
out beside the code that provokes the failure. They are driven by
`test/SizingTests.hs`, which asserts the failure kind and the source location.

| Program | Fails with | Fixable by a bigger budget? |
| --- | --- | --- |
| `unbounded-input-recursion.tel` | the recursion's test reads input that nothing bounds | No — no finite count exists to find |
| `over-budget-recursion.tel` | the search ran past its unrolling budget | Yes — or by needing fewer levels |

The distinction is the point. The first is a statement about the program: until
some refinement bounds the input, the recursion has no provable depth. The
second is a statement about the search: the depth exists, the compiler just was
not allowed to look far enough. Before this the two were reported identically,
as a bare integer that was not even the recursion's identifier.

`over-budget-recursion.tel` compiles at the CLI's budget of 65536; the test
suite drives it at a budget of 5 so the path is exercised in milliseconds
rather than by 65536 abstract unrollings.

## Seeing the counts a program did get

For programs that do size, the counts are worth looking at:

```sh
cabal run telomare -- --certificate simpleplus.tel
```

These are not new claims about the program. They are the very numbers the
compiler bakes in to make it total, which until now were computed and thrown
away.

Both of these programs still *run* under `--fast`, which skips sizing and
unrolls each recursion on demand. That is not a counterexample to anything: it
proves nothing about termination, which is exactly what sizing is for, and a
recursion with no bound runs until the fuel cap stops it.
