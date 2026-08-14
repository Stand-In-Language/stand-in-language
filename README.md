# Telomare
> A simple but robust virtual machine

<p float="left">
  <img src="https://github.com/Stand-in-Language/stand-in-language/actions/workflows/telomare-ci.yml/badge.svg" />
  <a href="https://gitter.im/stand-in-language/Lobby?utm_source=badge&utm_medium=badge&utm_campaign=pr-badge&utm_content=badge"
     title="Join the chat at https://gitter.im/stand-in-language/Lobby">
    <img src="https://badges.gitter.im/stand-in-language/Lobby.svg" /> 
  </a>
</p>


A virtual machine with a simple grammar evolved from simply typed lambda calculus, that eventually will have powerful static checking and an optimizing backend.

## Warning
This project is in active development. Do expect bugs and general trouble, and please let us know if you run into any by creating a new issue if one does not already exist.

## Quick Start

1. Clone this repository and change directory to it:
   ```sh
   $ git clone https://github.com/Stand-In-Language/stand-in-language.git
   $ cd stand-in-language
   ```
2. [Install Nix](https://nixos.org/nix/download.html):
   ```sh
   $ curl https://nixos.org/nix/install | sh
   ```
3. Optional (reduces build time by using telomare's cache):
   ```sh
   # Install cachix with nix-env or adding `cachix` to your `/etc/nixos/configuration.nix`'s' `environment.systemPackages` if in NixOS.
   $ cachix use telomare
   ```
4. Enter a Nix shell. This will setup an environment where all external dependencies will be available (such as `cabal` for building):
   ```sh
   $ nix develop # or nix develop -c zsh
   ```
5. Build the project:
   ```sh
   $ cabal build # or nix build
   ```
6. Run the tictactoe example and start playing with a friend (or run your own telomare file):
   ```sh
   $ cabal run telomare -- tictactoe.tel # or nix run . -- tictactoe.tel
   ```
7. Profit!

## Resource reporting

Telomare is total because every `{test, recursion, last}` in a program is
compiled into a loop whose iteration count the compiler *infers*, by unrolling
the recursion abstractly over a symbolic input until its test stops. A program
whose counts cannot be found does not compile.

Those counts are worth seeing, so they are reported rather than discarded.
There are exactly two reports: `--certificate`, which says what the compiler
knows without running the program, and `--meter`, which says what one run
actually cost.

```sh
$ cabal run telomare -- --certificate simpleplus.tel
recursion sites (iterations, over every input):
  Prelude:30:18 (#0)     <= 11
  Prelude:48:23 (#1)     <= 7
  simpleplus:12:42 (#2)  <= 10
  simpleplus:12:28 (#3)  <= 10

sizing budget in force: 65536 unrollings

recursion nesting (structural, approximate):
  triple         function             levels
  Prelude:11:19  Prelude.d2c          0, 1
  Prelude:44:34  Prelude.foldr.fixed  0, 1
```

The counts assert nothing new: they are the numbers already baked into the
program to make it total, and they hold for every input. The nesting below them
is a separate, structural reading of the source — it costs milliseconds rather
than the sizing pass's minutes, and it also reports which bindings are used
below the level they were bound at (on `tictactoe.tel`, `whoWon.board : !!`),
which is what duplicating a value across recursion levels costs. The two lists
index differently — a count is per instantiation, a nesting row is per `{test,
recursion, last}` as written — so they do not line up row by row, and the
report says so.

`--meter` runs the program and reports what the run cost — steps taken, and
term nodes built. Those are measurements of one run, not predictions about the
next:

```sh
$ printf '3 4\n' | cabal run telomare -- --meter simpleplus.tel
steps (measured): 46652
nodes built (measured): 13660
```

Neither is a memory figure, deliberately. Telomare's evaluator shares
environments rather than copying them, so counting the term it holds as a tree
counts shared structure once per reference — for `tictactoe.tel` that reads
about 1.2TB for a run that fits in a few GB. An honest memory figure needs
reachability over distinct nodes, which is not implemented; use `+RTS -s` for
the real thing.

When sizing fails, the error names the recursion, where it is, and which of the
two failures it is — a budget that was too small, or an input that nothing
bounds. Only the first is fixable by raising the budget. See
`test/programs/limits/` for a worked example of each.

## Compiling once

Sizing is the slow part — about 70 seconds for `tictactoe.tel` — and it gives
the same answer every time, because it runs the program over a *symbolic*
input. So it need only happen once:

```sh
$ cabal run telomare -- tictactoe.tel --compile      # ~70s, writes tictactoe.telc
$ cabal run telomare -- tictactoe.telc               # starts immediately
```

A `.telc` file holds the sized program together with its counts and its
certificate, so running it skips parsing, typechecking, resolving and sizing,
and `--certificate` on it prints instantly. If the sources are still around and
have changed since it was built, running it says so and carries on — an
artifact is expected to outlive the checkout it came from.

## Running without sizing

`--fast` skips sizing altogether and runs the recursion on demand, unrolling
one layer per call instead of a count inferred in advance. It starts
immediately, plays `tictactoe.tel` identically, and will even run programs the
sizing pass rejects:

```sh
$ printf '3 4\n' | cabal run telomare -- simpleplus.tel --fast --meter
enter two digits separated by a space
3 plus 4 is 7
function applications (measured): 2,560
gate selections (measured):       83
recursion unrolls (measured):     110 across 4 sites

  site   source            function          unrolls
  #1     Prelude:48:23     Prelude.foldr     48
  #0     Prelude:30:18     Prelude.dMinus    40
  #2     simpleplus:12:42  simpleplus.doAdd  12
  #3     simpleplus:12:28  simpleplus.doAdd  10
```

Per-site unrolls are only available this way: sizing compiles each site into a
loop of a fixed length, after which the site no longer exists to attribute
anything to. They are totals over the run rather than depths, so they are not
the same measurement as the certificate's per-instantiation counts.

What `--fast` gives up is the thing sizing is for: **nothing proves the program
terminates**. A recursion that would not have sized runs until a fuel cap stops
it (default 16777216 applications and unrollings per iteration of `main`,
`--fuel N` to change it, `--fuel 0` to lift it). That is why it is a flag and
why sizing remains the default.

## Telomare REPL
1. Run:
   ```sh
   $ cd <your/local/proyect/location>/telomare
   $ nix develop -c zsh
   $ cabal run telomare-repl -- --haskell # or nix run .#repl
   ```
2. Profit!

## Editor Support (LSP)

Telomare ships a language server (`telomare-lsp`) and an Emacs major mode
under [`emacs-telomare-mode/`](emacs-telomare-mode/), with variants for
Spacemacs, Doom, and vanilla Emacs.

### LSP capabilities

The language server provides:

- **Diagnostics** — on every document open and edit it reports parse
  errors, missing imported modules, undefined variable references, and
  resolver errors. Diagnostics are cleared when the document is closed.
- **Go to definition** — jumps to local `let`, lambda, and case-pattern
  binders, to top-level definitions, and to definitions in qualified
  imported modules.
- **Find references** — lists every reference to a symbol, optionally
  including its declaration.
- **Semantic-token highlighting** — keywords, comments, strings,
  numbers, and operators, for the whole file or a requested range.
- **Code action** — *Partially evaluate*: select an expression and the
  server evaluates it, reporting the result in an editor popup.
- **Workspace commands**:
  - `telomare.version` — reports the server version as a UTC timestamp.
  - `telomare.partialEval` — evaluates a given expression; this backs
    the partial-evaluation code action.

Document sync is full-text (whole-document). Hover and rename are not
implemented yet.

### Installing the Emacs mode

The recommended Spacemacs setup is to load Telomare's Emacs mode from the
same Telomare flake input that provides the language server. Do not point
Spacemacs at a random checkout unless you are actively developing the mode;
make the editor use the same pinned source that NixOS or Home Manager builds.

For a NixOS/Home Manager Spacemacs config, add Telomare as a flake input and
load the mode file from that input:

```elisp
(load "${telomare}/emacs-telomare-mode/telomare-mode-spacemacs.el")
```

The mode auto-detects the surrounding flake source path and starts the LSP with
`nix run path:<telomare-source>#lsp --`. This matters for Nix store paths:
`nix run /nix/store/...-source#lsp --` is parsed incorrectly by Nix, while
`nix run path:/nix/store/...-source#lsp --` is the intended absolute-path flake
form.

For a manual checkout-based setup, load the mode from this repository and set
`TELOMARE_ROOT` only if auto-detection cannot find `flake.nix`:

```elisp
(load "/path/to/telomare/emacs-telomare-mode/telomare-mode-spacemacs.el")
```

For Doom and vanilla Emacs setup, see
[`emacs-telomare-mode/README.md`](emacs-telomare-mode/README.md).

### Keybindings

The mode binds only features the server implements. Some entries below
come from `lsp-mode` rather than Telomare's mode — these are marked
*(lsp-mode)*. Spacemacs exposes the major-mode leader as `SPC m` in Evil
state and as `M-m m` in holy-mode; the leader entries are otherwise the
same bindings.

**Spacemacs — Evil mode** (`SPC m` major-mode leader):

| Key | Action |
|-----|--------|
| `SPC m g` | Go to definition |
| `SPC m G` | Find references |
| `SPC m a` | Execute code action (partial evaluation) |
| `SPC m v` | Show Telomare LSP version |
| `C-c C-v` | Show Telomare LSP version |
| `g d` | Go to definition *(lsp-mode / Evil default)* |

**Spacemacs — holy mode** (`M-m m` major-mode leader):

| Key | Action |
|-----|--------|
| `M-m m g` | Go to definition |
| `M-m m G` | Find references |
| `M-m m a` | Execute code action (partial evaluation) |
| `M-m m v` | Show Telomare LSP version |
| `C-c C-v` | Show Telomare LSP version |
| `M-.` | Go to definition *(lsp-mode)* |
| `M-?` | Find references *(lsp-mode)* |
| `M-,` | Jump back *(xref)* |

Vanilla Emacs binds `M-.`, `M-?`, `C-c a`, and `C-c C-v`.

### Troubleshooting

If navigation does not work, check the active LSP session with
`M-x lsp-describe-session`, restart it with `M-x lsp-workspace-restart`, and
confirm the server command with:

```elisp
M-: (telomare--lsp-command)
```

The expected command shape is:

```elisp
("nix" "run" "path:/nix/store/...-source#lsp" "--")
```

### LSP version command

`C-c C-v` (or `SPC m v` / `M-m m v` in Spacemacs) reports the server
version as a UTC timestamp truncated to minutes, using the parent commit
timestamp when git history is available and the flake source timestamp
when launched from a Nix store source without `.git`. It can also be
invoked directly:

```elisp
(lsp-request "workspace/executeCommand"
             `(:command "telomare.version" :arguments []))
```

The command shows an editor message such as:

```text
Telomare LSP version: 2026-05-22T10:14Z
```

## Git Hooks

You can setup your git configuration to automatically format and look for lint suggestions. Just run:

``` sh
$ git config core.hooksPath hooks
```

## Surface Syntax

Telomare source is a small expression grammar. Applications associate to the
left, definitions in the same `let` or module are mutually visible, and
continuation lines must remain indented under the expression they continue.

```text
module      ::= (import | definition)*
import      ::= "import" module-name
              | "import" "qualified" module-name "as" identifier
definition  ::= identifier (":" expression)? "=" expression
              | "[" identifier ("," identifier)* "]" "=" expression
expression  ::= "let" definition* "in" expression
              | "if" expression "then" expression "else" expression
              | "\\" pattern+ "->" expression
              | "case" expression "of" alternative+
              | atom+
alternative ::= pattern "->" expression
atom        ::= identifier | natural | string | "$" natural | "#" atom
              | "(" expression ")" | "(" expression "," expression ")"
              | "[" (expression ("," expression)*)? "]"
              | "{" expression "," expression "," expression "}"
pattern     ::= identifier | "_" | natural | string
              | "(" pattern "," pattern ")"
              | "(" pattern ":" expression ")"
identifier ::= letter (letter | digit | "_" | ".")*
```

The keywords are `let`, `in`, `if`, `then`, `else`, `case`, `of`, `import`,
`qualified`, and `as`. Naturals must fit in the implementation's `Int` range;
oversized literals are parse errors rather than wrapping.

UDTs deliberately retain the existing list-definition convention:

```telomare
[T, constructor, extractor, operation] = \h ->
  [ constructorBody, extractorBody, operationBody ]
```

Expansion recognizes this only when the first name starts uppercase and the body
is a lambda. There must be exactly one more name than body slots: the extra
name is the generated validator. This classification is not parser behavior.

| Source form | Parsed representation | Immediate expansion result |
| --- | --- | --- |
| `\p1 p2 -> e` | `LamPatF` | nested `LamF`, with cases for patterns |
| `let defs in e` | `LetSugarF` | `LetUPF` |
| `x : T = e` | annotated `SingleDefF` | `CheckF T e` |
| `[a, b] = e` | `ListDefF` | one binding per name |
| `[T, ...] = \h -> [...]` | `ListDefF` | UDT bindings and validator |
| `import ...` | `ModuleImportItem ImportDecl` | `ExpandedModuleImport ImportDecl` |
| `case e of ...` | `CaseUPF` | lowered later by `Telomare.Desugar` |

## Compiler stages

The library is organized so that modules delimit the standard stages of the
pipeline. In pipeline order:

| Stage | Modules | What happens |
| --- | --- | --- |
| Parse | `Telomare.Parse` | megaparsec grammar producing raw `ParsedSurfaceTerm` trees: no expansion, resolving, or semantic checks. Modules use `ModuleItem`; multi-pattern lambdas, refinement annotations, and list definitions remain as written. Complete public runners reject trailing input. |
| Expand | `Telomare.Expand` | removes the `SugarTermF` fragment (`ParsedSurfaceTerm -> ExpandedSurfaceTerm`), eliminating `LamPatF`/`LetSugarF` by type: multi-pattern lambdas become nested lambdas with hygienic case destructuring, list definitions and UDT conventions expand into bindings, and refinement annotations fold into `CheckF`. Module imports remain typed `ImportDecl` values in `ExpandedModuleItem`. |
| Desugar | `Telomare.Desugar` | binds and optimizes builtins and removes the case capability (`ExpandedSurfaceTerm -> DesugaredSurfaceTerm`), lowering cases to nested conditionals before resolution. |
| Resolve | `Telomare.Resolve` | resolves typed module imports, scope-checks only `DesugaredSurfaceTerm`, performs de Bruijn conversion and hash folding, and lowers core terms (`splitExpr`: `Term2 -> Term3`). Documents the dual `process`/`processWlet` pipeline. |
| Type check | `Telomare.TypeCheck` | unification-based check of `Term3` against the main type. |
| Size (totality) | `Telomare.Size`, `Telomare.Size.IR`, `Telomare.Machine` | telomare's distinguishing stage: `sizeTermM` abstractly interprets the program over symbolic input and infers a finite iteration count for every recursion site, then bakes the counts in (`Term3 -> CompiledExpr`). A program that cannot be sized does not compile. `Machine` is the shared step-algebra the sizing pass and the evaluators are assembled from. |
| Evaluate | `Telomare.Eval.Reference`, `Telomare.Eval.Meter`, `Telomare.Fast` | the reference interpreter, the step-counting meter, and the fuel-based fast path (which skips sizing). |
| Drive | `Telomare.Driver`, `Telomare.Artifact`, `Telomare.Certificate`, `Telomare.Levels` | orchestration (`compileModules`, `evalLoop`), `.telc` artifacts, and the static report. |

The IR vocabulary shared by all stages lives under `Telomare.IR.*`
(`Loc`, `Base`, `Types`, `Surface`, `Core`, `Builder`), with the error
types in `Telomare.Error` and pretty-printing in `Telomare.PrettyPrint`.
`Telomare.Lexical` holds the lexical facts of the language — the reserved
words, the identifier character classes, the comment delimiters — so that the
parser and the language server cannot disagree about them, and
`Telomare.Util` holds the few helpers that depend on no other Telomare module.

## Contributing
If you'd like to contribute, please fork the repository and use a feature branch. Pull requests are warmly welcome.

## Links
1. [A Better Model of Computation](http://sfultong.blogspot.com/2016/12/a-better-model-of-computation.html?m=1) by Sfultong
2. [SIL: Explorations in non-Turing Completeness](http://sfultong.blogspot.com/2017/09/sil-explorations-in-non-turing.html?m=1) by Sfultong
3. [Deconstructing Lambdas, Closures and Application](http://sfultong.blogspot.com/2018/04/deconstructing-lambdas-closures-and.html?m=1) by Sfultong
4. [Join the community's chat](https://gitter.im/stand-in-language/Lobby)


## Licensing
The code in this project is licensed under the Apache License 2.0. For more information, please refer to the [LICENSE file](https://github.com/Stand-In-Language/stand-in-language/blob/master/LICENSE).
