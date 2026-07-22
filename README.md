# 2026 Verification Workshop

Workshop materials for Rocq and CRIS.

## Workshop content

TBA. The lecture content is in development.

The repository contains one guided lecture file and two exercise files:

- `Behavior.v` introduces behaviors with small executable examples.
- `Optimizations.v` proves stateless constant folding and stateful
  store-to-load forwarding.
- `KVSortedList.v` proves that a sorted-list implementation refines an
  abstract key-value store. Its `get` operation traverses the list one cell at
  a time with `ITree.iter`.

## Requirements

- `git`
- `make`
- standard Unix tools such as `find` and `grep`
- [opam](https://opam.ocaml.org/doc/Install.html) 2.1 or newer

Linux and macOS can use the commands below directly. Windows users should run
the build inside WSL.

## Install

### 1. Create an opam switch

```sh
opam init
opam update
opam switch create cris-workshop ocaml-base-compiler.4.14.1
eval "$(opam env --switch=cris-workshop --set-switch)"
```

Activate the switch again after opening a new terminal:

```sh
eval "$(opam env --switch=cris-workshop --set-switch)"
```

### 2. Install CRIS v2026-07-22

```sh
opam repo add rocq-released https://rocq-prover.org/opam/released
opam pin add -y --jobs=N rocq-cris \
  'git+https://github.com/snu-sf/CRIS.git#v2026-07-22'
```

This installs the [CRIS v2026-07-22 release](https://github.com/snu-sf/CRIS/releases/tag/v2026-07-22),
Rocq 9.0.0, and the exact CRIS dependencies. Check the active installation:

```sh
opam list --installed rocq-cris
opam pin list | grep '^rocq-cris'
coqc --version
```

The final command should report version `9.0.0`.

### 3. Clone the workshop

```sh
git clone https://github.com/snu-sf/2026-verification-workshop.git
cd 2026-verification-workshop
```

### 4. Check the workshop

```sh
make check
```

A successful setup finishes with exit code 0.

## Editor setup

Launch the editor from a terminal where `cris-workshop` is active. Open the
workshop repository root so the editor can find `_CoqProject`.

### VS Code

Use [VsRocq](https://marketplace.visualstudio.com/items?itemName=rocq-prover.vsrocq).

```sh
opam install vsrocq-language-server.2.4.3
code --install-extension rocq-prover.vsrocq
command -v vsrocqtop
code .
```

Set `vsrocq.path` to the path printed by `command -v vsrocqtop` when VS Code
cannot locate the language server.

### Vim or Neovim

Use [Coqtail](https://github.com/whonore/Coqtail#installation). It requires Vim
with `+python3` or Neovim with `pynvim`, plus `coqidetop` on `PATH`.

### Emacs

Use the current [Proof General](https://github.com/ProofGeneral/PG#installing-proof-general)
package. Install it through NonGNU ELPA or MELPA, then start Emacs from the
active opam switch.

### Unicode input

CRIS source files use Unicode mathematical notation.

- **VS Code:** install
  [latex-input](https://marketplace.visualstudio.com/items?itemName=yellpika.latex-input),
  type a LaTeX-style name such as `\Sigma`, and accept the completion to insert
  `Σ`.
- **Vim/Neovim:** in Insert mode, `Ctrl-V u03a3` inserts `Σ`. See
  [Coqtail's Unicode input note](https://github.com/whonore/Coqtail#unicode-input)
  for native key sequences and optional plugins.
- **Emacs:** select the built-in `TeX` input method with
  `M-x set-input-method RET TeX RET`, type `\Sigma`, and use `C-\` to toggle the
  input method. See the GNU Emacs documentation on
  [input methods](https://www.gnu.org/software/emacs/manual/html_node/emacs/Select-Input-Method.html)
  and [`insert-char`](https://www.gnu.org/software/emacs/manual/html_node/emacs/Inserting-Text.html).

### Editor check

Open [`Behavior.v`](Behavior.v) and process it from the first line to
the end.

## Repository layout

| Path | Purpose |
|---|---|
| `Behavior.v` | Guided examples of terminating, nondeterministic, and I/O behaviors |
| `Optimizations.v` | Stateless and stateful compiler-optimization refinements |
| `KVSortedList.v` | Sorted-list implementation versus abstract key-value storage |

## Troubleshooting

Check the active switch and Rocq version:

```sh
eval "$(opam env --switch=cris-workshop --set-switch)"
command -v coqc
coqc --version
```

Reinstall CRIS and rebuild the workshop after a load-path or `.vo` error:

```sh
opam reinstall --jobs=N rocq-cris
make clean
make check
```

The [VsRocq FAQ](https://github.com/rocq-prover/vsrocq/blob/main/docs/FAQ.md),
[Coqtail documentation](https://github.com/whonore/Coqtail), and
[Proof General manual](https://proofgeneral.github.io/doc/master/userman/)
cover editor-specific problems.

## References

- [Rocq opam installation](https://rocq-prover.org/docs/using-opam)
- [Rocq 9.0 Reference Manual](https://rocq-prover.org/doc/V9.0.0/refman/)
- [A Tour of Rocq](https://rocq-prover.org/docs/tour-of-rocq)
- [Software Foundations](https://softwarefoundations.cis.upenn.edu/lf-current/index.html)
- [Interaction Trees project](https://deepspec.github.io/InteractionTrees/)
- [Interaction Trees paper](https://doi.org/10.1145/3371119)
- [Refinement Tutorial](https://github.com/dongjaelee1/refinement-tutorial)
- [Iris 4.4.0 Proof Mode documentation](https://gitlab.mpi-sws.org/iris/iris/-/blob/iris-4.4.0/docs/proof_mode.md)
- [Iris Proof Mode paper](https://iris-project.org/pdfs/2017-popl-proofmode-final.pdf)
- [Iris lecture notes](https://iris-project.org/tutorial-material.html)
- [CRIS paper](https://doi.org/10.1145/3808317)
- [Conditional Contextual Refinement](https://sf.snu.ac.kr/ccr/)
