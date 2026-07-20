# 2026 Verification Workshop

Workshop materials for Rocq and CRIS.

## Workshop content

TBA. The lecture content is in development.

## Requirements

- `git`
- `make`
- Bash, `find`, `sed`, and standard build tools
- [opam](https://opam.ocaml.org/doc/Install.html) 2.1 or newer
- GitHub access to `snu-sf/CRIS-private` and
  `snu-sf/2026-verification-workshop`
- [an SSH key configured for GitHub](https://docs.github.com/en/authentication/connecting-to-github-with-ssh)

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

### 2. Install Rocq 9.0 and the CRIS dependencies

```sh
opam repo add rocq-released https://rocq-prover.org/opam/released
opam install \
  coq.9.0.0 \
  coq-paco.4.2.3 \
  coq-itree.5.2.1 \
  coq-ext-lib.0.13.0 \
  coq-ordinal.0.5.6 \
  coq-stdpp.1.12.0 \
  coq-iris.4.4.0
```

The `coq.9.0.0` package provides Rocq 9.0 with the compatibility command names
used by CRIS. Check the active version:

```sh
coqc --version
```

The output should contain `9.0.0`.

### 3. Clone CRIS and the workshop

Keep both repositories under the same parent directory:

```text
verification-workshop/
├── CRIS-private/
└── 2026-verification-workshop/
```

```sh
mkdir verification-workshop
cd verification-workshop

git clone git@github.com:snu-sf/CRIS-private.git
git -C CRIS-private checkout 56a62de13912f282b460e9b806c0fce045e0880c

git clone git@github.com:snu-sf/2026-verification-workshop.git
```

The sibling layout matches the paths in `Makefile` and `_CoqProject`.

### 4. Build CRIS

```sh
eval "$(opam env --switch=cris-workshop --set-switch)"
make -C CRIS-private -j4
```

Use a smaller job count on a machine with limited memory.

### 5. Check the workshop

```sh
cd 2026-verification-workshop
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

### Editor check

Open [`exercises/Exercise00_RocqCheck.v`](exercises/Exercise00_RocqCheck.v) and
process it from the first line to the end.

## Repository layout

| Path | Purpose |
|---|---|
| `exercises/` | Student starter files |
| `checkpoints/` | Intermediate starting points |
| `theories/` | Reference definitions and proofs |
| `lectures/` | TBA |
| `handouts/` | TBA |

## Troubleshooting

Check the active switch and Rocq version:

```sh
eval "$(opam env --switch=cris-workshop --set-switch)"
command -v coqc
coqc --version
```

Rebuild CRIS and the workshop after a load-path or `.vo` error:

```sh
make -C ../CRIS-private -j4
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
- [Iris 4.4.0 Proof Mode documentation](https://gitlab.mpi-sws.org/iris/iris/-/blob/iris-4.4.0/docs/proof_mode.md)
- [Iris Proof Mode paper](https://iris-project.org/pdfs/2017-popl-proofmode-final.pdf)
- [Iris lecture notes](https://iris-project.org/tutorial-material.html)
- [CRIS paper](https://doi.org/10.1145/3808317)
- [Conditional Contextual Refinement](https://sf.snu.ac.kr/ccr/)
