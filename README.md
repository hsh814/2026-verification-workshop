# 2026 Verification Workshop

This repository contains hands-on material for learning operational semantics,
simulation, and module refinement with Rocq and CRIS. It assumes little prior
experience with Rocq or program verification and covers setup and the full
workshop exercise sequence.

The final exercise proves a contextual refinement between these two modules:

```text
source specification: key-value storage, state = Z -> option Z
target implementation: sorted list, state = list (Z * Z)

Beh(SortedListTarget) ⊆ Beh(KVSource)
```

The target is not a heap-linked list. It stores an entire strictly sorted
mathematical list as module-local state. The exercise therefore focuses on a
representation relation and simulation, rather than pointers or ownership.

## 1. Prerequisites

You need the following tools:

- `git`
- `make`
- [opam](https://opam.ocaml.org/doc/Install.html) 2.1 or newer
- [Visual Studio Code](https://code.visualstudio.com/Download)
- a GitHub account with repository access and an
  [SSH key configured for GitHub](https://docs.github.com/en/authentication/connecting-to-github-with-ssh)
- a POSIX shell and standard build tools

The workshop is not tied to a particular Linux distribution. CRIS's build
scripts do, however, use Bash, `make`, `find`, and `sed`. On Windows, use a
Unix-like environment. The supported route is to clone and build inside WSL and
open the folder using
[VS Code's WSL integration](https://code.visualstudio.com/docs/remote/wsl).

Both CRIS and this workshop repository are private. Ask an organizer for GitHub
access before the workshop if either clone command below fails.

The material is pinned to the following versions:

| Component | Version |
|---|---:|
| Rocq/Coq compatibility package | `coq.9.0.0` |
| Paco | `4.2.3` |
| Interaction Trees | `5.2.1` |
| ExtLib | `0.13.0` |
| Ordinal | `0.5.6` |
| stdpp | `1.12.0` |
| Iris | `4.4.0` |
| VsRocq | `2.4.3` |
| CRIS | `56a62de13912f282b460e9b806c0fce045e0880c` |

Some opam packages and executables retain the historical `coq` and `coqc`
names for compatibility with projects from before the Rocq rename.

## 2. Install Rocq 9.0

Create a dedicated opam switch so that the workshop does not interfere with
other Rocq or OCaml projects. The commands below use OCaml 4.14.1.

```sh
opam init
opam update
opam switch create cris-workshop ocaml-base-compiler.4.14.1
eval "$(opam env --switch=cris-workshop --set-switch)"
```

Add the Rocq release repository and install the package versions used to check
the workshop:

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

Activate this switch in every new terminal used for the workshop:

```sh
eval "$(opam env --switch=cris-workshop --set-switch)"
coqc --version
```

The reported version must include `9.0.0`. See the
[Rocq opam instructions](https://rocq-prover.org/docs/using-opam) and the
[Rocq 9.0.0 release page](https://rocq-prover.org/releases/9.0.0) for more
background.

## 3. Install CRIS and the workshop

Clone the repositories under the same parent directory. The workshop
`Makefile` and `_CoqProject` use this sibling layout by default:

```text
verification-workshop/
├── CRIS-private/
└── 2026-verification-workshop/
```

Starting in an empty directory, run:

```sh
mkdir verification-workshop
cd verification-workshop

git clone git@github.com:snu-sf/CRIS-private.git
git -C CRIS-private checkout 56a62de13912f282b460e9b806c0fce045e0880c

git clone git@github.com:snu-sf/2026-verification-workshop.git
```

Build CRIS first. Adjust the explicit job count for your machine if needed.

```sh
eval "$(opam env --switch=cris-workshop --set-switch)"
make -C CRIS-private -j4
```

Then check the complete workshop repository:

```sh
cd 2026-verification-workshop
make check
```

`make check` compiles five reference theories, four student starters, and five
checkpoints. It also rejects `Admitted` or `admit` in every workshop `.v` file.
The `Abort` commands in starters and checkpoints deliberately mark proof holes
for students, so they do not make this setup check fail.

For batch builds, a non-sibling CRIS checkout can be selected explicitly:

```sh
make check CRIS_DIR=/absolute/path/to/CRIS-private
```

The IDE also reads the relative CRIS paths in `_CoqProject`, so retaining the
sibling layout is the simplest option during the workshop.

## 4. Configure VS Code and VsRocq

Use [VsRocq](https://marketplace.visualstudio.com/items?itemName=rocq-prover.vsrocq),
the current official Rocq extension for VS Code. Install its language server in
the same opam switch as Rocq and CRIS:

```sh
eval "$(opam env --switch=cris-workshop --set-switch)"
opam install vsrocq-language-server.2.4.3
code --install-extension rocq-prover.vsrocq
command -v vsrocqtop
```

If `code` is not on `PATH`, use VS Code's
`Shell Command: Install 'code' command in PATH` action or install the extension
and open the workshop folder through the GUI.

Launch VS Code from the workshop root so that it inherits the current switch
and discovers `_CoqProject`:

```sh
cd /path/to/verification-workshop/2026-verification-workshop
eval "$(opam env --switch=cris-workshop --set-switch)"
code .
```

If VS Code was launched from the GUI and cannot find `vsrocqtop`, copy the
output of `command -v vsrocqtop` into the `Vsrocq: Path` (`vsrocq.path`)
setting. This workshop pins the extension and language server to upstream
release 2.4.3. If VS Code installed another extension version, select
**Install Another Version** on the VsRocq extension page and choose 2.4.3. An
opam packaging suffix such as `+1` does not indicate a protocol mismatch. See
the [VsRocq README](https://github.com/rocq-prover/vsrocq) and
[FAQ](https://github.com/rocq-prover/vsrocq/blob/main/docs/FAQ.md) for details.

### IDE smoke test

1. Open [Exercise00_RocqCheck.v](exercises/Exercise00_RocqCheck.v).
2. Process the sentences from the first line and confirm that goals and `Check`
   output appear.
3. Replace the final lemma's `Abort` with `reflexivity. Qed.`.
4. Confirm that VsRocq reaches the end of the file without an error.

This checks that the CRIS build, workshop load paths, and VsRocq all use the
same opam switch.

The pinned CRIS source warns that directly opening
`CRIS-private/theories/lib/ltac2_lib.v` may crash VsCoq 2. That internal file is
already compiled as a dependency and is not used as an editor exercise; do not
open it during the workshop.

## 5. Repository layout

| Path | Purpose |
|---|---|
| [`exercises/`](exercises/README.md) | Starter files that students edit |
| [`checkpoints/`](checkpoints/README.md) | Files for resuming at the next learning objective |
| `theories/` | Complete reference definitions and proofs, with no `Admitted` |
| [`handouts/simulation-cheat-sheet.md`](handouts/simulation-cheat-sheet.md) | Event polarity, simulation direction, and tactic summary |
| [`lectures/day1-outline.md`](lectures/day1-outline.md) | Lecture topics, schedule, and lab plan |

The reference solutions are intentionally available in the same repository. If
you want to solve an exercise without hints, work only in `exercises/` or the
appropriate checkpoint before consulting `theories/`.

## 6. Exercise order

| Order | File | Main idea |
|---:|---|---|
| 0 | [`Exercise00_RocqCheck.v`](exercises/Exercise00_RocqCheck.v) | Installation and IDE check |
| 1 | [`Exercise10_SimulationCases_Start.v`](exercises/Exercise10_SimulationCases_Start.v) | `Ret`/`Tau`, source `Choose`, and simulation direction |
| 2 | [`Exercise20_CompilerPairs_Start.v`](exercises/Exercise20_CompilerPairs_Start.v) | Local scratch state, observable I/O, and an invalid I/O transformation |
| 3 | [`Exercise32_KVSortedList_Start.v`](exercises/Exercise32_KVSortedList_Start.v) | State relation, `get`/`put`, and module refinement |

Fill the proof near each `TODO`, then replace its `Abort` with `Qed`. If you do
not finish before the class moves on, open the corresponding file from
[`checkpoints/`](checkpoints/README.md) and continue with the next concept.

The build targets can also be run separately:

```sh
make solutions
make exercises
make checkpoints
make clean
```

## 7. What the examples prove

### Small simulation cases

[SimulationCases.v](theories/SimulationCases.v) relates `Ret 42` to a target
that takes two `Tau` steps before returning `42`. It also explains a
deterministic target result by choosing a witness for `Choose bool` in the
nondeterministic source.

### Compiler-style program pairs

[CompilerPairs.v](theories/CompilerPairs.v) relates a direct source
calculation to a target that uses `SPut` and `SGet` on a private scratch slot.
The next pair matches the same observable `IO "print" [42]` request on both
sides. A deliberately invalid pair changes `print 42` to `print 43`; it has no
simulation theorem because the observable requests differ.

### Key-value storage refined by a sorted list

- [KVSource.v](theories/KVSource.v) defines the abstract state
  `Z -> option Z`.
- [SortedListTarget.v](theories/SortedListTarget.v) stores a strictly sorted
  `list (Z * Z)` as one module-local value.
- [KVSortedListProof.v](theories/KVSortedListProof.v) defines the relation using
  sortedness and pointwise lookup, proves the `get` and `put` function
  simulations, assembles the module simulation, and derives contextual
  refinement.

Remember that the argument order changes between simulation and refinement:

```text
ISim source target
ctx_refines target source
Beh(target) ⊆ Beh(source)
```

## 8. Troubleshooting

### `coqc --version` is not 9.0.0

The shell is using a different opam switch.

```sh
eval "$(opam env --switch=cris-workshop --set-switch)"
command -v coqc
coqc --version
```

Relaunch VS Code with `code .` from the same terminal.

### `From CRIS ...` fails to import

Check that `CRIS-private` is a sibling of the workshop, that it is at the pinned
commit, and that its `.vo` files were built first:

```sh
git -C ../CRIS-private rev-parse HEAD
make -C ../CRIS-private -j4
make clean
make check
```

### `From Workshop ...` fails to import

Open VS Code at the workshop root so that it discovers `_CoqProject`, then
build the reference theories:

```sh
make solutions
```

### VsRocq does not start

```sh
eval "$(opam env --switch=cris-workshop --set-switch)"
opam install vsrocq-language-server.2.4.3
command -v vsrocqtop
```

Set `vsrocq.path` to the absolute path printed by the last command.

## 9. References

### Rocq and operational semantics

- [A Tour of Rocq](https://rocq-prover.org/docs/tour-of-rocq)
- [Rocq 9.0 Reference Manual](https://rocq-prover.org/doc/V9.0.0/refman/)
- [Software Foundations: Logical Foundations](https://softwarefoundations.cis.upenn.edu/lf-current/index.html)
- [Software Foundations: Small-step Semantics](https://softwarefoundations.cis.upenn.edu/plf-current/Smallstep.html)
- [Software Foundations: Program Equivalence](https://softwarefoundations.cis.upenn.edu/plf-current/Equiv.html)

### Interaction Trees

- [Interaction Trees project and documentation](https://deepspec.github.io/InteractionTrees/)
- [Interaction Trees: Representing Recursive and Impure Programs in Coq](https://doi.org/10.1145/3371119)
- [Reasoning about Interactive Programs lecture notes](https://www.cs.uoregon.edu/research/summerschool/summer24/lectures/Zdancewic_Slides/index.html)

The interactive-programs lecture notes use an older Coq release. Use them for
the concepts and examples, not for this workshop's installation commands.

### Iris Proof Mode

These are lookup resources for the `iIntros`, `iDestruct`, `iSplit`, `iExists`,
and `iPureIntro` tactics used by CRIS proofs. The full Iris theory is not a
prerequisite for day one.

- [Iris 4.4.0 Proof Mode documentation](https://gitlab.mpi-sws.org/iris/iris/-/blob/iris-4.4.0/docs/proof_mode.md)
- [Interactive Proofs in Higher-Order Concurrent Separation Logic](https://iris-project.org/pdfs/2017-popl-proofmode-final.pdf)
- [Iris lecture notes and tutorial material](https://iris-project.org/tutorial-material.html)

### CRIS and contextual refinement

- [CRIS: The Power of Imagination in Hybrid Verification](https://doi.org/10.1145/3808317)
- [CRIS PLDI 2026 paper page](https://pldi26.sigplan.org/details/pldi-2026-papers/74/CRiS-The-Power-of-Imagination-in-Hybrid-Verification)
- [Conditional Contextual Refinement project](https://sf.snu.ac.kr/ccr/)
- [CRIS artifact](https://doi.org/10.5281/zenodo.19491861)
- [refinement-tutorial](https://github.com/dongjaelee1/refinement-tutorial)

See [lectures/day1-outline.md](lectures/day1-outline.md) for the complete day-one
schedule and scope.
