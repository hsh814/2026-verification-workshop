---
marp: true
theme: default
paginate: true
size: 16:9
title: From Behaviors to Contextual Refinement
description: Program Verification Workshop 2026 — Day 1
footer: 2026 Verification Workshop · Day 1
style: |
  section {
    font-family: "Noto Sans", "DejaVu Sans", sans-serif;
    font-size: 28px;
    padding: 48px 64px;
  }
  section.lead {
    text-align: center;
  }
  section.section {
    background: #17324d;
    color: #ffffff;
  }
  section.section h1,
  section.section h2 {
    color: #ffffff;
  }
  section.section footer,
  section.section::after {
    color: rgba(255, 255, 255, 0.72);
  }
  h1 {
    color: #17324d;
    font-size: 42px;
  }
  h2 {
    color: #245b78;
  }
  code {
    font-size: 0.88em;
  }
  pre code {
    font-size: 0.72em;
    line-height: 1.28;
  }
  table {
    font-size: 0.78em;
  }
  blockquote {
    border-left: 6px solid #2f80a8;
    color: #17324d;
    font-size: 1.05em;
  }
  .file {
    color: #2f80a8;
    font-weight: 700;
    letter-spacing: 0.03em;
  }
  .flow {
    color: #17324d;
    font-size: 1.15em;
    font-weight: 650;
    text-align: center;
  }
  .stop {
    background: #fff2cc;
    border: 2px solid #d6a800;
    border-radius: 12px;
    padding: 14px 20px;
  }
  .demo {
    background: #e8f4fa;
    border: 2px solid #2f80a8;
    border-radius: 12px;
    padding: 14px 20px;
  }
  section.diagram pre code {
    font-size: 0.68em;
    line-height: 1.12;
  }
---

<!-- _class: lead -->

# From Behaviors to Contextual Refinement

Program Verification Workshop 2026

Day 1 · CRIS fundamentals and guided proofs

<!--
Prompt: Welcome the class and open day1/lectures/Behavior.v. State one goal: follow a target module all the way to its observable behaviors.
Action: Ask everyone to process one Rocq sentence at a time.
-->

---

<span class="file">day1/lectures/Behavior.v</span>

# What can this program do?

```coq
Check Beh.of_itree.
(* itree coreE Any.t -> Tr.t -> Prop *)
```

`Beh.of_itree program trace` says that `trace` is one behavior of
`program`.

> Read it as trace membership.

<!--
Prompt: Keep the program fixed and ask whether one proposed trace belongs to its behavior set.
Action: Process Print Beh.t and Check Beh.of_itree.
-->

---

# Return produces a terminating trace

```coq
Definition return_42 : itree coreE Any.t :=
  Ret (42%Z)↑.

Check ((42%Z)↑ : Any.t).
Check (Tr.done (42%Z)↑).
Check (Beh.of_itree return_42 (Tr.done (42%Z)↑)).
```

```text
Ret 42  ─────────▶  done 42
```

`Any.t` stores the whole-program return value. The notation `x↑` injects a
typed value into `Any.t`.

<!--
Prompt: The interaction tree has finished. Its return value appears in the trace. Point out the common Any.t value on both sides.
Action: Process the three Check commands and return_42_terminates. Treat the proof as certification of the example.
-->

---

# Tau preserves the observation

```coq
Definition silent_return_42 : itree coreE Any.t :=
  tau;; return_42.
```

```text
tau; Ret 42  ─────▶  done 42
     Ret 42  ─────▶  done 42
```

`Tau` is an internal computation step.

<!--
Prompt: Ask which part of the tree changed and which part of the trace changed.
Action: Process silent_return_42_terminates and point to Beh.sb_tau.
-->

---

# Choose gives several behaviors

```coq
Definition choose_bit : itree coreE Any.t :=
  'b : bool <- trigger (Choose bool);;
  Ret ((if b then 1%Z else 0%Z)↑).
```

```text
choose_bit ─────▶ done 0
choose_bit ─────▶ done 1
```

One program supports both membership propositions.

<!--
Prompt: Keep choose_bit fixed. Vary only the proposed trace.
Action: Process the two lemmas and identify the existential witness in Beh.sb_choose.
-->

---

# I/O extends the trace

```coq
Definition echo_once : itree coreE Any.t :=
  'answer : Z <- trigger (@IO Z Z "echo" 7%Z);;
  Ret answer↑.
```

```text
request echo(7)
  ├─ response 9 ─▶ interact echo(7 ↦ 9); done 9
  └─ unanswered ─▶ hang echo(7)
```

<!--
Prompt: An I/O request exposes an observable boundary. A response selects the continuation.
Action: Process echo_once_reply_9 and echo_once_may_hang.
-->

---

# Trace shapes

```coq
Print Tr.t.
Check Tr.spin.
```

```text
done(ret)     abort       spin
hang(request)             interact(io, rest)
```

- `spin`: infinitely many internal steps
- `interact`: one observable I/O followed by the remaining trace
- an infinite I/O behavior: an infinite chain of `interact`

<!--
Prompt: Give the class names for finite termination, silent divergence, unanswered I/O, and continuing I/O.
Action: Process Print Tr.t and Check Tr.spin. Keep coinduction internals outside today's proof exercises.
-->

---

<!-- _class: section -->

# Where does the closed interaction tree come from?

```text
program construction
              │
              │
              ▼
?  : itree coreE Any.t
              │
              ▼
         Beh.of_itree
```

`Behavior.v` started at the final observation interface.

<!--
Prompt: We can observe the behavior of a coreE tree. Ask what program structure has already disappeared by the time we reach this type.
Handoff: Stay in day1/lectures/Behavior.v. The next slide inspects its final Print coreE command.
-->

---

<span class="file">day1/lectures/Behavior.v · final recap</span>

# `coreE` is the residual whole-program signature

```coq
Print coreE.
```

```text
coreE = Choose | Take | IO
```

After module compilation:

- named function calls have been resolved;
- module-local state operations have been interpreted;
- the client/service boundary has been erased.

Residual effects: `Choose`/`Take` branch; `IO` records observable interaction.

<!--
Action: Process Print coreE and read the transition comment that follows it.
Prompt: Point to the absence of Call, SGet, and SPut in Print coreE. Compilation has handled those module-internal effects.
Prompt: Choose and Take affect the behavior set through branching. External I/O becomes part of a trace.
-->

---

<span class="file">day1/lectures/Behavior.v → ModuleIntro.v</span>

# Why build the program from modules?

## Modular programming and verification

- Modules preserve named component boundaries during implementation and proofs.
- A client can link against a refined service implementation.

## State interpretation

- Each `SMod.t` supplies an initial local state.
- Compilation interprets `SGet` and `SPut` over the combined module state.

<!--
Prompt: A behavior describes the whole closed program. Program construction still needs component boundaries and state ownership.
Prompt: The first boundary supports separate implementation and contextual replacement. The second gives SGet and SPut their state semantics.
Handoff: crisE is the event signature used while both structures are still present.
-->

---

<span class="file">day1/lectures/ModuleIntro.v</span>

# Two modules, one linked program

```text
module ConstService { get() = 42 }
module Main         { main() = ConstService.get() }
```

Define the two modules separately, then link them:

```text
ConstModule ──┐
              ├── ★ ──▶ whole program ──▶ behavior
MainModule ───┘
```

<!--
Prompt: Start from the ordinary module-level program. The service and client can be implemented independently because they share a named boundary.
Action: Open day1/lectures/ModuleIntro.v, read its opening comment, and continue to ConstHdr.
-->

---

# A header names a typed boundary

```coq
Module ConstHdr.
  Definition get :=
    fnsig (fn "get") (fntyp () Z).
End ConstHdr.
```

```text
get : unit → Z
```

Callers and implementations share this signature.

`Module ConstHdr` is a Rocq namespace. `ConstHdr.get` is a concrete CRIS
function signature stored inside that namespace.
`mn +:+ "." +:+ method` builds its qualified string name.

<!--
Prompt: Separate Rocq's namespace mechanism from the semantic modules constructed later. The header gives the boundary a stable name, argument type, and return type.
Action: Process Check ConstHdr.get.
-->

---

# Ordinary return, interaction-tree return

Ordinary code:

```text
get() = return 42
```

CRIS function body:

```coq
Definition get : () -> itree crisE Z :=
  fun _ => Ret 42%Z.

Check get.
```

`Ret` constructs an interaction tree that returns immediately.

<!--
Prompt: Relate ordinary return to Ret. Ret is an itree constructor; the body performs no event before returning.
Action: Process ConstModule through Check get, then pause.
-->

---

<span class="file">day1/lectures/ModuleIntro.v</span>

# Inspect the function-body event signature

```coq
Print crisE.
Check Call.
Check SGet.
Check SPut.
```

```text
crisE = agE +' callE +' pgE +' coreE
                    │       │
                   Call   SGet / SPut
```

Relevant constructors today are `Call`, `SGet`, and `SPut`.

```coq
get : () -> itree crisE Z
```

<!--
Prompt: We encountered crisE in the concrete type of get. Inspect it now. Call names another body; SGet and SPut refer to module-local state.
Action: Process Print crisE and the three Check commands.
-->

---

# Package the service

```coq
Program Definition smod : SMod.t := {|
  SMod.scopes := scopes;
  SMod.fnsems := fnsems;
  SMod.initial_st := ∅;
|}.

Definition t : Mod.t := SMod.to_mod ∅ smod.
```

```text
module = named function bodies + private initial state + scope
```

This first service uses empty local state.

`smod : SMod.t` is a semantic module value. `SMod.to_mod` turns it into the
`Mod.t` value consumed by linking.

<!--
Prompt: fnsems registers get under ConstHdr.get. SMod packages the body map, scope, and initial state; SMod.to_mod makes the resulting value linkable.
Action: Finish the ConstModule definitions.
-->

---

# Ordinary call, named CRIS call

Ordinary code:

```text
main() = ConstService.get()
```

CRIS function body:

```coq
Definition main : Any.t -> itree crisE Any.t :=
  fun _ =>
    n <- ccallU ConstHdr.get tt;;
    Ret n↑.
```

`ccallU ConstHdr.get tt` emits a named `Call` event.

<!--
Prompt: The header fixes the call's argument and result types. The caller refers to the service by name; linking will supply its body.
Action: Process MainModule from Check ccallU through Check t.
-->

---

<!-- _class: diagram -->
<!-- _footer: "" -->
<!-- _paginate: false -->

# From function fragments to a linked module

```text
MainModule.main                         ConstModule.get
Any.t -> itree crisE Any.t              () -> itree crisE Z
        │ package code, state, scope            │
        ▼                                       ▼
MainModule.smod : SMod.t              ConstModule.smod : SMod.t
        │ SMod.to_mod ∅                         │ SMod.to_mod ∅
        ▼                                       ▼
MainModule.t : Mod.t                    ConstModule.t : Mod.t
        └──────────────────┬────────────────────┘
                           │  ★
                           ▼
                    modules : Mod.t
```

<!--
Prompt: Every node above the star is now a concrete object from ModuleIntro.v. The star combines both function maps and initial states.
Handoff: Define the linked program represented by the bottom node.
-->

---

# Link, compile, observe

```coq
Definition modules : Mod.t :=
  MainModule.t ★ ConstModule.t.

Definition linked : LMod.t :=
  Mod.to_lmod modules ε.

Definition program : itree coreE Any.t :=
  LMod.compile linked tt↑.

Check (Beh.of_itree program).
```

<!--
Prompt: Linking supplies the function map. Compilation interprets calls and threads local state. Beh.of_itree program is the behavior set from the first file.
Action: Process LinkedProgram from top to bottom.
-->

---

<!-- _class: diagram -->

# From the linked module to behaviors

```text
                  modules : Mod.t
                         │ Mod.to_lmod modules ε
                         ▼
                    linked : LMod.t
                         │ LMod.compile linked tt↑
                         ▼
            program : itree coreE Any.t
                         │ Beh.of_itree
                         ▼
            Beh.of_itree program : Tr.t -> Prop
```

- `Mod.to_lmod` turns `SGet` and `SPut` into operations on linked state.
- `LMod.compile` resolves named calls and interprets that state, leaving `coreE`.

<!--
Prompt: Recap the concrete definitions just processed. Mod.to_lmod translates each crisE body to lmodE; named calls remain. LMod.compile resolves those calls and interprets linked state.
Handoff: The linked program contains a client module and a service module. Ask whether the same team must own both.
-->

---

<span class="file">ModuleIntro.v → RefinementIntro.v · motivation</span>

# Linked modules may have different owners

```text
APPLICATION TEAM                         LIBRARY TEAM

Client                                   Cell library
  calls Cell.set / Cell.get                publishes API + contract
  proves an output property                owns code + private state

                    ╲                    ╱
                     ╲   deployment     ╱
                          Client ★ Cell
```

A module boundary can also be an ownership boundary.

<!--
Prompt: We just linked MainModule and ConstModule. Ordinary projects often assign the client and library to different teams.
Prompt: Name each responsibility before introducing any refinement terminology.
Action: Read the final transition comment in ModuleIntro.v one paragraph at a time across the next five slides.
-->

---

# A Cell has public behavior and private code

```text
PUBLIC API + CONTRACT
set : Z -> unit
get : unit -> Z

set(v) updates the logical cell to v.
With no intervening set, a following get() returns v.

────────────────────────────────────────────────────────────

ONE PRIVATE IMPLEMENTATION
state current := 0

set(v):  current := v
get():   return current
```

The application team receives the public contract.
The library team owns the private implementation.

<!--
Prompt: Read the API types first, then the contract in ordinary language. The logical cell is the abstract state described by the contract.
Prompt: The code below the divider is one implementation of that contract. Its field current belongs to the provider.
Prompt: CellSpec and CellImpl are conceptual names in this motivation; the workshop has not defined Rocq identifiers with those names.
-->

---

# The client proof uses the contract

```text
Client code                         Proof from CellSpec

Cell.set(42)                        set(42)
x <- Cell.get()                         │ contract
output(x)                               ▼
                                   get() returns 42
                                        │
                                        ▼
                                   output(42)
```

The proof mentions `set`, `get`, their specified results, and observable I/O.

<!--
Prompt: Derive the output property using only the public contract. The proof never opens the private field current.
Prompt: This is the proof the application team wants to retain across library releases.
-->

---

# The provider may change private code

```text
RELEASE 1                             RELEASE 2

set(v):                              set(v):
  current := v                         if current != v:
                                         current := v

get():                               get():
  return current                       return current
```

Each release must satisfy the same public Cell contract.
The client code and its output proof stay unchanged.

<!--
Prompt: Read release 2 as a small implementation optimization. Future releases may also change the algorithm, cache, or state representation.
Prompt: The provider now owes a proof that each release respects the published contract.
Handoff: Ask for the theorem that validates a release for present and future clients.
-->

---

# Preserve the client proof across releases

The application proof was derived from `CellSpec`.
Every new `CellImpl` release must stay within that contract:

```text
new CellImpl behavior
          │
          │ must already be permitted by
          ▼
      CellSpec behavior
          │
          │ supports the existing proof of
          ▼
      Client's output property
```

A release with an extra observable behavior could invalidate the client proof.
The provider must rule out such a behavior in every client context.

<!--
Prompt: Follow the dependency from bottom to top. The client proof remains valid when every behavior of the new implementation is already covered by CellSpec.
Prompt: A context can call set and get in arbitrary ways and observe their results. The provider theorem must therefore cover every compatible context.
Handoff: Express “no extra observable behavior in any context” as behavior inclusion.
-->

---

# One theorem validates every future client

The provider publishes the implementation before seeing every future client.
The replacement theorem therefore quantifies over a client context:

```text
for every compatible Ctx,
  Beh(CellImpl ★ Ctx) ⊆ Beh(CellSpec ★ Ctx)
```

Every deployed implementation trace is permitted by the published contract.
This all-client replacement theorem is **contextual refinement**.

Open `day1/lectures/RefinementIntro.v`.

<!--
Prompt: CellSpec packages the public contract as a module. CellImpl is the provider's deployed code. Ctx contains a client and any supporting modules.
Prompt: The displayed inclusion is the schematic behavioral reading. RefinementIntro.v will state the exact ctx_refines proposition, demonstrate replacement inside a linked module, and then follow adequacy down to refines_lmod.
Prompt: This is the substitutability reading of contextual refinement. One provider theorem covers every compatible present or future client.
Prompt: Fix the direction with the concrete names: CellSpec permits behaviors; CellImpl stays inside that set after linking with every compatible context.
Handoff: Open day1/lectures/RefinementIntro.v.
-->

---

<span class="file">day1/lectures/RefinementIntro.v</span>

# The provider's contextual-refinement theorem

The implementation, specifications, and client remain abstract `Mod.t` values:

```coq
Variables (CellImpl CellSpec Client ClientSpec : Mod.t).

Check (⊢ ctx_refines CellImpl CellSpec).
```

The library provider proves:

```text
⊢ ctx_refines CellImpl CellSpec
```

`CellImpl` is the deployed target. `CellSpec` is the published source.

<!--
Prompt: Keep the concrete Cell names from the previous slide. This is the exact proposition corresponding to the all-client theorem stated in ordinary language.
Prompt: RefinementIntro.v leaves all four modules abstract. We study the theorem's statement and how a client proof uses it.
Action: Open RefinementIntro.v and process through the first Check.
-->

---

# Specialize the theorem to one client

```coq
Lemma cell_in_one_context :
  ctx_refines CellImpl CellSpec ⊢
  refines (CellImpl ★ Client) (CellSpec ★ Client).
```

```text
deployed program                         proof model

CellImpl ★ Client  ───── refines ─────▶  CellSpec ★ Client
```

```coq
iIntros "CELL_REF".
iSpecialize ("CELL_REF" $! Client).
iExact "CELL_REF".
```

Both sides use the same `Client` module definition. They are separate
executions with separate runtime states.

<!--
Prompt: CELL_REF contains the promised “for every context.” iSpecialize chooses this Client. Read the resulting refines statement before processing the three proof commands.
Action: Process cell_in_one_context.
-->

---

# The client team proves against `CellSpec`

`ClientSpec` describes the externally visible behavior of the application.

```coq
Check (⊢ ctx_refines
  (CellSpec ★ Client)
  (CellSpec ★ ClientSpec)).
```

```text
CellSpec ★ Client ──client proof──▶ CellSpec ★ ClientSpec
    unchanged contract                         abstraction
```

<!--
Prompt: ClientSpec can state that the application outputs 42, without exposing the Client implementation. CellSpec remains the unchanged library contract on both sides.
-->

---

# The replacement remains open for linking

```coq
ctx_refines CellImpl CellSpec ⊢
  ctx_refines (CellImpl ★ Client) (CellSpec ★ Client)
```

```text
TARGET                               SOURCE
CellImpl ★ Client ─refinement proof─▶ CellSpec ★ Client
   replacement                       contract + same Client
```

Deployment uses `CellImpl`; the proof carries its traces back to `CellSpec`.

<!--
Prompt: This conclusion remains contextual: another module may still be linked later. Point to the single component that changes and the Client component that remains available.
Handoff: Show the corresponding replacement lemma.
-->

---

# The modular replacement proof

```coq
Lemma replace_cell_in_client :
  ctx_refines CellImpl CellSpec ⊢
  ctx_refines (CellImpl ★ Client) (CellSpec ★ Client).
Proof.
  iIntros "CELL_REF".
  jStartProof (ctx_refines_BiProset).
  jIntros "(IMPL & CLIENT)".
  jPoseProof "CELL_REF" with "IMPL" as "SPEC".
  jFrame.
Qed.
```

<!--
Prompt: Treat the script as a completed proof. Keep attention on the theorem statement: the Cell component changes and Client remains linked.
-->

---

# Compose the provider and client proofs

```coq
ctx_refines CellImpl CellSpec ∗
  ctx_refines (CellSpec ★ Client) (CellSpec ★ ClientSpec) ⊢
ctx_refines (CellImpl ★ Client) (CellSpec ★ ClientSpec)
```

```text
CellImpl ★ Client ──replacement──▶ CellSpec ★ Client
                                           │ client proof
                                           ▼
                                  CellSpec ★ ClientSpec
```

```text
first edge, Ctx := ⌽  : refines (CellImpl ★ Client)
                               (CellSpec ★ Client)
composed,   Ctx := ⌽  : refines (CellImpl ★ Client)
                               (CellSpec ★ ClientSpec)
```

<!--
Prompt: Read the two team proofs as adjacent refinement edges. ctxr_trans composes them. The empty context turns either open edge into a concrete refines assertion.
Action: Process deploy_client_abstraction, then Print ctx_refines.
-->

---

<!-- _class: diagram -->

# Adequacy closes this concrete pair

```text
Mt := CellImpl ★ Client       Ms := CellSpec ★ ClientSpec

refines Mt Ms
        │ refines_adequacy
        │ requires Mod.wf Mt + initial world invariant
        ▼
∃ rs, ✓ rs ∧
  refines_lmod (Mod.to_lmod Mt ε) (Mod.to_lmod Ms rs)
        │ definition
        ▼
Beh.of_itree (compile (Mod.to_lmod Mt ε))
        ⊆
Beh.of_itree (compile (Mod.to_lmod Ms rs))
```

<!--
Prompt: Keep Mt and Ms concrete throughout. refines_adequacy closes their module-local resources. The resulting refines_lmod unfolds directly to compiled-program behavior inclusion.
Action: Process Check Beh, Print refines, Check refines_adequacy, Check refines_lmod, and Print refines_lmod.
-->

---

# The result is behavior inclusion

```text
trace ∈ Beh(compile (Mod.to_lmod Mt ε))
          │ refines_lmod
          ▼
trace ∈ Beh(compile (Mod.to_lmod Ms rs))
```

```coq
Lemma refinement_means_behavior_inclusion
    (Target Source : LMod.t) (trace : Tr.t) :
  refines_lmod Target Source ->
  Beh.of_itree (LMod.compile Target tt↑) trace ->
  Beh.of_itree (LMod.compile Source tt↑) trace.
```

**Every behavior produced by the target layer is permitted by the source
layer.**

<!--
Prompt: The composed theorem has reached its semantic bottom layer. Transport one trace from the deployed Cell-plus-Client program to CellSpec-plus-ClientSpec. The same argument applied to the first edge transports it to CellSpec-plus-Client.
Action: Process refinement_means_behavior_inclusion.
-->

---

# Why this is program verification

Suppose every source behavior satisfies `P`.

```text
trace ∈ Beh(Target)
          │ refinement
          ▼
trace ∈ Beh(Source)
          │ SOURCE_OK
          ▼
        P trace
```

Examples of `P`: output safety, a return-value postcondition, or protocol
compliance.

<!--
Prompt: Return to the Cell client once more. CELL_REF supplies the first arrow; the application team's proof supplies the second.
Prompt: Universal properties over CRIS behaviors transfer along this inclusion.
-->

---

# Rocq makes property transfer explicit

```coq
Lemma refinement_transfers_universal_properties
    (Target Source : LMod.t) (P : Tr.t -> Prop)
    (REFINE : refines_lmod Target Source)
    (SOURCE_OK : forall trace,
       Beh.of_itree (LMod.compile Source tt↑) trace ->
       P trace) :
  forall trace,
    Beh.of_itree (LMod.compile Target tt↑) trace ->
    P trace.
Proof.
  intros trace TARGET_BEHAVIOR.
  apply SOURCE_OK.
  apply REFINE.
  exact TARGET_BEHAVIOR.
Qed.
```

<!--
Prompt: Read the proof as function composition: TARGET_BEHAVIOR, then REFINE, then SOURCE_OK.
Action: Process refinement_transfers_universal_properties one tactic at a time.
-->

---

# The next goal is contextual refinement

For a source module and its replacement target, we want:

```coq
⊢ ctx_refines Target Source
```

Unfolding the outer definition exposes the quantification:

```text
for every compatible Ctx,
  Beh(Target ★ Ctx) ⊆ Beh(Source ★ Ctx)
```

We need a reusable proof technique for this all-context behavior claim.

<!--
Prompt: Separate the semantic goal from its proof technique. Contextual refinement is still the theorem we want.
Prompt: A single proof must cover future contexts, including contexts that perform I/O, diverge, and call back into the module.
Handoff: Ask what a direct proof over complete linked behaviors would have to inspect.
-->

---

<!-- _class: diagram -->

# Whole-execution reasoning scales poorly

```text
choose an arbitrary Ctx
          │
          ▼
choose a trace of Target ★ Ctx
          │
          ▼
analyze the complete linked execution
          │
          ▼
construct the same trace for Source ★ Ctx
```

Changing `Ctx` changes the execution tree. Calls may re-enter the module, and
the trace may be finite, blocked on I/O, or infinite.

The local reason that the two modules correspond is buried inside this global
argument.

<!--
Prompt: Follow the quantifiers in ctx_refines. A direct proof starts over for each arbitrary context behavior.
Prompt: The implementation change is usually local: an extra load disappears, a representation changes, or a loop is reorganized.
Handoff: Keep that local correspondence as an invariant while executions unfold.
-->

---

<!-- _class: diagram -->

# Simulation is the local proof technique

A simulation relates pairs of execution configurations.

```text
SOURCE CONFIGURATION          R          TARGET CONFIGURATION

        ⟨S₀⟩ ─────────────────────────────── ⟨T₀⟩
          │ matching source steps              │ one target step
          ▼                                    ▼
        ⟨S₁⟩ ─────────────────────────────── ⟨T₁⟩
                              R
```

The proof follows the programs one step at a time and re-establishes `R`.

<!--
Prompt: A configuration records the remaining computation and current module-local state.
Prompt: The target generates the behavior that must be included. Each target move therefore receives a matching source move.
Prompt: The source may use more internal steps, as in a removed load or an arithmetic simplification.
-->

---

<!-- _class: diagram -->

# The simulation rule preserves observations

```text
RELATED CONFIGURATIONS
        │
        ├─ internal step ─▶ match with internal source steps
        │
        ├─ I/O event ─────▶ expose the same request and shared response
        │
        ├─ Call f(x) ─────▶ match the same function name and argument
        │
        └─ Return v ──────▶ return the same value
                              │
                              ▼
                    RELATED CONTINUATIONS
```

Each rule matches the currently visible interaction and supplies the relation
needed to continue.

<!--
Prompt: Read the cases as the interface of the simulation proof. Silent implementation work may differ; observations and control transfers line up.
Prompt: The workshop tactics select these cases and leave the relation-restoration obligations as Rocq goals.
-->

---

<!-- _class: diagram -->

# Repeated matching produces a source behavior

```text
TARGET EXECUTION             SOURCE EXECUTION

configuration T₀     R      configuration S₀
      │ target step              │ matching steps
      ▼                          ▼
configuration T₁     R      configuration S₁
      │                          │
      ▼                          ▼
             same observable trace
```

Finite executions finish with matching returns or I/O boundaries.
Infinite executions continue the rule coinductively.

CRIS packages this soundness argument as:

```coq
ISim.t open Source Target emp Ist -> ⊢ ctx_refines Target Source
```

<!--
Prompt: The relation lets us extend a matching source prefix whenever the target execution extends.
Prompt: main_adequacy links the same context to both sides and turns the open simulation into contextual refinement.
Action: Process Check ISim.t and simulation_is_enough in RefinementIntro.v.
-->

---

<!-- _class: diagram -->

# Modules create control boundaries

```text
known module code
      │ local SGet / SPut / computation
      ▼
Call touch() ───────────────────────────▶ unknown Ctx
                                             │ I/O, choices,
                                             │ re-entrant calls
continuation ◀────────────────────────── return value
      │
      ▼
known module code
```

The simulation proof handles execution while the module has control.
The linking context handles execution between an unknown call and its return.

A simulation relation must support both transfers of control.

<!--
Prompt: Local proof rules can inspect the module bodies. The proof has no body for a context-provided touch function.
Prompt: At the call boundary the simulation proof must establish enough state information for execution by an arbitrary context and its possible re-entry.
-->

---

<!-- _class: diagram -->

# Simulation needs a relation on local states

```text
SOURCE CONFIGURATION                  TARGET CONFIGURATION

⟨source state, source code⟩    R    ⟨target state, target code⟩
```

The remaining computations determine which facts the relation must retain.

```text
before local steps       enough information to match the next steps
before unknown Call      enough information to transfer control
after Call               enough information to resume both continuations
at return                related final states
```

Source and target states may use different representations.

<!--
Prompt: R is chosen for the pair of programs under proof. It records exactly the state facts needed by future simulation rules.
Prompt: State equality is one possible relation. Representation-changing refinement usually needs a different relation.
Handoff: Introduce the CRIS parameter that carries this relation.
-->

---

<!-- _class: diagram -->

# CRIS names the state relation `Ist`

The exact type is:

```coq
ist_type Σ :=
  gmap key (option Any.t) ->
  gmap key (option Any.t) ->
  iProp Σ
```

```text
Ist source_state target_state
```

`Ist` may express `True`, equality of selected state entries, or a
representation invariant.

<!--
Prompt: Read Ist as a binary relation on the two module-local state maps. Its result is an Iris proposition because the relation may own logical resources.
Prompt: Keep the examples schematic here. Concrete definitions first appear with the Rocq programs that use them.
Action: Process Check (ist_type Σ) in RefinementIntro.v.
-->

---

<!-- _class: diagram -->

# `Ist` is the control-boundary contract

```text
function entry        before unknown Call       after Call          return

   rely on Ist  ─local steps─▶ guarantee Ist ─Ctx─▶ rely on Ist ─steps─▶
                                                                        │
                                                                        ▼
                                                     equal result ∧ guarantee Ist
```

- Known function code may assume `Ist` when it receives control.
- Before releasing control, it establishes `Ist`.
- A synchronized return also establishes equal results.

Every exported function obeys the same contract, so a re-entrant call starts
from `Ist`.

<!--
Prompt: Rely describes the premise at entry or resumption. Guarantee describes the obligation at call or return.
Prompt: Local source and target steps may temporarily break Ist. The control boundary is where the relation must hold.
-->

---

<!-- _class: diagram -->

# The unknown-Call rule uses the boundary contract

```text
⟨Call f(arg); Kₛ, sₛ⟩ ───────── Ist(sₛ, sₜ) ───────── ⟨Call f(arg); Kₜ, sₜ⟩
                              │
                  same function name and argument
                      guarantee Ist; Ctx runs
                              ▼
                one shared return value r
             post-states sₛ' and sₜ' satisfying Ist
                      rely on Ist; resume
                         ╱          ╲
                        ▼            ▼
                     Kₛ(r)         Kₜ(r)
```

The simulation proof summarizes the context execution through its return value
and the restored `Ist`.

<!--
Prompt: This is the high-level open-call rule. A concrete proof later instantiates it when the two Rocq trees expose matching calls.
Prompt: The rule quantifies over the shared return and related post-states. It therefore covers arbitrary context execution and re-entry.
-->

---

# The per-function simulation statement

For each exported function name `fn`, prove:

```coq
ISim.sim_fun open Source Target Ist fn
```

The statement requires the simulation to:

```text
receive source and target entry states satisfying Ist
match the two function bodies under the simulation rules
match observable events and unresolved calls
return equal values with final states satisfying Ist
```

<!--
Prompt: This is the first formal rung. Source occurs before Target in ISim.sim_fun.
Prompt: Keep tactics out of this slide. The next exercise introduces them while the corresponding Rocq goal is visible.
Handoff: Combine all exported-function statements into the module-level statement.
-->

---

<!-- _class: diagram -->

# Formal chain · assemble the module simulation

```coq
Lemma simF_fn :
  ISim.sim_fun open Source Target Ist fn.

Lemma sim : ISim.t open Source Target emp%I Ist.
Proof.
  cStartModSim.       (* initial Ist + one goal per exported function *)
  - (* prove the initial states satisfy Ist *)
  - apply simF_fn.    (* repeat for every exported function *)
Qed.
```

`cStartModSim` turns the module statement into:

```text
source function-map well-formedness
initial source and target states satisfy Ist
one ISim.sim_fun goal for each exported source function
```

<!--
Prompt: cStartModSim unfolds the ISim.t module obligation. apply reuses each proved ISim.sim_fun theorem.
Prompt: This is a construction proof: per-function simulations and the initial-state relation are the inputs to the module simulation.
Handoff: Apply the CRIS soundness and adequacy theorems to this completed sim statement.
-->

---

<!-- _class: diagram -->

# Formal chain · obtain behavior inclusion

```coq
Lemma ctxr : ⊢ ctx_refines Target Source.
Proof. eapply main_adequacy, sim. Qed.
```

```text
ctxr
  ≡ ∀ Ctx, refines (Target ★ Ctx) (Source ★ Ctx)
                        │ refines_adequacy
                        │ requires Mod.wf (Target ★ Ctx)
                        │          + initial world invariant
                        ▼
Mt := Mod.to_lmod (Target ★ Ctx) ε;  Ms(rs) := Mod.to_lmod (Source ★ Ctx) rs

∃ rs, ✓ rs ∧ refines_lmod Mt (Ms rs)
                        │ definition of refines_lmod
                        ▼
Beh.of_itree (LMod.compile Mt tt↑)
  ⊆
Beh.of_itree (LMod.compile (Ms rs) tt↑)
```

<!--
Prompt: main_adequacy is the soundness theorem from open module simulation to contextual refinement.
Prompt: ctx_refines supplies refines for any chosen context. refines_adequacy reaches the closed behavior-inclusion relation under its explicit semantic assumptions.
Action: Process Check ISim.sim_fun, Check ISim.t, simulation_is_enough, and Check refines_adequacy.
Prompt: Keep the argument orders visible: ISim.t takes Source then Target; ctx_refines and refines_lmod name Target first.
-->

---

<!-- _class: section -->

# A simulation proof, one goal at a time

Start with empty local state.

```text
Source: return (1 + 2)
Target: return 3
```

Open `day1/exercises/Optimizations.v`.

<!--
Prompt: RefinementIntro.v supplied the three statements. This demo inspects the goal produced at every rung.
Handoff: Open day1/exercises/Optimizations.v and fold the implementation of cStartTypedFunSim.
-->

---

<span class="file">day1/exercises/Optimizations.v · Example 1</span>

# One interface, two bodies

```coq
(* Source *)
fun _ => Ret ((1 + 2)%Z)

(* Target *)
fun _ => Ret 3%Z
```

The target has performed constant folding.

<!--
Prompt: Identify the common function name and check that both bodies have the declared Z return type.
-->

---

# The first state relation is True

```coq
Definition Ist : ist_type Σ :=
  fun _ _ => True%I.
```

Both modules start with empty local state.

Every pair of local states satisfies this first relation.

<!--
Prompt: Process Definition Ist. Ask what information a later step can recover from this relation: only True.
-->

---

# Goal 1 · Simulate one function

```coq
Lemma simF_fold_constants :
  ISim.sim_fun open Source Target Ist
    (fid StatelessOptHdr.fold_constants).
```

```text
one exported function
  source body  ~  target body
```

<!--
Prompt: This is the first statement from the proof ladder. Source appears before Target.
Action: Enter simF_fold_constants and inspect the goal before running a tactic.
-->

---

# Enter the function bodies

```coq
cStartTypedFunSim u.
```

The generated goal contains:

```text
"IST" : Ist st_src st_tgt
--------------------------------
source computation
target computation
postcondition: ist_with_eq Ist
```

`cStartTypedFunSim` resolves function lookup, decodes `Any.t`, and exposes the
typed argument `u : ()`.

<!--
Prompt: Run cStartTypedFunSim u. Locate u, st_src, st_tgt, and "IST" in the actual Rocq goal.
Prompt: Treat lookup and Any.t decoding as workshop infrastructure; begin the semantic proof at the two bodies.
-->

---

# Expose the two returns

```coq
unfold StatelessOptSource.fold_constants,
       StatelessOptTarget.fold_constants.
```

Read the center of the generated `wsim` goal as:

```text
source: Ret (1 + 2)
target: Ret 3
post:   ist_with_eq Ist
```

<!--
Prompt: Process the unfold command. Identify the next constructor on each side before choosing a tactic.
-->

---

# Match the two returns

```coq
cStep.
```

Rocq now asks for:

```coq
ist_with_eq Ist
  (st_src, (1 + 2)%Z↑)
  (st_tgt, 3%Z↑)
```

Its definition is:

```coq
⌜(1 + 2)%Z↑ = 3%Z↑⌝ ∗ Ist st_src st_tgt
```

<!--
Prompt: Run cStep and stop. cStep consumes the matching Ret constructors. Point to the pure equality and the restored state relation.
-->

---

# GUIDED DEMO 1 · Finish the function

<div class="demo">

Continue from the `ist_with_eq` goal:

```coq
iSplit; eauto.
```

Read `iSplit` from the connective in the goal:

```text
P ∗ Q
│   └── Ist st_src st_tgt, which reduces to True
└────── equal return values
```

Type the proof with the instructor, then replace `Admitted` with `Qed`.

</div>

<!--
Prompt: Continue from the goal produced by cStep. Run iSplit as a separate sentence so everyone sees both subgoals. Finish each with eauto.
Prompt: iSplit follows the Iris separating conjunction. The arithmetic equality computes to reflexivity; Ist unfolds to True.
-->

---

<span class="file">day1/exercises/Optimizations.v · Example 2</span>

# The optimization crosses an I/O boundary

```coq
(* Source *)
x <- trigger (IO (I := Z) "input" tt);;
Ret (x + 0)%Z

(* Target *)
x <- trigger (IO (I := Z) "input" tt);;
Ret x
```

`Behavior.v` records the external request and reply in the trace.
The optimization preserves that event and simplifies its continuation.

<!--
Prompt: Ask what an external observer can see before discussing tactics. Both programs issue the same request with the same argument. The arithmetic simplification happens after the reply.
Action: Process the read_simplify definitions and enter simF_read_simplify.
-->

---

# Match the event, then prove every continuation

```text
source: IO "input" () ──reply──▶ return (reply + 0)
target: IO "input" () ──reply──▶ return reply
```

```coq
cStep as reply.
cStep.
iSplit;
  [replace (reply + 0)%Z with reply by lia; done | done].
```

`reply` is arbitrary. One I/O simulation step gives both continuations the
same environment response. `lia` discharges the integer identity
`reply + 0 = reply`.

<!--
Prompt: Run cStep as reply and locate reply : Z in the Rocq context. The simulation rule quantifies over every response because the program cannot choose the input.
Prompt: The second cStep matches the returns. The remaining equality and Ist=True obligations use the same iSplit pattern as constant folding.
-->

---

<span class="file">day1/exercises/Optimizations.v · Example 3</span>

# A loop creates a family of simulation goals

```coq
(* Source *)
ITree.iter
  (fun cursor =>
     match cursor with
     | O => Ret (inr O)
     | S cursor' => Ret (inl cursor')
     end)
  n

(* Target *)
Ret O
```

The source takes `n` silent iterations. A proof for arbitrary `n` follows the
decreasing loop cursor.

<!--
Prompt: State the semantic reason for induction. The input determines how many source steps occur, so a fixed sequence of cStepS commands covers only one concrete input.
Action: Enter simF_countdown after processing its source and target definitions.
-->

---

# One unfolding exposes a smaller loop

Here `body` is the cursor function shown on the preceding slide.

```text
ITree.iter body O
  = Ret O

ITree.iter body (S n)
  = Tau (ITree.iter body n)
                          ▲
                   induction hypothesis
```

```coq
iInduction n as [|n] "IH".
aUnfoldS.
```

Successor case: `aUnfoldS` exposes `Tau` and the smaller iterator.

<!--
Prompt: These equations concern the whole iterator. The body returns inr O at zero and inl n at a successor; ITree.iter turns the latter into Tau followed by the recursive iterator.
Prompt: Connect the Rocq induction cases to the equations. The base case reaches a return. The successor case exposes one silent source step and the smaller cursor n.
-->

---

# STOP 1 · Follow the countdown cursor

<div class="stop">

Complete `simF_countdown`.

The starter has already executed:

```coq
iInduction n as [|n] "IH"; aUnfoldS.
```

Finish the two visible goals:

```coq
- cStep. iSplit; eauto.
- cStepS. iApply ("IH" with "IST").
```

Replace `Admitted` with your proof and `Qed`.

Reference solution: `day1/answers/Optimizations.v`

</div>

<!--
Prompt: Give 15–20 minutes. The comments name every new tactic. Ask which program fragment becomes smaller and why IH needs the current IST.
Resume: Process the two answer branches. Emphasize that countdown termination supplies structural induction; a potentially infinite loop requires coinductive reasoning.
-->

---

# Goal 2 · Assemble three function simulations

```coq
Lemma sim : ISim.t open Source Target emp%I Ist.
Proof.
  cStartModSim.
```

The module proof checks:

```text
source function-map well-formedness
empty initial states satisfy Ist = True
simF_fold_constants
simF_read_simplify
simF_countdown
```

<!--
Prompt: Enter sim and run cStartModSim. A module simulation covers every exported source function. The trivial initial relation is discharged during setup; the larger function map also exposes a well-formedness goal.
-->

---

# Register the three per-function simulations

```coq
all: try solve [mod_tac].
- apply simF_fold_constants.
- apply simF_read_simplify.
- apply simF_countdown.
Qed.
```

```text
return + I/O + finite loop simulations
                   ↓
          one module simulation
```

<!--
Prompt: mod_tac proves that every function-map entry is present. Each following bullet registers the function simulation proved above.
-->

---

# Goal 3 · Obtain contextual refinement

```coq
Lemma ctxr : ⊢ ctx_refines Target Source.
Proof.
  eapply main_adequacy, sim.
Qed.
```

<!--
Prompt: Apply main_adequacy first and state the remaining goal aloud: ISim.t open Source Target emp Ist. The lemma sim supplies it.
Prompt: Close by reading the conclusion semantically: every context-linked Target behavior is permitted by the corresponding Source.
-->

---

<!-- _class: diagram -->

# Recap · `ISim.t` proves contextual refinement

For every refinement example in this workshop:

```text
per-function statements
ISim.sim_fun open Source Target Ist fn
                    │ cStartModSim + apply
                    ▼
module-level statement
ISim.t open Source Target emp%I Ist
                    │ main_adequacy
                    ▼
⊢ ctx_refines Target Source
```

```coq
Lemma ctxr : ⊢ ctx_refines Target Source.
Proof. eapply main_adequacy, sim. Qed.
```

<!--
Prompt: Re-establish the global destination before introducing state. The exercises construct sim; main_adequacy converts it to contextual refinement.
Prompt: Source precedes Target in ISim.t. Target precedes Source in ctx_refines.
Handoff: The next example changes Ist while preserving this proof ladder.
-->

---

<span class="file">day1/exercises/Optimizations.v · Example 4</span>

# Store-to-load forwarding

```coq
(* Source *)
cput cell x;;;
y <- cgetU cell;;
Ret y

(* Target *)
cput cell x;;;
Ret x
```

Both stores are internal module steps.

<!--
Prompt: The target forwards x to the return. Ask what information connects the two private cells before and after the transformation.
-->

---

# The earlier relation, now in Rocq

```coq
Definition Ist : ist_type Σ :=
  fun st_src st_tgt =>
    (∃ x : Z,
      ⌜st_src = {[StateOptSource.cell # x↑]} /\
       st_tgt = {[StateOptTarget.cell # x↑]}⌝)%I.
```

```text
source cell: x  ~  target cell: x
```

This is the `Ist` used in the paired callback diagrams.
`StateOptHdr.mn ↯ "cell"` creates a state key qualified by the module name.

<!--
Prompt: Return to the diagram's sentence “both cells contain a.” The existential witness records that shared logical value inside Rocq and can change after a store or callback.
-->

---

# Read proof-mode tactics from connectives

| Assertion shape | Proof action |
|---|---|
| `⌜P⌝` | `iPureIntro` moves `P` to Rocq |
| `P ∗ Q` | `iSplit` creates one goal for each part |
| `∃ x, P x` | `iExists v` chooses the witness |
| `"H" : ∃ x, ⌜P x⌝` | `iDestruct "H" as (x) "%"` |

The state relation has the final shape:

```coq
∃ x : Z, ⌜source cell = x /\ target cell = x⌝
```

<!--
Prompt: Derive each tactic from the outer connective. This table supplies the proof-mode vocabulary used in STOP 2 and the KV proof.
-->

---

# Prove the re-entry function first

```text
initial relation      (old, old)
source store          (x,   old)
target store          (x,   x)
new relation witness  x
```

```coq
iDestruct "IST" as (old) "%".
cStepsS. cStepsT.
```

`cStepsS` and `cStepsT` execute consecutive deterministic steps on the source
and target sides.

<!--
Prompt: This is store_load, the function called by the concrete re-entrant context. Its simulation is one reason re-entry can restore the callback relation.
Prompt: Intermediate pairs may fall outside Ist; the proof restores it at the synchronization point.
Action: In day1/exercises/Optimizations.v, enter simF_store_load and stop at Admitted.
-->

---

# STOP 2 · Restore the cell relation

<div class="stop">

Complete `simF_store_load`.

The starter has matched the returns and left the new `Ist` goal:

```coq
iExists x. done.
```

Replace `Admitted` with your proof and `Qed`.

Reference solution: `day1/answers/Optimizations.v`

</div>

<!--
Prompt: Give 10–15 minutes. Ask which value should witness the new existential, then map the existential goal to iExists.
Resume: Open day1/answers/Optimizations.v and process the per-function simulation, module-level simulation, and adequacy line.
-->

---

# Return to the callback diagram

Both bodies write `x`, call a function supplied by the linking context, then
read their cells:

```coq
cput cell x;;;
ccallU CallbackHdr.touch tt;;;
y <- cgetU cell;;
Ret (y + 0)%Z                 (* source *)
Ret y                         (* target *)
```

The context may call an exported function before `touch` returns. In the two
paired executions, that call can update the corresponding source-side and
target-side cells. The final logical value can therefore differ from `x`.

<!--
Prompt: Recall the concrete trace with x = 5 and after = 7, then return to the general diagram where after is arbitrary.
Prompt: Ask whether the proof may remember x after the callback. In each paired execution, a re-entrant context can update that run's cell through the public API. The proof uses the post-call relation.
Action: Enter simF_callback_read and process through the iAssert.
-->

---

# Encode the boundary guarantee

Before the call, establish the guarantee:

```coq
iAssert
  (Ist {[StateOptSource.cell # x↑]}
       {[StateOptTarget.cell # x↑]})
  as "IST".
{ iExists x. done. }
```

`iAssert P as "H"` proves an intermediate assertion and keeps it under the
name `"H"`.

Match the unknown call:

```coq
cCall "IST" as (ret st_src st_tgt) "IST".
```

<!--
Prompt: Match this code to the “before touch: guarantee Ist(x)” node in the earlier STS.
Prompt: cCall consumes the pre-call guarantee and matches the same unknown call on both sides.
Action: Process through cCall and inspect the newly introduced values and IST.
-->

---

# Encode the post-call rely

After the call:

```text
ret                one arbitrary return shared by both continuations
st_src, st_tgt     an arbitrary pair of post-call states
"IST"              constraint: Ist st_src st_tgt
```

<!--
Prompt: Match these values to the “after touch: rely on Ist(after)” node. Open IST with witness after, read both cells, and finish with equal results plus the restored relation.
Action: Process the rest of simF_callback_read. Treat Any.downcast as typed-call infrastructure.
-->

---

# The earlier context, now in Rocq

```coq
Definition touch : () -> itree crisE () :=
  fun _ =>
    ccallU StateOptHdr.store_load 7%Z;;;
    Ret tt.
```

```text
callback_read x
  └─ touch()
       └─ store_load 7
  └─ read cell = 7
```

The final logical cell value is `7` in both paired executions.

<!--
Prompt: This is the touch pseudocode used in the earlier concrete trace. The value after is 7 here; the general theorem covers every compatible context.
Action: Process ReenteringContext.touch.
-->

---

# Specialize the all-context theorem

The contextual theorem already covers `ReenteringContext.t`:

```coq
⊢ refines
  (Target ★ ReenteringContext.t)
  (Source ★ ReenteringContext.t)
```

```coq
iPoseProof ctxr as "REF".
iSpecialize ("REF" $! ReenteringContext.t).
iExact "REF".
```

- `iPoseProof` names the reusable contextual theorem.
- `iSpecialize` chooses this concrete context.
- `iExact` closes the matching refinement goal.

<!--
Prompt: The function simulation already established the all-context theorem. This proof performs one universal instantiation.
Action: Process reentering_context_example one command at a time.
Handoff: The next example strengthens Ist from equal cells to two different data representations.
-->

---

<!-- _class: section -->

# First non-trivial data-representation proof

```text
SOURCE STATE                    TARGET STATE
abstract key-value map    ~     sorted list of key-value pairs
```

This example defines an `Ist` that connects two different representations of
the same logical storage.

Open `day1/exercises/KVSortedList.v`.

<!--
Prompt: State the new proof task directly. The source exposes an abstract key-value state; the target implements it with a sorted mathematical list.
Prompt: This is the first exercise where Ist is a representation relation.
Handoff: Open day1/exercises/KVSortedList.v and inspect the public header first.
-->

---

<span class="file">day1/exercises/KVSortedList.v</span>

# One API, two private representations

```text
get : Z → option Z
put : Z × Z → unit
```

```text
Source state  : Z → option Z
Target state  : list (Z × Z)
```

Clients see the API. The module owns the representation.

<!--
Prompt: The source is the abstract key-value specification. The target is the sorted-list implementation.
Action: Process KVHdr and compare both initial states.
-->

---

# Source lookup is immediate

```coq
Definition get : Z -> itree crisE (option Z) :=
  fun k =>
    'm : amap <- cgetU v_map;;
    Ret (m k).
```

```coq
Definition put : Z * Z -> itree crisE () :=
  ...
  cput v_map (map_put m k v);;;
  Ret tt.
```

<!--
Prompt: The abstract state is already a lookup function. get applies it directly.
-->

---

# Target state is a sorted mathematical list

```coq
Definition entries := list (Z * Z).

Fixpoint list_get (q : Z) (xs : entries) : option Z := ...
Fixpoint list_put (k v : Z) (xs : entries) : entries := ...
```

- keys are strictly increasing
- equal keys are overwritten
- lookup stops once the head key exceeds the query

<!--
Prompt: The list lives as one module-local mathematical value. Pointer ownership and allocation belong to a later workshop layer.
-->

---

# The representation relation

```coq
Definition state_rel (m : amap) (xs : entries) : Prop :=
  sorted_keys xs /\
  forall k, m k = list_get k xs.
```

```text
sortedness        supports ordered insertion and early lookup exit
lookup agreement  connects every observable get result
```

<!--
Prompt: Ask students to state this relation before processing its definition. Then compare their statement with the file.
-->

---

# Provided algebra for updates

```coq
sorted_keys_put :
  sorted_keys xs ->
  sorted_keys (list_put k v xs)

list_get_put :
  list_get q (list_put k v xs) =
  map_put (fun q => list_get q xs) k v q
```

<!--
Prompt: These are the supplied sequential data-structure lemmas. Their proofs are marked as provided in the file. The exercise combines them into state_rel_put.
-->

---

# STOP 3 · Relate the empty states

<div class="stop">

Complete `state_rel_empty`.

```text
empty_map  ~  []
```

The starter has already unfolded `state_rel` and split its conjunction:

```coq
- constructor.
- reflexivity.
```

Reference solution: `day1/answers/KVSortedList.v`

</div>

<!--
Prompt: The first goal is sortedness of the empty list. The second is pointwise agreement between two functions that both return None.
-->

---

# STOP 4 · Preserve the relation under `put`

<div class="stop">

Complete `state_rel_put`. The starter has exposed its two conjuncts:

```coq
- apply sorted_keys_put. exact Hsorted.
- intros q.
  rewrite list_get_put. unfold map_put.
  destruct (Z.eq_dec q k);
    [reflexivity | apply Hlookup].
```

Reference solution: `day1/answers/KVSortedList.v`

</div>

<!--
Prompt: Use 15–20 minutes across STOP 3 and STOP 4. Match each visible goal with one supplied lemma or one elementary list/function fact.
Resume: Open day1/answers/KVSortedList.v and process state_rel_empty and state_rel_put.
-->

---

# From `state_rel` to the full `Ist`

`IstLocal` owns the map/list cells and stores `state_rel m xs`.
The full relation also tracks state owned by the linking context:

```text
Ist =
  IstProd
    (IstSB Source.scopes IstLocal)
    IstEq
```

A provided helper hides this packaging:

```coq
Ist_from_state_rel m xs st :
  ⌜state_rel m xs⌝ ⊢
  Ist
    (union_with uwnd {[KVSource.v_map # m↑]} st)
    (union_with uwnd {[SortedListTarget.v_entries # xs↑]} st)
```

<!--
Prompt: IstSB selects module-owned state. IstEq says that the remaining context-owned state st is shared. Function exercises use the helper statement as an interface.
Action: Process IstLocal, Ist, and Ist_from_state_rel. Fold the helper proof after checking its statement.
-->

---

# Put repeats the restoration pattern

```text
pre-state      m      ~  xs
source update  map_put m k v
target update  list_put k v xs
post-state     related by state_rel_put
```

```coq
pose proof (state_rel_put m xs k v Hrel) as Hupdated.
cStep.
iSplit; [eauto |].
```

<!--
Prompt: Connect this diagram directly to the equal-cell timeline from day1/exercises/Optimizations.v.
Action: In day1/exercises/KVSortedList.v, enter simF_put and process the provided setup. Identify k, v, m, xs, Hrel, and the shared context state st_tgtR.
-->

---

# STOP 5 · KV put simulation

<div class="stop">

Complete `simF_put`.

```coq
iApply (Ist_from_state_rel _ _ st_tgtR).
iPureIntro.
exact Hupdated.
```

`Hupdated` is the mathematical step. The provided helper rebuilds the CRIS
state relation.

Reference solution: `day1/answers/KVSortedList.v`

</div>

<!--
Prompt: Give 10 minutes. Ask which helper conclusion matches the visible Ist goal and which pure fact supplies its premise.
Resume: Open day1/answers/KVSortedList.v and process its simF_put proof.
Handoff: Put restores the relation with supplied algebra. Get follows the iterator's control flow, so its proof follows the cursor by induction.
-->

---

<!-- _class: diagram -->

# Lookup carries a cursor

```coq
Definition get : Z -> itree crisE (option Z) :=
  fun q =>
    'xs : entries <- cgetU v_entries;;
    ITree.iter
      (fun rest : entries =>
        match rest with
        | [] => Ret (inr None)
        | (k, v) :: tl =>
            match Z.compare q k with
            | Lt => Ret (inr None)
            | Eq => Ret (inr (Some v))
            | Gt => Ret (inl tl)
            end
        end)
      xs.
```

<!--
Prompt: The induction variable is the remaining suffix, not the whole module state.
Action: Process SortedListTarget.get and point to the anonymous iterator body.
-->

---

# One skipped head produces Tau

```coq
match Z.compare q k with
| Lt => Ret (inr None)
| Eq => Ret (inr (Some v))
| Gt => Ret (inl tl)
end
```

`ITree.iter` interprets `inl tl` as continuation with the tail.

```text
Gt branch: one silent step, then search tl
```

<!--
Prompt: Lt and Eq terminate. Gt exposes the next cursor after an internal iterator step.
-->

---

# The proof follows the cursor

```coq
pose proof Hrel as Hstate.
destruct Hrel as [_ Hlookup]. rewrite Hlookup.
generalize xs at 1 3. iIntros (cursor).
```

After the rewrite, the goal contains the same list in two computational
positions: the source lookup and the target iterator cursor.
`generalize xs at 1 3` replaces those occurrences with one `cursor`.
`iIntros (cursor)` introduces that quantified value into the Iris goal.
`Hstate` keeps the relation for restoring `Ist`.

<!--
Prompt: Show the goal before and after generalize. Occurrence selection avoids changing the saved Hstate. The new cursor is exactly the target program's remaining suffix.
Action: Process through iIntros cursor, then run iInduction and inspect both goals.
-->

---

# Unfold one target iteration

```coq
iInduction cursor as [|[k' v'] tl] "IH"; aUnfoldT.
```

This first creates `[]` and nonempty-list goals. In the nonempty goal:

```coq
simpl. destruct (Z.compare k k') eqn:Hcmp.
```

| Cursor case | Proof action |
|---|---|
| `[]` | `cStep`, then restore `Ist` |
| `Eq` | `cStep`, then restore `Ist` |
| `Lt` | `cStep`, then restore `Ist` |
| `Gt` | `cStepT; iApply "IH"` |

`aUnfoldT` exposes one iteration; `cStepT` consumes the `Gt`-branch `Tau`.

<!--
Prompt: Connect aUnfoldT to the target iterator and cStepT to its Tau continuation. The terminating branches reuse the same helper as STOP 5.
Action: In day1/exercises/KVSortedList.v, process the supplied prefix of simF_get and stop at Admitted.
-->

---

# STOP 6 · Iterator induction

<div class="stop">

Complete `simF_get`.

Continue after the provided `iInduction` and `aUnfoldT`.

- `[]`: use `cStep`, `iSplit`, and `Ist_from_state_rel`.
- Nonempty: run `simpl; destruct (Z.compare k k') eqn:Hcmp`.
- `Eq` / `Lt`: reuse the terminating-case pattern.
- `Gt`: use `cStepT; iApply "IH"`.

Reference solution: `day1/answers/KVSortedList.v`

</div>

<!--
Prompt: Give 35–45 minutes. First ask everyone to write the four cases on paper. Release the answer proof branch by branch.
Resume: Open day1/answers/KVSortedList.v, process simF_get together, and explain aUnfoldT and cStepT at the Gt branch.
-->

---

# Assemble and return to behaviors

```coq
Lemma sim : ISim.t open Source Target emp%I Ist.
Lemma ctxr : ⊢ ctx_refines Target Source.
```

```text
state_rel_empty
      │
simF_put + simF_get
      │
      ▼
module simulation
      │ main_adequacy
      ▼
ctx_refines SortedListTarget KVSource
```

<!--
Prompt: The initial empty states satisfy the relation. Each exported operation preserves it. Adequacy gives the replacement theorem.
Action: Process sim and ctxr as an instructor-led closing proof.
-->

---

# Optional advanced · Make `put` iterative

```text
cursor = (prefix, rest)

rest = []             ──▶ finish with prefix ++ [(k, v)]
k < head.key          ──▶ finish with prefix ++ (k, v) :: rest
k = head.key          ──▶ finish with prefix ++ (k, v) :: tail
k > head.key          ──▶ continue with (prefix ++ [head], tail)
```

Maintain this equation at every iterator step:

```coq
prefix ++ list_put k v rest = list_put k v original
```

Open `day1/exercises/KVSortedListAdvanced.v`.

<!--
Prompt: Offer this exercise to early finishers. The suffix decreases in the induction, while the prefix records the processed cells. The invariant says that finishing the remaining insertion reconstructs the same pure list_put result.
-->

---

<!-- _class: lead -->

# Back to the first question

```text
sorted-list target + any compatible client
                    │ link and compile
                    ▼
              target behavior
                    ⊆
              source behavior
```

Every target behavior is permitted by the abstract key-value source.

<!--
Prompt: Trace the whole chain aloud: behavior, module, refinement, simulation, state relation, iterator induction, contextual refinement.
Close: Ask which cursor decreases in STOP 1 and STOP 6, and which relation witness changes in STOP 2 and STOP 5.
-->
