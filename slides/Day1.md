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
---

<!-- _class: lead -->

# From Behaviors to Contextual Refinement

Program Verification Workshop 2026

Day 1 · CRIS fundamentals and guided proofs

<!--
Prompt: Welcome the class and open Behavior.v. State one goal: follow a target module all the way to its observable behaviors.
Action: Ask everyone to process one Rocq sentence at a time.
-->

---

<span class="file">Behavior.v</span>

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
Action: Process Print Tr.t, Print Beh.t, and Check Beh.of_itree.
-->

---

# Return produces a terminating trace

```coq
Definition return_42 : itree coreE Any.t :=
  Ret (42%Z)↑.

Check (Tr.done (42%Z)↑).
Check (Beh.of_itree return_42 (Tr.done (42%Z)↑)).
```

```text
Ret 42  ─────────▶  done 42
```

<!--
Prompt: The interaction tree has finished. Its return value appears in the trace.
Action: Process return_42_terminates. Treat the proof as certification of the example.
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
Action: Process Check Tr.spin. Keep coinduction internals outside today's proof exercises.
-->

---

<!-- _class: section -->

# Where does the closed interaction tree come from?

```text
?  : itree coreE Any.t
              │
              ▼
         Beh.of_itree
```

Open `ModuleIntro.v`.

<!--
Prompt: We can now observe a closed tree. Real programs arrive as modules with calls and private state.
Handoff: Open ModuleIntro.v and ask how those pieces become the tree expected by Beh.of_itree.
-->

---

<span class="file">ModuleIntro.v</span>

# A module packages code and state

```coq
Check SMod.fnsems.
Check SMod.initial_st.
```

```text
module = named function bodies + private initial state + scope
```

Function bodies have type `itree crisE ...`.

<!--
Prompt: A module carries executable bodies and the state those bodies may access.
Action: Process the initial Check commands in ModuleIntro.v.
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

<!--
Prompt: The header gives the boundary a stable name, argument type, and return type.
Action: Process Check ConstHdr.get.
-->

---

# The service implements the boundary

```coq
Definition get : () -> itree crisE Z :=
  fun _ => Ret 42%Z.

Program Definition smod : SMod.t := {|
  SMod.fnsems := fnsems;
  SMod.initial_st := ∅;
|}.
```

The first service uses empty local state.

<!--
Prompt: Read fnsems as a finite map from the function name to this body.
Action: Process the ConstModule definitions and fold masks and fsp_none from the spoken explanation.
-->

---

# The client performs a call

```coq
Definition main : Any.t -> itree crisE Any.t :=
  fun _ =>
    n <- ccallU ConstHdr.get tt;;
    Ret n↑.
```

```text
MainModule.entry  ── Call get() ──▶  ConstModule.get
```

<!--
Prompt: ccallU produces a named Call event. Linking will supply its body.
Action: Process the MainModule definitions.
-->

---

# Link, compile, observe

```coq
Definition modules : Mod.t :=
  MainModule.t ★ ConstModule.t.

Definition program : itree coreE Any.t :=
  LMod.compile (Mod.to_lmod modules ε) tt↑.

Check (Beh.of_itree program).
```

<!--
Prompt: Linking supplies the function map. Compilation interprets calls and threads local state. Beh.of_itree program is the behavior set from the first file.
Action: Process LinkedProgram from top to bottom.
-->

---

# Private state will matter soon

```coq
Check cgetU.
Check cput.
```

```text
SGet key       reads the current module-local value
SPut key value updates the module-local value
```

Compilation interprets both operations while producing the closed tree.

<!--
Prompt: Preview these operations. The current ConstModule uses an empty state, so the first refinement example can ignore them.
-->

---

<!-- _class: section -->

# When may another service replace this one?

```text
MainModule ★ SourceService
MainModule ★ TargetService
```

The client was chosen today. A reusable replacement theorem must support clients
chosen later.

Open `RefinementIntro.v`.

<!--
Prompt: We have constructed and observed one implementation. Replacement asks for a comparison that survives future clients.
Handoff: Open RefinementIntro.v.
-->

---

<span class="file">RefinementIntro.v</span>

# Target behaviors are allowed by the source

```text
Beh(Target) ⊆ Beh(Source)
```

- `Source`: the reference program or specification
- `Target`: the implementation we plan to run

The target introduces no behavior outside the source set.

<!--
Prompt: Read the inclusion from a target trace toward a source trace.
Action: Process Check refines_lmod.
-->

---

# Closed-program refinement

```coq
Print refines_lmod.
```

Read its body as:

```text
Beh.of_itree (compile Target)
  ⊆
Beh.of_itree (compile Source)
```

<!--
Prompt: Compilation puts both sides back at the behavior interface from the first file.
Action: Process refinement_means_behavior_inclusion one line at a time.
-->

---

# A context supplies the rest of the program

```coq
Print ctx_refines.
```

```text
for every Ctx,
  refines (Target ★ Ctx) (Source ★ Ctx)
```

The same context is linked to both sides.

<!--
Prompt: The quantified context can contain any compatible caller and supporting modules.
Action: Point out that the theorem supports later clients without reopening this proof.
-->

---

# Keep the argument order visible

```text
behavior inclusion
  Beh(Target) ⊆ Beh(Source)

contextual refinement
  ctx_refines Target Source

simulation
  ISim.t ... Source Target ...
```

<!--
Prompt: Ask the class to read each line aloud. The simulation judgment lists the reference side first; the conclusion lists the replacing target first.
-->

---

# The proof challenge

```text
              Ctx₁   Ctx₂   Ctx₃   ...
                \      |      /
          Source  ~  Target
```

`ctx_refines` quantifies over every context.

We want one local proof that composes with all of them.

<!--
Prompt: Context enumeration is the specification. Simulation is the reusable proof method.
Handoff: Process the three Check commands for ISim.sim_fun, ISim.t, and main_adequacy.
-->

---

# Simulation discharges the contextual claim

```text
per-function simulations
          │
          ▼
ISim.t open Source Target IC Ist
          │
          │ main_adequacy
          ▼
IC ⊢ ctx_refines Target Source
```

<!--
Prompt: ISim carries a relation Ist between source and target module states. Adequacy returns to the replacement theorem.
Action: Process simulation_is_enough.
-->

---

<!-- _class: section -->

# What does an actual simulation proof look like?

Start with empty local state.

```text
Source: return (1 + 2)
Target: return 3
```

Open `Optimizations.v`.

<!--
Prompt: RefinementIntro supplied the proof ladder. Optimizations.v instantiates every rung.
Handoff: Open Optimizations.v and fold the implementation of cStartTypedFunSim.
-->

---

<span class="file">Optimizations.v · Example 1</span>

# One interface, two bodies

```coq
(* Source *)
fun _ => Ret ((1 + 2)%Z)

(* Target *)
fun _ => Ret 3%Z
```

The target has performed constant folding.

<!--
Prompt: Identify the function name shared by the two modules. Predict the target/source order of the final ctx_refines theorem.
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
Prompt: A simulation relation records exactly the information needed by future steps. This example needs no stored information.
-->

---

# A function simulation

```coq
Lemma simF_fold_constants :
  ISim.sim_fun open Source Target Ist
    (fid PureOptHdr.fold_constants).
```

```text
one exported function
  source body  ~  target body
```

<!--
Prompt: sim_fun is the per-function obligation previewed in RefinementIntro.v.
Action: Enter exercise_simF_fold_constants.
-->

---

# Process one proof step at a time

```coq
cStartTypedFunSim u.
unfold PureOptSource.fold_constants,
       PureOptTarget.fold_constants.
```

Now inspect the goal:

```text
source: Ret (1 + 2)
target: Ret 3
post:   restore Ist
```

<!--
Prompt: cStartTypedFunSim handles the Any.t boundary. The unfolded goal exposes the two typed bodies.
Action: Stop before Abort.
-->

---

# STOP 1 · Constant folding

<div class="stop">

Complete `exercise_simF_fold_constants`.

```coq
(* match the returns *)
(* restore Ist *)
```

Replace `Abort` with your proof and `Qed`.

</div>

<!--
Prompt: Give 5–8 minutes. Ask students to name the two obligations created by iSplit.
Resume: Process the reference simF_fold_constants proof together.
-->

---

# Assemble the module proof

```coq
Lemma sim : ISim.t open Source Target emp%I Ist.
Proof.
  cStartModSim.
  - iIntros "_". done.
  - apply simF_fold_constants.
Qed.

Lemma ctxr : ⊢ ctx_refines Target Source.
Proof. eapply main_adequacy, sim. Qed.
```

<!--
Prompt: cStartModSim asks for related initial states and one proof per exported function. main_adequacy closes the ladder from the previous section.
-->

---

<span class="file">Optimizations.v · Example 2</span>

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

# The relation carries one integer

```coq
Definition Ist : ist_type Σ :=
  fun st_src st_tgt =>
    (∃ x : Z,
      ⌜st_src = {[source_cell # x↑]} /\
       st_tgt = {[target_cell # x↑]}⌝)%I.
```

```text
source cell: x  ~  target cell: x
```

<!--
Prompt: The existential witness records the shared logical value. It can change after a store.
-->

---

# Open, step, restore

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

<!--
Prompt: A simulation relation is an invariant over paired states. Intermediate pairs may fall outside it; the proof restores it at the synchronization point.
Action: Enter exercise_simF_store_load and stop before Abort.
-->

---

# STOP 2 · Restore the cell relation

<div class="stop">

Complete `exercise_simF_store_load`.

```coq
(* match the final returns *)
(* choose x as the new relation witness *)
```

Replace `Abort` with your proof and `Qed`.

</div>

<!--
Prompt: Give 15–20 minutes. Ask which value should witness the new existential.
Resume: Process the reference function proof, module proof, and adequacy line.
-->

---

<!-- _class: section -->

# What if the states use different representations?

```text
equal integer cells
        ↓
abstract map  ~  sorted list
```

Open `KVSortedList.v`.

<!--
Prompt: The previous relation connected equal representations. Representation refinement keeps observations aligned across different state types.
Handoff: Open KVSortedList.v and inspect the public header first.
-->

---

<span class="file">KVSortedList.v</span>

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

state_rel_put :
  state_rel m xs ->
  state_rel (map_put m k v) (list_put k v xs)
```

<!--
Prompt: Treat the first two as the supplied sequential data-structure library. The simulation uses their combined state_rel_put result.
-->

---

# STOP 3–4 · Establish the pure relation

<div class="stop">

1. Prove `exercise_state_rel_empty`.
2. Prove `exercise_state_rel_put` using the provided lemmas.

```text
empty_map  ~  []

map_put m k v  ~  list_put k v xs
```

</div>

<!--
Prompt: Use 15–20 minutes. Keep the focus on choosing the two conjuncts and applying supplied algebra.
Resume: Process state_rel_empty and state_rel_put.
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
cFinishKVReturn Hupdated.
```

<!--
Prompt: Connect this diagram directly to the equal-cell timeline from Optimizations.v.
Action: Keep the standard Ist wrapper folded. Enter exercise_simF_put and process the supplied setup.
-->

---

# STOP 5 · KV put simulation

<div class="stop">

Complete `exercise_simF_put`.

```coq
pose proof (state_rel_put m xs k v Hrel) as Hupdated.
cFinishKVReturn Hupdated.
```

`Hupdated` is the mathematical step; the second tactic handles CRIS bookkeeping.

</div>

<!--
Prompt: Give 15–20 minutes. Ask students to identify the representation witnesses before writing tactics.
Resume: Process the reference simF_put proof.
Handoff: Put restores the relation with supplied algebra. Get follows the iterator's control flow, so its proof follows the cursor by induction.
-->

---

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
iInduction cursor as [|[k' v'] tl] "IH".
```

| Cursor case | Proof action |
|---|---|
| `[]` | unfold iterator, return `None` |
| `Lt` | return `None` |
| `Eq` | return `Some v'` |
| `Gt` | take target `Tau`, apply `IH` |

<!--
Prompt: Generalization gives the source lookup and target iterator the same cursor. The program structure then supplies the induction structure.
Action: Enter exercise_simF_get and stop before Abort.
-->

---

# STOP 6 · Iterator induction

<div class="stop">

Complete `exercise_simF_get`.

```coq
iInduction cursor as [|[k' v'] tl] "IH".
```

Use `cFinishKVReturn Hstate` in the terminating cases.<br>
Use `cStepT; iApply "IH"` in the `Gt` case.

</div>

<!--
Prompt: Give 35–45 minutes. First ask everyone to write the four cases on paper. Release the reference proof branch by branch.
Resume: Process simF_get together and explain aUnfoldT and cStepT at the Gt branch.
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
Close: Ask each student which relation witness changed in STOP 2 and STOP 5.
-->
