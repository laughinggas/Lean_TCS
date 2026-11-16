import Mathlib.Tactic
import Cslib.Foundations.Semantics.LTS.Basic

/-!
# Week 3: verifying a packet-batching router

In this sheet, we learn about some important tactics in Lean, which can do a lot of heavy lifting of a proof. First, lets try to remove the compilation errors in the file.

The imports above import certain files from `Mathlib` and `CSLib`, mathematical and CS libraries of theorems associated with Lean respectively. Currently, you probably don't have these libraries downloaded in your system. Look at `lakefile.toml`, you will see a dependency on CSLib has been established there. Now, to actually download it into your local copy, run `lake update cslib` in your VSCode terminal. VSCode might prompt, asking to install a certain version of Lean. If it does, then say yes. Installation might take about 10-15 minutes, and will require an active internet connection. Once the download is complete, you can shut VSCode and reopen. This file should then compile.

You can find the following imported files in the `.lake` folder. The location of the first imported file is `.lake/packages/mathlib/Mathlib/Tactic.lean`. The location of the second imported file is `.lake/packages/cslib/Cslib/Foundations/Semantics/LTS/Basic.lean`. Open the second file (note that you can read it but cannot modify it). It lists basic properties of Labelled Transition Systems (LTS). You can read through the file if you like. We will be using some definitions and theorems from there.

Mathlib provides the tactics `ring`, `positivity`, `omega` and `grind`.
TACTIC ROUTING
`ring`: polynomial equalities.
`omega`: solves `Nat`/`Int` linear constraints and truncated `Nat` subtraction, once any necessary polynomial identity has been proved separately.
`grind`: SMT solver-inspired proof automation tool that propagates equalities, instantiates supplied rules, and combines facts.
`positivity`: proves goals of the form `0 < a`, `0 ≤ a`, or `a ≠ 0`.

A router handles batches of packets for one fixed flow identifier. Two payload
fragments can be coalesced to share a header. Batch descriptors enter a bounded
queue; a permitted flow can forward one queued descriptor. We verify:
* the precise byte saving of coalescing;
* no queue overflow and no loss/creation of descriptors in the accounting;
* valid protocol transitions and preservation of safety along an execution.

A queue slot holds one batch descriptor, not one byte or one packet. n below
counts packets within a batch. The queue counters count descriptors. All counters
are of type `Nat`. We model counts and guards, not packet contents, FIFO order, elapsed
time, or cryptographic authentication. Receiving then forwarding one descriptor
need not forward the newly received descriptor if older ones were queued. -/

namespace PacketRouter

/- Two fragments of sizes `a` and `b` can be sent separately, paying two headers per
pair. -/
def splitBytes (n a b header : Nat) : Nat :=
  n * (a + header) + n * (b + header)

/- Two fragments of sizes `a` and `b` could also be sent together, paying one header per pair -/
def packedBytes (n a b header : Nat) : Nat :=
  n * (a + b + header)

-- Can you describe what `Buffer` does?
structure Buffer where
  queued : Nat
  forwarded : Nat
  received : Nat
  deriving Repr, DecidableEq

def enqueue (s : Buffer) : Buffer :=
  { s with queued := s.queued + 1, received := s.received + 1 }

def forward (s : Buffer) : Buffer :=
  { s with queued := s.queued - 1, forwarded := s.forwarded + 1 }

-- The capacity is external to the record.
def Safe (capacity : Nat) (s : Buffer) : Prop :=
  s.queued ≤ capacity ∧ s.queued + s.forwarded = s.received

namespace Wire

/-! `ring` normalizes polynomial expressions in a commutative semiring or ring (such as `Int`). Note that `Nat` subtraction does not count as ring subtraction. -/

-- header and payload costs can be accounted for separately.
example (n payload header : Nat) :
    n * (payload + header) = n * payload + n * header := by
  ring

/- Prove the following theorem. One serializer loops over each packet; another groups all payload and header bytes. Prove that their byte counts agree, using `ring`. Hint: the `unfold` tactic might help! -/
theorem split_expanded (n a b header : Nat) :
    splitBytes n a b header = n * a + n * b + 2 * n * header := by
  sorry

/- Prove that coalescing saves exactly one header per pair. -/
theorem savings (n a b header : Nat) :
    splitBytes n a b header = packedBytes n a b header + n * header := by
  sorry

end Wire

namespace Buffers

/-! `omega` can finish linear goals, including those containing subtraction of `Nat`. -/

example (queued capacity : Nat) (room : queued < capacity) :
    queued + 1 ≤ capacity := by
  omega

/- Prove `enqueue_safe`, which says that `enqueue` preserves safety, as long as the current queue is strictly less than the `capacity`.
Hint: `constructor` and `change` might be helpful. -/

/- Prove `forward_safe`, which says that forwarding preserves safety, as long as the initial queue is nonempty.
Hint: One can use `change` at a hypothesis as well. Some things can be left out with placeholders in a `change` statement, Lean will infer it. -/

end Buffers

inductive Event where
  | arrive
  | transmit
  deriving Repr, DecidableEq

/- The `flow` is fixed for this queue. `Permit` is its authorization policy. `receive` requires spare capacity. `send` requires a nonempty queue and authorization.
A `RouterStep` proof therefore carries evidence of the relevant runtime guards.
Note that the functions alone do not perform these checks. -/
inductive RouterStep (capacity : Nat) (Permit : Nat → Prop) (flow : Nat) :
    Buffer → Event → Buffer → Prop where
  | receive (s : Buffer) (room : s.queued < capacity) :
      RouterStep capacity Permit flow s Event.arrive (enqueue s)
  | send (s : Buffer) (nonempty : 0 < s.queued) (allowed : Permit flow) :
      RouterStep capacity Permit flow s Event.transmit (forward s)

/- `router` is a labelled transition system, as defined in CSLib. You can `ctrl+click` on `Cslib.LTS` to go to its definition in the appropriate file in CSLib. `lts.Tr s event t` means one valid step. -/
def router (capacity : Nat) (Permit : Nat → Prop) (flow : Nat) :
    Cslib.LTS Buffer Event where
  Tr := RouterStep capacity Permit flow

namespace Protocol

/- `grind` combines equalities and facts, including instances of universal rules.
It does not need to inspect a policy's implementation when the needed rule is
already a hypothesis. -/

example (Checked : Nat → Prop) (als flow : Nat)
    (hid : als = flow) (hcheck : Checked als) : Checked flow := by
  grind

/-  Use `grind` to prove the theorem below. -/
-- PS: you can also try `apply?`. This tactic tries to find the exact theorem which will close the goal.
theorem permission_from_rule (Checked Permit : Nat → Prop) (als flow : Nat)
    (hid : als = flow) (hcheck : Checked als)
    (rule : ∀ id, Checked id → Permit id) : Permit flow := by
  sorry

/- Prove `step_safe`, which says that every valid step preserves safety. -/
theorem step_safe (capacity : Nat) (Permit : Nat → Prop) (flow : Nat) :
    (router capacity Permit flow).TrInv (Safe capacity) := by
  sorry

/- CSLib also supplies `lts.MTr s labels t`, an execution with a finite event list.
Its `stepL` constructor prefixes one transition, while `refl` ends an empty trace. -/

/- Can you explain what this theorem does? -/
theorem two_step_trace (capacity : Nat) (Permit : Nat → Prop) (flow : Nat)
    (s mid t : Buffer)
    (h1 : (router capacity Permit flow).Tr s Event.arrive mid)
    (h2 : (router capacity Permit flow).Tr mid Event.transmit t) :
    (router capacity Permit flow).MTr s [Event.arrive, Event.transmit] t := by
  exact Cslib.LTS.MTr.stepL h1 (Cslib.LTS.MTr.stepL h2 Cslib.LTS.MTr.refl)

/- The following theorem says that any finite number of valid steps preserves safety (compare with `step_safe` above). -/
theorem trace_safe (capacity : Nat) (Permit : Nat → Prop) (flow : Nat) :
    (router capacity Permit flow).MTrInv (Safe capacity) := by
  exact Cslib.LTS.mtrInv_of_trInv (step_safe capacity Permit flow)

end Protocol

namespace Final

/-! The following is a description that AI came up with for the theorem below. What do you think of it?

The batch's paired payloads are coalesced, a descriptor is received, and an
authorized queued descriptor is forwarded. We need both local guard proofs
to establish that the execution exists. Invariant preservation alone would
not prove the existence of a valid transition or a permitted transmission.

Byte counts and descriptor counts measure different resources. The bandwidth
hypothesis budgets the split layout plus a reserve. The conclusion shows the
coalesced layout respects that same budget and quantifies the saving exactly. -/

/- Prove the following theorem. Don't be scared! Try to go through it step by step.

You might construct your own proof, or you can use the suggested (AI-generated) workflow below. Compare the two -- was yours shorter / more direct?
1. Use `Protocol.permission_from_rule` to establish `Permit flow`.
2. Build `hreceive` using `RouterStep.receive s room`.
3. Prove `0 < (enqueue s).queued`.
4. Build `hsend` using `RouterStep.send`, that positivity fact, and the permission.
5. Use `Protocol.two_step_trace`, then `Protocol.trace_safe` with the starting `hs`.
6. Obtain `Wire.savings`.
7. Prove the two counter equalities.
8. Package the six guarantees in a nested conjunction. -/
theorem verified_batch_cycle (capacity : Nat) (s : Buffer)
    (Checked Permit : Nat → Prop) (als flow : Nat)
    (n a b header budget reserve : Nat)
    (hs : Safe capacity s) (room : s.queued < capacity)
    (hid : als = flow) (hcheck : Checked als)
    (rule : ∀ id, Checked id → Permit id)
    (hbudget : splitBytes n a b header + reserve ≤ budget) :
    (router capacity Permit flow).MTr s [Event.arrive, Event.transmit]
      (forward (enqueue s)) ∧
      Safe capacity (forward (enqueue s)) ∧
      (forward (enqueue s)).queued = s.queued ∧
      (forward (enqueue s)).forwarded = s.forwarded + 1 ∧
      packedBytes n a b header + reserve ≤ budget ∧
      splitBytes n a b header - packedBytes n a b header = n * header := by
    sorry

end Final

namespace Stretches

/- Optional exercise! Prove that unauthorized flows cannot transmit. -/
example (capacity : Nat) (Permit : Nat → Prop) (flow : Nat) (s t : Buffer)
    (denied : ¬ Permit flow) :
    ¬ (router capacity Permit flow).Tr s Event.transmit t := by
  sorry

/- Optional exercise! Prove that the optimization is strictly beneficial. Hint: `positivity` might be helpful! -/
example (n a b header : Nat) (hn : 0 < n) (hh : 0 < header) :
    packedBytes n a b header < splitBytes n a b header := by
  sorry

end Stretches

end PacketRouter
