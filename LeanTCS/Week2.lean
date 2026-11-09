import Lean

/-!
In this file, we build a small collaborative programming platform. Users can read,
edit, and delete resources. We will model the data, state a permission policy,
make that policy executable, and prove that a protected edit respects it.

Our policy is:
  read   : the resource is public OR the user owns it;
  edit   : the user owns it;
  delete : the user owns it AND the resource is private.
The last condition is a product rule: public resources must be made private
before deletion. This is not a model of all real repository permissions. -/

/- Reminders from last week
`def name inputs : T := value` defines a named value of type T with inputs.
`theorem name hypotheses : P := proof` gives a named proof of proposition P with hypotheses.
`example hypotheses : T := value` checks an unnamed declaration. -/

-- A namespace is quite literally what it says: it names a given space. So if you write `namespace Name`, and then make a definition `Def` within it, then `Def` has the full name `Name.Def`. Inside `Name`, we can simply write `Def`. `end Name` closes the namespace `Name`.
namespace AccessControl

/- An `inductive` type lists constructors. In the case below, there are three possible users and actions respectively.
`deriving Repr` supplies printing support for `#eval`. Its purpose is to instruct Lean to generate a function that converts users into text.
`deriving DecidableEq` supplies an equality decision procedure. We will examine
this later in this file. -/

inductive User where
  | alice
  | bob
  | eve
  deriving Repr, DecidableEq

inductive Action where
  | read
  | edit
  | delete
  deriving Repr, DecidableEq

/- A `Resource` has an owner, a visibility flag, and a
body. For this small exercise, its body is just a natural-number document version. -/
structure Resource where
  owner : User
  isPublic : Bool
  body : Nat
  deriving Repr, DecidableEq

-- Define the Resource `publicDoc` whose owner is Alice, body is 10, and document is public. Also define `privateDoc` whose owner is Bob, body is 20, and document is private.

#eval publicDoc

#eval privateDoc

/-- The following definition changes the body of a given resource `r` to the given number `n`. -/
def replaceBody (r : Resource) (n : Nat) : Resource :=
  { r with body := n }

/- Note that `{ r with body := n }` creates a new record, copying all other fields from r. Lean values are immutable: it does not modify r. The original remains available. -/

#eval (replaceBody publicDoc 11).body

-- Define `setVisibility`, which changes the publicity of the given resource `r` to the given Boolean `b`.

example : publicDoc.owner = User.alice := by
  sorry

-- Note: an unnamed example can build data too, not just prove a proposition.
example : Resource :=
  { owner := User.eve, isPublic := false, body := 0 }

/- Write an example showing that replacing a resource's body preserves its owner. -/

/- Now write a theorem named `replaceBody_setVisibility_comm`, which states that changing visibility and replacing the body commute. In other words, changing visibility and then replacing the body is the same as replacing the body and then changing visibility. -/

/- A subtype `{r : Resource // r.owner = User.alice}`
is a data type containing a usable resource together with a proof about it.
Return usable data with a proof: build an Alice-owned resource in a subtype. `⟨value, property⟩` constructs a subtype. You can type `⟨` by doing `\`+`<`. If `a` is a term which has type a subtype, then `a.val` or `a.1` gives the value, and `a.prop` or `a.2` gives the proof of the property. -/
example : {r : Resource // r.owner = User.alice} := sorry
-- What do you think is the type of this set?

inductive Request where
  | read
  | modify (update : Nat → Nat)
  | setVisibility (visible : Bool)
/- As shown in the example above, constructors in inductive definitions can have inputs. `modify` takes an operation as its argument: a function Nat → Nat. `setVisibility` carries Boolean data.
`Request.modify : (Nat → Nat) → Request` is a constructor function; applying it stores an operation. Note that it does not yet execute that operation. -/

#check Request.read

/- `requiredAction` maps the richer request to the permission category it needs. -/
def requiredAction : Request → Action
  | Request.read => Action.read
  | Request.modify _ => Action.edit
  | Request.setVisibility _ => Action.edit

/-- `runRequest` acts on the request. -/
def runRequest (q : Request) (r : Resource) : Resource :=
  match q with
  | Request.read => r
  | Request.modify f => replaceBody r (f r.body)
  | Request.setVisibility b => setVisibility r b

/- `match` is a pattern-matching tactic: it matches the given term `q` with all the possible options it could take. -/

-- Do you understand what `runRequest` does?

/-! `matchesAction` checks whether a `Request` is labelled with its correct `Action`.
The comma-separated patterns inspect both arguments. For example, the `modify` constructor together with
the `edit` constructor produces true.
The wildcard placeholder `_` matches anything (that has not already been specified) without naming it, covering all
remaining pairs. -/
def matchesAction : Request → Action → Bool
  | Request.read, Action.read => true
  | Request.modify _, Action.edit => true
  | Request.setVisibility _, Action.edit => true
  | _, _ => false

-- What do the following evals check?
#eval matchesAction (Request.modify (fun n => n + 1)) Action.edit
#eval matchesAction (Request.modify (fun n => n + 1)) Action.read

-- A proof by cases on both inductive values verifies the complete table.
-- You saw the `cases` tactic last week: there is a way to simpify its usage, as done below.
-- `<;>` applies the tactic on its right to EVERY goal made by the tactic on its left.
-- Put your cursor right before the two `<;>`. You will see multiple goals which are case splitting on `a` and `q`. In this case, the tactic after `<;>` completely solves all cases.
theorem matchesAction_correct (q : Request) (a : Action) :
    matchesAction q a = true ↔ a = requiredAction q := by
  cases q <;> cases a <;> simp [matchesAction, requiredAction]

/- A type is recursive when one of its constructors contains an argument of that
same type: a recursive function calls itself. `Request` is not recursive: its operation argument has type `Nat → Nat`, not `Request`. `RequestBatch` below is recursive. -/
inductive RequestBatch where
  | empty
  | step (head : Request) (tail : RequestBatch)

-- What does the definition below do?
def batchLength : RequestBatch → Nat
  | RequestBatch.empty => 0
  | RequestBatch.step _ rest => 1 + batchLength rest

-- Can you define `appendBatch`, which joins two batches?

-- Now define `runBatch`, which executes requests from left to right on an evolving resource

-- Can you define `exampleBatch` of type `RequestBatch`, which sets the visibility to `true` and then modifies to `n + 1` from `n`?

-- Do you get the expected answers?
#eval batchLength exampleBatch -- 2
#eval (runBatch exampleBatch privateDoc).body -- 21
#eval (runBatch exampleBatch privateDoc).isPublic -- true

namespace BatchLemmas

-- Prove that the batch length of appended batches is the sum of the batch lengths.
theorem batchLength_append (xs ys : RequestBatch) :
    batchLength (appendBatch xs ys) = batchLength xs + batchLength ys := by
  -- The `induction` tactic is used for inductive definitions. Here, we try to break down `xs` into its base case and its inductive step: if true up to a certain step, then true for the next step. For the second one, we give the inductive constructors as well as an extra `ih`, which is the hypothesis that the target is true up to a certain point, and the goal changes to proving it for the next step.
  induction xs with
  | empty => simp only [appendBatch, batchLength, Nat.zero_add]
  | step q rest ih =>
      simp only [appendBatch, batchLength, ih, Nat.add_assoc]

-- Prove that the batch length is 0 if and only if the batch length is empty.
-- Hint: use `cases` on `xs`.
theorem batchLength_eq_zero_iff (xs : RequestBatch) :
    batchLength xs = 0 ↔ xs = RequestBatch.empty := by
  sorry

-- `generalizing r` lets it be applied to the new resource produced by the first request.
-- `simpa [...] using h` can adapt a proof whose type becomes the goal after simplification.
theorem runBatch_append (xs ys : RequestBatch) (r : Resource) :
    runBatch (appendBatch xs ys) r = runBatch ys (runBatch xs r) := by
  induction xs generalizing r with
  | empty => rfl
  | step q rest ih =>
      simpa only [appendBatch, runBatch] using ih (runRequest q r)

-- `calc` presents an equality proof as a chain; `_` stands for the preceding right-hand side.
theorem runBatch_owner (xs : RequestBatch) (r : Resource) :
    (runBatch xs r).owner = r.owner := by
  induction xs generalizing r with
  | empty => rfl
  | step q rest ih =>
      calc
        (runBatch (RequestBatch.step q rest) r).owner
            = (runRequest q r).owner := ih (runRequest q r)
        _ = r.owner := by cases q <;> rfl

-- What is the theorem above proving?
end BatchLemmas

namespace GeneratedDeclarations -- starting a new namespace inside the namespace `AccessControl`

/-! Lean builds more than a new type when you write an inductive def or structure.
The following are some of the automatically generated declarations:

Declaration                 Purpose
Declaration                 Purpose
`Request.modify`              Constructor; packages a `Nat → Nat` operation.
`Request.casesOn`             Case-analysis helper; no induction hypotheses.
`Request.modify.inj`          From `modify f = modify g`, obtain `f = g`.
`Request.modify.injEq`        Rewrites `(modify f = modify g)` to `(f = g)`.

`Resource.mk`                 Default structure constructor, in field order.
`Resource.owner`              Projection `Resource → User`.
`Resource.isPublic`           Projection `Resource → Bool`.
`Resource.body`               Projection `Resource → Nat`.
`Resource.casesOn`            Elimination/case-analysis helpers for the record.
`Resource.mk.inj` / `.injEq`     Constructor injectivity, now for its three fields.

Like inductive defs, structures also inherit automatically generated theorems. A namespace is created in the name of the structure, and these theorems exist there. `Resource.mk` expects arguments in the order of declaration: `owner`, `isPublic`, `body`. Record syntax names those arguments.

(To do at home if interested) To learn more about this, read Chapters 7, 8 and 9 here:
https://lean-lang.org/theorem_proving_in_lean4/Inductive-Types/#inductive-types
-/
-- ask me / discuss if you don't understand these! Good to know but not necessary
#check Request.modify
#check Request.casesOn
#check Request.modify.inj
#check Request.modify.injEq

#check Resource.mk
#check Resource.owner
#check Resource.mk.inj
#check Resource.mk.injEq

example : Resource.owner (Resource.mk User.alice true 10) = User.alice := by
  sorry

-- Prove the following example which which says that if two resources are equal, then their visibility is the same.
-- Hint: The `have` tactic might help with the proof, along with the lemmas mentioned above. The `have` tactic can be used to make a new hypothesis within the proof context. The syntax is the same as `theorem`, where `theorem` is replaced with `have`. `have hnew : Hypothesis := by ...` opens a subproof of `Hypothesis`. Once it is proved, Lean adds `hnew : P` to the local context and returns to the original goal. You must prove the intermediate fact; `have` does not assume it without justification (you can use `sorry` if you want to prove it later). `have hnew := proofTerm` asks Lean to infer its type.
-- Note that the local name of the `have` statement is not available outside the proof.
example (u v : User) (b c : Bool) (n m : Nat)
    (h : Resource.mk u b n = Resource.mk v c m) : b = c := by
  sorry

-- Write an example which states that modification of a `Request` is equal for two different `Nat → Nat` functions if and only if the functions are equal. iff, denoted `↔`, is typed by `\`+`iff`.
-- Try to use `simp` to prove it in one line. What does `simp` use?

/- Prove that incrementing publicDoc's body by 1 produces 11. -/

/- Prove that if resources are equal, then owners are the same. Do not substitute or destruct h.
Hint: `congrArg p h` applies the same function p to both sides of an equality.
Which function p is appropriate here? -/
example {r s : Resource} (h : r = s) : r.owner = s.owner := by
  sorry

/- Show that if `Request.modify f = Request.modify g` for some `f` and `g`, then the two requests have the same effect on any resource; that is, the modified requests run on the same resource are the same. -/

/- Use the generated constructor `Resource.mk` to complete this example. -/
example : {r : Resource // r.owner = User.alice} := by
  sorry

end GeneratedDeclarations -- closing the newer namespace

/- The following definition defines what actions are "allowed". -/
def Allowed (u : User) (a : Action) (r : Resource) : Prop :=
  match a with
  | Action.read => r.isPublic = true ∨ u = r.owner
  | Action.edit => u = r.owner
  | Action.delete => u = r.owner ∧ r.isPublic = false

namespace PolicyLogic

-- A `section` is a scope for variables and other local settings; it does not add a prefix to declaration names. Closing a section stops its variables being available to later declarations. A namespace also creates a scope, but additionally prefixes names.

section Requests

/- The `variable` below declares u and r once for any statements that need them in this `section`. Note that `variable` does not choose concrete values. Each declaration using them receives the parameters it needs. Unused `section` variables are normally omitted from the resulting declaration. One can also define implicit variables. -/

variable (u : User) (r : Resource)

-- Prove the following.
-- Hint: When you have `a ∨ b` in your goal, `left` and `right` will change the goal to `a` and `b` respectively.
example (u : User) (r : Resource)
    (h : r.isPublic = true ∨ u = r.owner) : Allowed u Action.read r := by
  sorry

-- Prove the theorem `ownerMayRead`: if a given user is the owner of a given resource, then the user is allowed to perform the read action on the resource.

-- Hint: When you have `h : a ∧ b`, `h.1` and `h.2` will change the goal to `a` and `b` respectively.
-- Prove that, if a user is allowed to perform the delete action on a resource, then the user is the owner of the resource.

/- * `constructor` splits an AND goal.
* Bullets `·` (hover on it to see how it is typed) delimit separate goals. -/

-- Prove that an owner may delete a private resource.

-- Prove that deletion permission implies both editing permission and reading permission.

end Requests

-- u and r from Requests are now out of scope. We introduce fresh parameters.

/- Refute the assertion that every reader may edit through an example.
`¬ P` abbreviates `P → False` or `not P`. -/

end PolicyLogic

/-! A `class` is a `structure` whose values Lean can "remember", or can automatically find. -/

/- `Owned α` supplies an owner operation for values of type α. -/
class Owned (α : Type) where
  owner : α → User

-- Like for `structure`, a dictionary of theorems/defs is constructed for `class`.
#check Owned.mk
-- Projections are built as well
#check Owned.owner

-- `instance` is what is "remembered" by Lean.
-- This property here is saying that every `Resource` has an `owner`. Going ahead, defining this as an instance would mean that, if you have a `Resource`, and if you need the fact that it is `Owned`, you do not need to prove it, Lean will automatically supply a proof (we shall see how this happens ahead).
instance resourceOwned : Owned Resource where
  owner := Resource.owner

structure Issue where
  author : User
  closed : Bool
  deriving Repr, DecidableEq

-- Define and prove an `instance` `issueOwned` which shows that `Issue` is `Owned`.
instance issueOwned : Owned Issue where
  owner := Issue.author

/- The `[]` brackets are used for hypotheses which are instances. You already know explicit arguments `(x : α)` and implicit arguments `{α : Type}`. The new binder `[Owned α]` is an `instance` argument: Lean searches registered
instances to supply an internal proof of this. Note that this can only be used for a `class`, which is `Owned`, in this case. -/
def IsOwner {α : Type} [Owned α] (u : User) (x : α) : Prop :=
  u = Owned.owner x

namespace Interfaces

-- `#synth C` asks Lean to find an instance of C.
#synth Owned Resource
#synth Owned Issue

-- DecidableEq is another class: `[DecidableEq α]` supplies, for ANY x y : α,
-- a decision of x = y. Our earlier `deriving DecidableEq` generated these instances.
#synth DecidableEq User


-- In this example, the resource argument determines α = Resource; Lean then supplies the proof `resourceOwned`.
theorem isOwner_resource (u : User) (r : Resource) : IsOwner u r ↔ u = r.owner := by
  sorry

-- Now comment out the `instance` you made, which shows `Owned Resource`. What happens? Why?

-- (Please uncomment it!)

-- Can you show that Alice is the owner of an issue authored by Alice?

section GenericOwnership

variable {α : Type} [Owned α]

/- Given an element of type `α` (which has an `Owned` instance on it -- look at `variable` above), prove that the owner returned by the interface owns the element. -/
example (x : α) : IsOwner (Owned.owner x) x := by
  sorry

-- A conversion `f` preserves ownership. Show it preserves the ownership predicate in both directions.
-- Hint: `unfold IsOwner` exposes the definition of `IsOwner`. Remember also that `rw` works for any expression which has an equivalence relation. For example, it works for statements with `=` or with `↔`.
theorem isOwner_map {β : Type} [Owned β] (f : α → β)
    (preserves : ∀ x, Owned.owner (f x) = Owned.owner x)
    (u : User) (x : α) : IsOwner u (f x) ↔ IsOwner u x := by
  sorry

end GenericOwnership

structure Wrapped (α : Type) where
  value : α

/- Build an `Owned` instance for this wrapper assuming an `Owned` instance on `α`. -/

end Interfaces

/-! An arbitrary `P : Prop` is a statement, not necessarily an executable test.
`Decidable P : Type` contains one of:
  `Decidable.isTrue h  where h : P` or
  `Decidable.isFalse h where h : ¬ P`.
Unlike `P`, this has computationally distinguishable branches.
We now know how to convert terms of type `Prop` into data types!
-/
#check Decidable
#check DecidableEq

/- Below, we register a decision procedure for the policy. Lean combines equality decisions with standard decisions for `∧` and `∨`. `infer_instance` finds those constructive instances. -/
instance allowedDecidable (u : User) (a : Action) (r : Resource) :
    Decidable (Allowed u a r) := by
  unfold Allowed
  cases a <;> infer_instance

#synth Decidable (Allowed User.bob Action.read publicDoc)

-- What does this def do?
-- `decide P : Bool` converts a decision on the proof of `P:Prop` into a Boolean answer.
def canAccess (u : User) (a : Action) (r : Resource) : Bool :=
  decide (Allowed u a r)

#eval canAccess User.bob Action.read publicDoc
#eval canAccess User.bob Action.edit publicDoc
#eval canAccess User.bob Action.delete privateDoc

-- Now define `requestCanRun`, which returns a `Bool` deciding on whether the action corresponding to a request is allowed for a given resource by a given user.
-- Clue: use `requiredAction`

#eval requestCanRun User.alice (Request.modify (fun n => n + 5)) publicDoc
#eval requestCanRun User.eve (Request.modify (fun n => n + 5)) publicDoc

namespace Decisions

/-! `decide P : Bool` converts a decision on P into a Boolean answer.
`decide` is also a tactic: it proves a proposition by computing its decision.
These are related but have different result types. You can also prove `¬ P` by
computation when the supplied procedure determines that `P` is `false`.

`if P then x else y` needs an instance `[Decidable P]` when `P` is a proposition.
`if h : P then ... else ...` additionally names the evidence: `h : P` in the
first branch and `h : ¬ P` in the second.

`by_cases h : Q` makes two proof goals: one has `h : Q` as an assumption, and the other has `h : ¬ Q`. -/

-- Prove that the user Eve is not allowed to edit `privateDoc` using the tactic `decide`.

-- Prove that, if a certain action is allowed, then the user can access the resource by the given action.

/- Use computation to show that Alice cannot delete her public resource. Explain which part of the deletion policy fails. -/

/- Manually construct the decision for edit access. Do not solve the whole goal
with `infer_instance`: first split on `Allowed u (requiredAction q) r`, then simplify each branch.
Note: This definition is not registered as an instance, avoiding competing defaults. If not, it could lead to errors, or "diamonds". We don't discuss these further, ask me if you're curious! -/
def manualEditDecision (u : User) (r : Resource) :
    Decidable (Allowed u Action.edit r) := by
  sorry
-- try to replace `def` above with `theorem`. What happens and why?

/- Prove that `requestCanRun` is `true` if and only if the required action on the request is allowed. -/

/- Abstract the idea to any proposition with a supplied decision procedure.
Prove that a numeric indicator is 1 exactly when P holds.
Why is `[Decidable P]` required in the statement? -/
example {P : Prop} [Decidable P] :
    (if P then (1 : Nat) else 0) = 1 ↔ P := by
  sorry

-- Prove `canAccess_iff`, which says that a `User` can access if and only if they are performing an allowed action. Can you use the `<;>` tactic?
-- How would you formalize this theorem statement? Does it match what is below? Go through the proof, notice how short it is.

-- Prove `requestCanRun_iff`, which says that a request can run iff the user is allowed to do the required action on the request.

end Decisions

namespace RequestReasoning

-- Prove the theorem `runRequest_owner` which says that the owner of a run resource is the same as the owner of the resource.
-- Hint: break it down into the right `cases`.

-- Prove that editing is allowed for a request run on a resource if and only if editing is allowed on the resource.
-- Hint: `change P` changes the goal to `P` if `P` is definitionally equal to the goal.

/- Prove that a user is allowed to read any resource whose visibility is set to `true`. -/

/- Prove that a read request has no effect on any resource. -/

/- Prove that running `modify f` followed by `modify g` has the same effect as one request carrying their composition. Order matters: f runs first, then g. -/

/- Prove that: after any authorized request, its user can read the resulting resource. -/

/- Disprove the claim that visibility changes preserve all existing permissions:
Bob may delete `privateDoc`, but making it public removes deletion permission.
Explain why this does not contradict the ownership invariant proved above. -/
example : Allowed User.bob Action.delete privateDoc ∧
    ¬ Allowed User.bob Action.delete
      (runRequest (Request.setVisibility true) privateDoc) := by
  sorry

-- Prove `owner_may_request`: if a `User` is the owner of a `Resource`, then the user is allowed to perform the required action.

-- Prove `owner_after_request`: if a `User` is the owner of a `Resource`, then the user is the owner after the request has run.

end RequestReasoning

-- We ask only for the document version when a resource was actually returned.
def returnedBody (result : Option Resource) : Option Nat :=
  match result with
  | none => none
  | some r => some r.body

example (result : Option Resource) : returnedBody result = result.map Resource.body := by
  cases result <;> rfl

/- `protectedRun` returns `none` if a required action is not allowed, and returns an "accepted" result otherwise. -/
def protectedRun (u : User) (q : Request) (r : Resource) : Option Resource :=
  if Allowed u (requiredAction q) r then some (runRequest q r) else none

/- `Option α` is a standard inductive data type supplied by Lean. Its elements are "optional" values, which are either `some x` around a value `x` from the underlying type `α`, or `none`, which carries no value.
Note that `Option Resource` and `Resource` are different types. To use a returned
`Resource`, a caller must handle the possibility that there is none.

`Option` can represent nullable types or computations that might fail. `Option` is also useful for parsing text that may not be a number, looking up a missing key, and safely indexing a list. A function returning `Option` can give a
result for every input while representing the cases where its intended answer
is absent. `Option` does not explain why a request failed; types such as `Except` can be used if failure reasons must be known. We don't cover this, ask me if you want to know more! -/

-- What are the two evals below doing? Hover over `map` to see what it does. This is something that is defined in the Lean library. You can `Ctrl+click` on it to see the definition in the Lean file.
#eval (protectedRun User.alice (Request.modify (fun n => n + 1)) publicDoc).map Resource.body
#eval (protectedRun User.eve (Request.modify (fun n => n + 1)) publicDoc).map Resource.body

/- The alternative `runWithProof` takes an authorization proof from its caller.
It does not itself need to compute a decision. -/
def runWithProof (u : User) (q : Request) (r : Resource)
    (_permission : Allowed u (requiredAction q) r) : Resource :=
  runRequest q r

-- Notice that both methods return data, but the proof input in the second method is erased when compiling executable code.

namespace ProtectedOperations

/-! Useful tools beyond the familiar four tactics:
* `unfold D at h` exposes the def `D` in a hypothesis `h`.
* `split at h` separates its branches and splits into goals, retaining the condition or its negation.
*  `next hallowed =>` names the first unnamed evidence.
* `Option.some.inj h` recovers `x = y` from `some x = some y`. This is the same mechanism as `Request.modify.inj`.
* `subst r'` replaces a variable `r'` using an equality in the hypotheses / context.
* `cases h` eliminates the impossible equality none = some r'. In this case, it follows from `Request.noConfusion`.
For more tactics and explanations of these tactics, please look at the tactic cheatsheet provided in the Github repo. -/

-- Prove: given evidence, the runtime check accepts the exact result. This relates the checking method and the proof-requiring method for any request.
theorem protectedRun_of_allowed (u : User) (q : Request) (r : Resource)
    (h : Allowed u (requiredAction q) r) :
    protectedRun u q r = some (runRequest q r) := by
  sorry

-- Note that the proof-requiring method can also compute.
example :
    (runWithProof User.alice (Request.modify (fun n => n + 1)) publicDoc rfl).body
      = 11 := by
  sorry

/- Prove that an owner can successfully run any body-modifying operation `f`. -/
-- Hint: look for previously proved theorems above!
example (f : Nat → Nat) (r : Resource) :
    protectedRun r.owner (Request.modify f) r =
      some (runRequest (Request.modify f) r) := by
  sorry

/- Prove that every unauthorized request is rejected. -/

/- Every successful request was authorized, returns the exact interpreted result,
and preserves ownership.

Tip: It will help to form a mental model of the proof before you actually start coding the proof. -/
theorem successfulRequestIsSafe (u : User) (q : Request) (r r' : Resource)
    (h : protectedRun u q r = some r') :
    Allowed u (requiredAction q) r ∧ r' = runRequest q r ∧ r'.owner = r.owner := by
  sorry

/- Relate the checking method and the proof-requiring method for any request.
If permission is already known, their returned Resource values agree.
Hint: Why does the checker require a
decision procedure while runWithProof itself does not? -/
example (u : User) (q : Request) (r : Resource)
    (h : Allowed u (requiredAction q) r) :
    protectedRun u q r = some (runWithProof u q r h) := by
  sorry

/-!
Leaving you with some food for thought:
1. Why return a Resource or a subtype rather than an existential proof when the
   caller needs computational data?
2. Could a function always returning none satisfy successfulRequestIsSafe?
   Yes: safety alone does not guarantee success. The worked acceptance lemma
   and Exercise 6.1 specify when this particular implementation succeeds.
3. What authentication does this model establish? None: it assumes its User
   argument identifies the caller. Its theorem proves the specified permission rule.
-/

end ProtectedOperations

-- The following material is a longer worked extension / take-home discussion.

-- `BatchAllowed` is a proposition describing authorization at every intermediate
-- state, not just at the initial `Resource`.
def BatchAllowed (u : User) : RequestBatch → Resource → Prop
  | RequestBatch.empty, _ => True
  | RequestBatch.step q rest, r =>
      Allowed u (requiredAction q) r ∧ BatchAllowed u rest (runRequest q r)

-- `batchCanRun` is an executable `Bool`.
def batchCanRun (u : User) : RequestBatch → Resource → Bool
  | RequestBatch.empty, _ => true
  | RequestBatch.step q rest, r =>
      requestCanRun u q r && batchCanRun u rest (runRequest q r)

-- `protectedBatch` returns data in `Option` and stops at the first rejected request.
def protectedBatch (u : User) : RequestBatch → Resource → Option Resource
  | RequestBatch.empty, r => some r
  | RequestBatch.step q rest, r =>
      match protectedRun u q r with
      | none => none
      | some mid => protectedBatch u rest mid

namespace BatchVerification

-- This induction reuses the earlier bridge for a single request.
-- Prove `batchCanRun_iff`: a batch can run iff the batch is allowed.

-- Soundness: success guarantees the exact unchecked result, every permission,
-- and ownership preservation.
theorem protectedBatch_sound (u : User) (xs : RequestBatch) (r r' : Resource)
    (h : protectedBatch u xs r = some r') :
    r' = runBatch xs r ∧ BatchAllowed u xs r ∧ r'.owner = r.owner := by
  sorry

-- Completeness rules out the useless implementation that always rejects.
theorem protectedBatch_complete (u : User) (xs : RequestBatch) (r : Resource)
    (h : BatchAllowed u xs r) :
    protectedBatch u xs r = some (runBatch xs r) := by
  sorry

theorem protectedBatch_accepts_iff (u : User) (xs : RequestBatch) (r : Resource) :
    protectedBatch u xs r = some (runBatch xs r) ↔ batchCanRun u xs r = true := by
  sorry

-- Checked composition includes failure propagation, not just the success case.
theorem protectedBatch_append (u : User) (xs ys : RequestBatch) (r : Resource) :
    protectedBatch u (appendBatch xs ys) r =
      (match protectedBatch u xs r with
       | none => none
       | some mid => protectedBatch u ys mid) := by
  sorry

-- If a user is the owner of a resource, then the user is allowed to act on the batch.
theorem owner_batchAllowed (u : User) (xs : RequestBatch) (r : Resource)
    (howner : IsOwner u r) : BatchAllowed u xs r := by
  sorry

-- Prove `appended_length_zero_iff`: batch length of an appended batch is 0 iff both batches are empty.

end BatchVerification

#eval (protectedBatch User.bob exampleBatch privateDoc).map Resource.body
#eval (protectedBatch User.eve exampleBatch privateDoc).map Resource.body

namespace ClassicalExamples

/-! `classical` locally makes classical reasoning available, including decisions for
arbitrary propositions. The problem below is using a `noncomputable`
decision or chosen witness to produce observable data.
-/

-- A `classical` proof may use the law of excluded middle: for every proposition, either this proposition or its negation is true. This means that you can have a proof of a proposition without returning executable data.
example (policy : Resource → Prop) (r : Resource) : policy r ∨ ¬ policy r := by
  exact Classical.em (policy r)

theorem readerExists (r : Resource) : ∃ u : User, Allowed u Action.read r := by
  exact ⟨r.owner, PolicyLogic.ownerMayRead r.owner r rfl⟩

/- We choose a reader. -/
noncomputable def chosenReader (r : Resource) : User :=
  Classical.choose (readerExists r)

-- `Classical.choose` takes an existence proof in `Prop` and returns a witness in `Type`. It specifies a witness which satisfies the property provided in the proposition. In particular, suppose you have `p : Prop` and `h : ∃ x, p x`, that is, there exists an `x` for which `p` is `true`, then `Classical.choose x` will return such an `x` to you, without specifying how the `x` was obtained. Now suppose you have a `y` for which `p y`, then it is not necessary that `x = y`. `Classical.choose_spec h` will give you `p x`, that is, the fact that `x` satisfies `p`.

-- Remove the `noncomputable` tag from the def above. What error do you get?

#eval chosenReader publicDoc
-- The eval above shows that noncomputable defs cannot be evaluated.

#check chosenReader publicDoc
-- Note: type checking is not evaluation!


-- Prove this using `Classical.choose_spec`
theorem chosenReader_allowed (r : Resource) : Allowed (chosenReader r) Action.read r := by
  sorry

-- Think about this example. Can you prove it?
example : chosenReader r = r.owner := by
  sorry
-- Do you notice something else about this example?

end ClassicalExamples

namespace FinalWorkflow

theorem verifiedOwnerWorkflow (u : User) (xs ys : RequestBatch) (r : Resource)
    (howner : IsOwner u r) :
    ∃ output : {s : Resource // IsOwner u s},
      protectedBatch u (appendBatch xs ys) r = some output.val ∧
      protectedBatch u xs r = some (runBatch xs r) ∧
      protectedBatch u ys (runBatch xs r) = some output.val ∧
      output.val = runBatch ys (runBatch xs r) ∧
      output.val.owner = r.owner ∧
      BatchAllowed u (appendBatch xs ys) r ∧
      batchCanRun u (appendBatch xs ys) r = true ∧
      batchLength (appendBatch xs ys) = batchLength xs + batchLength ys ∧
      (batchLength (appendBatch xs ys) = 0 ↔
        xs = RequestBatch.empty ∧ ys = RequestBatch.empty) ∧
      canAccess u Action.read output.val = true ∧
      Allowed (ClassicalExamples.chosenReader output.val) Action.read output.val := by
    sorry

end FinalWorkflow

-- There is a way to check the axioms a theorem uses / is dependent on.
#print axioms AccessControl.FinalWorkflow.verifiedOwnerWorkflow

-- If you see `sorryAx`, that means something is unproved.
-- Lean has three standard axioms:
-- Law of excluded middle: `Classical.choice.{u} {α : Sort u} : Nonempty α → α`
-- Propositional extensionality asserts that if propositions `a` and `b` are logically equivalent (that is, if `a` can be proved from `b` and vice versa), then `a` and `b` are equal, meaning `a` can be replaced with `b` in all contexts: `propext {a b : Prop} : (a ↔ b) → a = b`
-- Quotient axiom asserts the equality of elements related by the quotient's relation. The relation r does not need to be an equivalence relation to use this axiom. When r is not an equivalence relation, the quotient is with respect to the equivalence relation generated by r: `Quot.sound.{u} {α : Sort u} {r : α → α → Prop} {a b : α} : r a b → Quot.mk r a = Quot.mk r b`
-- There are ways to build axioms, we shall see that next week!

end AccessControl
