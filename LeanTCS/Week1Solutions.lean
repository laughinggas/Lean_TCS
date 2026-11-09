/-
Welcome to Lean 101! Today, we try to cover some basic concepts, such as dependent type theory, the foundation of Lean. We will also explore the different kinds of structures that exist in Lean.
-/

-- To begin with, click Alt+Z or Option+Z (for Mac users). This will ensure that all text will be visible within your view.

-- If you have Lean compiled and working properly, you should now see `No info found` on the right hand side of your screen. You might see some orange vertical bars which should rapidly disappear, leaving behind some red dots. If this is not the case, please ask for help!
-- The right hand side is called the InfoView, its output changes line by line, and dependent on the position of your cursor.
-- As an example, click on line 16. Move through the line. When does the message in the InfoView change?

--------------------------------------------------------------------------------
-- SECTION 1: TYPES & COMMANDS (#check, #print, #eval)
--------------------------------------------------------------------------------

-- What is a Type? One might think of a type as a set, but with different membership qualities. An element of a set can belong to different sets, but an element in Lean has a unique type. Check out (pun intended) one of the fundamental types in Lean, the natural numbers. `#check` shows you the type of the given object. In this case, naturals are of type Type.
#check Nat

-- Lets see the definition of the natural numbers. The `#print` command shows this to you.
#print Nat
-- The definition is an inductive one: Nat has 2 constructors - one is 0, and the other is the successor function (`Nat.succ`).

-- Here is 0. By default, Lean infers non-negative integers as natural numbers.
#check 0

-- Can you check 1?
#check 1

-- What do you think is the type of negative numbers? Check it out. Hover on different writings in the InfoView, what do you see?
#check -1

-- Hovering on words gives us descriptions of said words in Lean, and their type.

-- We can explicitly tell Lean what type we want a term to be using type annotations `(term : Type)`.
-- Let's observe how natural numbers and integers behave under operations:
#check (0 : Nat) + (-1)
-- Why does the above code throw an error?
-- Because we tell Lean that 0 has type Nat, so it takes addition over Nat, and is now expecting a Nat, but gets -1. Looking at - it looks for negation over Nat, but this does not exist.

-- Notice how Lean coerces 0 to Int because (-1) is Int.
#check 0 + -1
-- What is coercion? It is a map from one type to another. In this case, the coercion is the natural map Nat → Int. This is a part of type theory: if `a` is of type `T`, then `a` cannot be a part of type `T'`. However, if there is a coercion `f` from `T` to `T'`, then one can write `(a : T')` instead of `f a`. Since the coercion from Nat to Int is very fundamental, there is no obvious distinction between `a : Nat` and `a : Int`.

-- What happens when you subtract in natural numbers?
#check 0 - 1
-- Use `#eval` to check the evaluated value.
#eval 0 - 1
-- Any guesses why this is happening?
-- Subtraction is defined over Nat as the following: for m ≤ n, m - n is 0.

-- Can you obtain the expected answer?
#eval (0 - 1 : Int)

-- Lesson: Be careful with types!

-- `#eval` computes/evaluates expressions, while `#check` only inspects their types.
-- Let us consider product types.
#check (5, 9)
#eval (5, 9, 3).1
#eval (5, 9, 3).2
-- What does this tell you about how Lean works products? Can you write the correct statement to obtain 9 from (5, 9, 3)?
-- Nat × Nat × Nat is actually Nat × (Nat × Nat), that is, Lean is left-associative. So (5, 9, 3) is actually stored as (5, (9, 3)).

#eval (5, 9, 3).2.1


-- Here is proof of how 1 is defined (1 is shorthand for `Nat.succ 0`, or `0 + 1`). `rfl` stands for reflexivity (equality by definition).
example : 0 + 1 = 1 := by
  rfl
  rfl
-- The double blue ticks on the left imply that Lean's kernel is happy with the given proof. The keyword `by` signifies the start of the proof (in something called "Tactic Mode").
-- Notice how the InfoView changes based on where your cursor is. Put it on multiple points on line 51, and then line 52. After `by` on line 51, you should see the goal in the InfoView, given to the right of the `⊢` symbol. On line 52, `Goals accomplished!` is another sign that the proof is complete. Try adding another `rfl` on line 53 (maintaining the indentation). What do you get?
-- An error which says: No goals to be solved
-- Because the goals have been accomplished

--------------------------------------------------------------------------------
-- SECTION 2: DEFINITIONS, STRINGS, AND TYPE INFERENCE
--------------------------------------------------------------------------------

def hello := "world"
-- We are making a definition above, which is called `hello`. In general, definitions are of the following form:
-- def Identifier Inputs : Type of Identifier := Definition
-- If I write
-- def A ... : B := C
-- this means that I am defining C to be of type B (so it must follow the rules of B), and naming it A, with hypotheses or input ... . We will discuss the hypotheses/inputs ahead.
-- Can you now remake the definition of hello using the same structure? Do you get any errors? How do you resolve them? Any guesses as to why the definition above still works?
def hello : String := "world"
-- yes, I get an error which says: "hello" has already been declared. This is because every def must have a unique identifier/name.
-- the def above works because Lean can infer the type of the definition

-- Can you now check the definition of String?

-- Notice that you can hover over String to see a natural language description of it. Another way is to Ctrl+click on String. This action will take you to the source file. Don't worry if you don't understand the definition!

--------------------------------------------------------------------------------
-- SECTION 3: FUNCTIONS AND LAMBDAS
--------------------------------------------------------------------------------

-- Lets define functions in Lean. Here is a function that adds 1 to a natural number:
def addOne (n : Nat) : Nat := n + 1
-- The (n : Nat) is the input.

#check addOne
#eval addOne 5

-- We can also define functions by:
def addOne' : Nat → Nat := fun n => n + 1
-- This is called Lambda abstraction.

#eval addOne' 5

-- Write a function `double` that takes a `Nat` and multiplies it by 2.
def double (n : Nat) := 2 * n

-- Lets evaluate it!
#eval double 7

-- Here are some more examples of an evaluation of a function
#eval (fun x : Nat => x + 5) 10

#check fun x : Nat => fun y : Bool => if not y then x + 1 else x + 2

#eval (fun x : Nat => fun y : Bool => if !y then x + 1 else x + 2) 5 True

-- Some mathematically common examples of operations of functions are:
def f (n : Nat) : String := toString n

def g (s : String) : Bool := s.length > 0

#check fun x => g (f x)

#check fun x : Nat => true
-- Notice that you have a warning above. What does this warning mean?
-- It means that x has not been actually used in the output of the function.

-- Is this the same as the above definition?
#check fun _ => true
-- No, because the type has not been specified.

-- What about these two definitions?
#eval (fun _ => true) 10
-- yes, this is the same, since the type inferred by Lean is Nat

#eval (fun _ => true) 1.2
-- no, since the type inferred by Lean is Real

-- What is happening here is type abstraction - Lean is looking at the information you give it and inferring the type of the input from this info.

-- You can pass functions as parameters and by giving them names f and g you can then use those functions in the implementation:
#check fun (g : List Nat → Bool) (f : Nat → List Nat) (x : Nat) => g (f x)

-- You can also pass types as parameters:
#check fun (α β γ : Type) (g : β → γ) (f : α → β) (x : α) => g (f x)
-- Notice that you can give multiple parameters for the same type.

--------------------------------------------------------------------------------
-- SECTION 4: TYPES & PROPOSITIONS AS TYPES
--------------------------------------------------------------------------------

-- In Lean's foundation (Dependent Type Theory), Types themselves have types!
#check Nat      -- Type
#check Bool     -- Type
#check Type     -- Type 1  (Lean has an infinite hierarchy of universes: Type 0, Type 1, Type 2, ...)
-- Check the type of Type 3
#check Type 3

-- What about mathematical statements / propositions?
-- In Lean, a mathematical proposition (like "2 + 2 = 4") also have types.
#check 2 + 2 = 5
#eval 2 + 2 = 5
-- `Prop` is the type of all logical statements.
-- A proof of a proposition `P` is simply a term/element of type `P`. In other words, lets say we have a proposition called `h` which says that 2 + 2 = 5. Then `h` has type `Prop`. You can imply that a false statement can also be a proposition then.
#check False
-- Any element of type `h` is a proof of `h`. Moreover, in the Lean universe, `h` is a subsingleton: any two elements `a` and `b` of type `h` must be equal. In other words, propositions have definitional proof irrelevance: two proofs of h / two elements of type `h` are definitionally equal in Lean.
-- This follows from the Curry-Howard Isomorphism ("Propositions as Types").

def two_plus_two_is_four : 2 + 2 = 4 := by
  rfl
-- Here, two_plus_two_is_four is the proof (reflexivity) of the proposition 2 + 2 = 4.
#check two_plus_two_is_four

-- We generally use the keyword theorem instead of def, but the underlying meaning (and the way to write) is the same!
theorem two_plus_two_is_four' : 2 + 2 = 4 := by
  rfl

-- This theorem will be "remembered" by Lean, and can then be used in proving other theorems.
example : 2 + 2 = 4 := by
  rw [two_plus_two_is_four']
-- The tactic `rw` above is shorthand for rewrite: it tries to find the LHS from the given theorem, `two_plus_two_is_four'`, and replaces the first occurence of this in the goal with the RHS of `two_plus_two_is_four'`. If you want to go from RHS to LHS instead, you can use `←` (typed as \+l).

-- For an unnamed theorem, we use the keyword example. Note that this will not be remembered by Lean.
example : 4 = 2 + 2 := by
  rfl
-- Can you try to solve this using `two_plus_two_is_four'`?

example : 4 = 2 + 2 := by
  rw [← two_plus_two_is_four']

-- Consider the following def which adds an element `a` to the end of a list `h` containing elements of type `α`.
def conning (α : Type) (h : List α) (a : α) := List.cons a h
-- Notice that both `h` and `a` are "dependent" on the type `α`, which is also an input. This is what dependent type theory means: types can depend on parameters! For a more detailed explanation, look at Section 2.8 here: https://lean-lang.org/theorem_proving_in_lean4/Dependent-Type-Theory/#dependent-type-theory .

--------------------------------------------------------------------------------
-- SECTION 5: TACTICS & PROVING
--------------------------------------------------------------------------------

-- Give proofs for the two theorems below. The yellow squiggly lines under the theorem name give you a warning. Remove sorry from the first theorem and click on by: what does it say?
-- It gives an error of unsolved goals.

-- `sorry` and `admit` are ways to tell Lean: assume I have a proof of this theorem, so that Lean does not throw an error at you.
-- A lemma for your consideration: `Nat.add_zero`

theorem simple_addition (n m : Nat) (h : m = 0) : n + 0 = n + m := by
  rw [Nat.add_zero, h, Nat.add_zero]

-- Try to replace `sorry` and `admit` with proofs. Don't be afraid if you see errors! :)

theorem add_zero_left (n : Nat) : 0 + n = n := by
  rw [Nat.add_comm, Nat.add_zero]

-- Can't solve the second? What is the source of the problem?
-- Hint: try using the theorem `Nat.add_comm`.

-- Let us try basic logical reasoning with tactics:
-- `intro` introduces hypotheses into the context.
-- `exact` provides the exact proof required.
-- `apply` applies a theorem or implication.

theorem of_implies (P Q : Prop) (hP : P) (hPQ : P → Q) : Q := by
  -- Look at the InfoView. We have hypotheses hP and hPQ, and goal Q, ie. we want a proof of Q.
  apply hPQ
  -- The goal changed to P, since we applied hPQ, which says: if you have a proof of Q, you have a proof of P. We do have a proof of P in the hypothesis.
  exact hP

-- Remember that Lean is smart with inferring what is left blank. Notice in `of_implies` that when you give `hP` and `hPQ`, you are automatically giving extra information: `P` and `Q`. In the example below, I am replacing `P` and `Q` with what are called placeholders, Lean fills them.
example (n : Nat)
    (hZero : n = 0)
    (hStep : n = 0 → n + 1 = 1) :
    n + 1 = 1 := by
  apply of_implies _ _ hZero hStep

-- In particular, for the sake of convenience, it might be nice not to have to type out `P` and `Q` every time you reference the above theorem. The way to do this is to make the parameters implicit, using the `{}` brackets.
theorem of_implies' {P Q : Prop} (hP : P) (hPQ : P → Q) : Q := by
  apply hPQ
  apply hP

example (n : Nat)
    (hZero : n = 0)
    (hStep : n = 0 → n + 1 = 1) :
    n + 1 = 1 := by
  apply of_implies' hZero hStep

-- Now what if we wanted to make a def using `P` and `Q`? You can use the `@` feature, which denotes the same (theorem/def/function) with all the arguments made explicit.
def myRule := @of_implies' True True

#check myRule

-- Write a theorem proving that if P implies Q and Q implies R, then P implies R.
-- Hint: You might want to use `intro` in the proof. The `intro` tactic introduces a hypothesis and adds a name. For example, if your goal says `∀ x y, p x y`, then `intro x y` introduces two variables x and y into the context.
theorem pip {P Q R : Prop} (h1: P → Q) (h2: Q → R) : P → R := by
  intro hP
  apply h2
  apply h1
  apply hP

--------------------------------------------------------------------------------
-- SECTION 6: CASES — USING THE POSSIBLE WAYS TO BUILD A PROOF
--------------------------------------------------------------------------------

-- `P ∨ Q` means "P or Q"; `P ∧ Q` means "P and Q".
-- Type these symbols with \or and \and, followed by a space.
-- A proof h : P ∨ Q comes from one of two constructors:
-- `Or.inl hP`, where hP : P, or `Or.inr hQ`, where hQ : Q.
-- To USE h, `cases h` splits the proof into these two possibilities.
-- To PROVE an or-statement, use `Or.inl` or `Or.inr` instead.

-- If either P or Q implies R, then P ∨ Q implies R.
example (P Q R : Prop) (h : P ∨ Q) (hPR : P → R) (hQR : Q → R) : R := by
  cases h with
  | inl hP =>
    -- In this branch we have hP : P; the goal is R.
    exact hPR hP
  | inr hQ =>
    -- In this branch we have hQ : Q; the goal is still R.
    exact hQR hQ

-- Move the cursor through each branch and compare the InfoView contexts.
-- `inl` and `inr` are constructor names; hP and hQ are names we choose.
-- Each branch must prove the same original goal using its own assumptions.

-- A proof h : P ∧ Q has ONE constructor, containing BOTH proofs.
-- Here `cases` unpacks the proof rather than creating two alternative goals.
example (P Q : Prop) (h : P ∧ Q) : Q := by
  cases h with
  | intro hP hQ =>
    exact hQ

-- Alternatively, we have:
example (P Q : Prop) (h : P ∧ Q) : Q := by
  exact h.2

-- `cases` also works on data. Bool has two constructors, false and true.
example (b : Bool) : (!(!b)) = b := by
  cases b with
  | false => rfl
  | true => rfl

-- This is a case split, not induction: splitting a natural number gives
-- zero and successor cases, but does not give an induction hypothesis.

-- Swap the alternatives. Replace sorry with a cases proof.
-- Hint: use `Or.inr` and `Or.inl`.
example (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
  cases h with
  | inl h =>
    apply Or.inr h
  | inr h =>
    apply Or.inl h

-- Unpack an and-statement and return its first component.
example (P Q : Prop) (h : P ∧ Q) : P := by
  exact h.1

--------------------------------------------------------------------------------
-- SECTION 7: SIMP — SIMPLIFYING GOALS AND HYPOTHESES
--------------------------------------------------------------------------------

-- `simp` repeatedly uses standard simplification rules (lemmas tagged
-- [simp]), along with basic reductions. It can close a goal completely,
-- or leave a simpler goal for your next tactic. Always inspect the InfoView.
-- Unlike a single `rw [h]`, simp may apply many rules, repeatedly, throughout
-- the target. It is not a general search for any mathematical proof.

example (n : Nat) : 0 + n + 0 = n := by
  simp

example (P : Prop) : (P ∧ True) ↔ P := by
  simp

-- `simp [h]` adds h to the simplification rules for this invocation.
-- When h is an equality, it can rewrite expressions using that equality.
example {n : Nat} (h : n = 0) : n + 3 = 3 := by
  simp [h]

-- When h proves a proposition, simp can simplify that proposition to True.
-- When h proves its negation, simp can simplify it to False.
example {n : Nat} (h : n = 0) : (if n = 0 then 7 else 9) = 9 → False := by
  simp [h]

example (n : Nat) (h : n ≠ 0) : (if n = 0 then 7 else 9) = 9 := by
  simp [h]

-- The brackets can contain several facts: `simp [h1, h2]`.
-- They can also contain a definition name, asking simp to unfold it.
example : addOne 4 = 5 := by
  simp [addOne]

-- `simp at h` simplifies the TYPE of hypothesis h rather than the goal.
-- Compare this with `simp [h]`, which uses h to simplify the goal.
example (P : Prop) (h : P ∧ True) : P := by
  simp at h
  -- Now h : P.
  exact h

-- `simp?` simplifies like simp and reports a suggested `simp only [...]`
-- invocation in the InfoView. It proves the goal here, as simp would.
-- Click the suggestion to replace simp? with the proposed tactic.
-- `simp only [...]` restricts the named rewrite rules instead of using
-- the whole default simp set (basic simplifier reductions still run).
-- The exact suggestion can depend on the Lean version and imported lemmas.
example (n : Nat) : 0 + n = n := by
  simp only [Nat.zero_add]

-- Try changing the previous line to `simp only [Nat.zero_add]`.
-- `simp? [h]` also works: it includes h and suggests sufficient rules.
example (n : Nat) (h : n = 0) : n + 3 = 3 := by
  simp only [h, Nat.zero_add]

-- Prove these using simp.

example (n : Nat) : 0 + (n + 0) = n := by
  simp

example {n m : Nat} (h : n = m) : n + 0 = m := by
  simp [h]

example {P : Prop} (h : True ∧ P) : P := by
  simp at h
  apply h

example (n : Nat) : n + 0 = n := by
  simp only [Nat.add_zero]

example {u v : Nat} (h : (u = 2 ∧ v = 3) ∨ (u = 3 ∧ v = 2)) :
    (v = 2 ∧ u = 3) ∨ (v = 3 ∧ u = 2) := by
  cases h with
  | inl h =>
    apply Or.inr
    simp [h]
  | inr h =>
    apply Or.inl
    simp [h]

-- Reference: https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/

--------------------------------------------------------------------------------
-- SECTION 8: STRUCTURES, ALGEBRAIC DATA TYPES & ALIASES
--------------------------------------------------------------------------------

-- `abbrev` creates an alias (a shorthand name for an existing type).
abbrev edges := Nat × Nat
-- A pair of natural numbers representing an edge (u, v).

#check ((1, 2) : edges)

-- `structure` allows us to bundle data together (like objects or structs in other languages).
-- Defining a structure introduces a completely new type to Lean that can't be reduced to any other type. This is useful because multiple structures might represent different concepts that nonetheless contain the same data. For instance, a point might be represented using either Cartesian or polar coordinates, each being a pair of floating-point numbers. Defining separate structures prevents API clients from confusing one for another.
structure Graph (Vertices : Type) where
  Edges : Vertices → Vertices → Prop
  IsSymm : ∀ u v, Edges u v → Edges v u

-- Let's create an instance of a `graph`:
def myFirstGraph : Graph (Fin 5) := {
  Edges := fun u v => if (u == 0 ∧ v == 1) ∨ (u == 1 ∧ v == 0) then True else False,
  IsSymm := by
    -- Prove it!
    intro u v
    simp only [Fin.isValue, beq_iff_eq, ite_false_right, and_true]
    intro h
    cases h with
  | inl h =>
    apply Or.inr
    simp [h]
  | inr h =>
    apply Or.inl
    simp [h]
}

-- We can access the fields of a structure using dot notation:
#check myFirstGraph.IsSymm
#check myFirstGraph.Edges

-- Define a structure `Point2D` that contains two coordinates `x` and `y`, both of type `Float` or `Int`.
structure Point2D where
x : Int
y : Int

-- Now define the `origin`
def origin : Point2D :=
{ x := 0,
  y := 0 }

#eval origin.x

--------------------------------------------------------------------------------
-- SECTION 9: WRAPPING UP & MINI-PROJECT
--------------------------------------------------------------------------------

/-
RECAP OF WHAT WE LEARNED TODAY:
1. `#check` to inspect types, `#eval` to compute values, `#print` to inspect definitions.
2. The difference between `Nat` (non-negative) and `Int` (signed integers).
3. Defining terms with `def` and function application syntax.
4. Types as terms and Propositions as Types (`Prop`).
5. Writing interactive proofs using tactics (`by`, `intro`, `apply`, `exact`, `rfl`).
6. Case analysis (`cases`) and simplification (`simp`, `simp [h]`, `simp?`).
7. Custom data structures (`abbrev`, `structure`).

Final Exercise:
Define a structure `Person` with a `name : String` and `age : Nat`.
Then write a function `isAdult` that takes a `Person` and returns a `Bool` (`true` if age ≥ 18, `false` otherwise).
-/

-- Write a structure Person with fields name : String and age : Nat.
structure Person where
  name : String
  age : Nat

-- Define alice with name "Alice", age 20;
def alice : Person :=
{
  name := "Alice",
  age := 20
}

-- Define bob with name "Bob", age 17.
def bob : Person :=
{
  name := "Bob",
  age := 17
}

-- Inspect Person with #check and #print, then evaluate alice.name and bob.age.
#check Person
#print Person
#eval alice.name
#eval bob.age

-- Write an abbrev PersonPair for Person × Person, and make a pair of them.
abbrev PersonPair : Person × Person := (alice, bob)

-- Use projections and field notation to obtain Bob's name from the pair.
#eval PersonPair.2.name

-- Define isAdult which returns true exactly when age ≥ 18.
def isAdult (p : Person) : Bool := if p.age ≥ 18 then True else False

-- Define birthday : Person → Person, adding 1 to age.
def birthday : Person → Person := fun p =>
  {
    name := p.name,
    age := p.age + 1
  }

-- Evaluate isAdult alice and isAdult bob.
#eval isAdult alice  -- Expected: true
#eval isAdult bob    -- Expected: false
#eval isAdult (birthday bob)    -- Expected: true

-- try to prove the following
example (p : Person) : (birthday p).name = p.name := by
  rfl

example (p : Person) : (birthday p).age = p.age + 1 := by
  rfl

-- Hint: you might need `Nat.le_trans`. You may also use placeholders for any information you cannot currently fill.
example {p : Person} (h: isAdult p) : isAdult (birthday p) := by
  simp only [isAdult, ge_iff_le, decide_true, decide_false, Bool.ite_false_right, Bool.and_true,
    decide_eq_true_eq] at h
  simp only [isAdult, birthday, ge_iff_le, Nat.reduceLeDiff, decide_true, decide_false,
    Bool.ite_false_right, Bool.and_true, decide_eq_true_eq]
  apply Nat.le_trans _ h
  simp only [Nat.reduceLeDiff]
