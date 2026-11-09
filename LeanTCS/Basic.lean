/-
Welcome to Lean 101! Today, we try to cover some basic concepts, such as dependent type theory, the foundation of Lean. We will also explore the different kinds of structures that exist in Lean.
-/

-- To begin with, click Alt+Z or Option+Z (for Mac users). This will ensure that all text will be visible within your view.

-- If you have Lean compiled and working properly, you should now see `No info found` on the right hand side of your screen. You might see some orange vertical bars which should rapidly disappear, leaving behind some red dots. If this is not the case, please ask for help!
-- The right hand side is called the InfoView, its output changes line by line, and dependent on the position of your cursor.
-- As an example, click on line 10. Move through the line. When does the message in the InfoView change?

-- What is a Type? One might think of a type as a set, but with different membership qualities. An element of a set can belong to different sets, but an element in Lean has a unique type. Check out (pun intended) one of the fundamental types in Lean, the natural numbers. `#check` shows you the type of the given object. In this case, naturals are of type Type.
#check Nat

-- Lets check out the definition of the natural numbers. The `#print` command shows this to you.
#print Nat
-- The definition is an inductive one: Nat has 2 constructors - one is 0, and the other is the successor function

-- Here is 0
#check 0
-- Can you check 1?

#check -1
#check (0 : Nat) + (-1)
#check (0 : Int) + (-1)
#check 0 - 1
#eval 0 - 1

-- Here is proof of how 1 is defined.
example: 0 + 1 = 1 := rfl

def hello := "world"
-- We are making a definition above, which is called `hello`. In general, definitions are of the following form:
-- def Identifier : Type of Identifier := Definition
-- If I write
-- def A : B := C
-- this means that I am defining C to be of type B (so it must follow the rules of B), and naming it A.
-- Can you now remake the definition of hello using the same structure? Do you get any errors? How do you resolve them? Any guesses as to why the definition above still works?

-- Your answer


#print String

abbrev edges := Nat × Nat

structure graph where
vertices : Nat
edges : Nat × Nat
