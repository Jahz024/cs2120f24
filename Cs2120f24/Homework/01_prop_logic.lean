import «Cs2120f24».Lectures.«02_prop_logic».formal.syntax
import «Cs2120f24».Lectures.«02_prop_logic».formal.semantics
import «Cs2120f24».Lectures.«02_prop_logic».formal.properties

/-!
CS 2120-002 F24 Homework #1: Propositional Logic
-/

namespace cs2120f24
open PLExpr


/-!
First, we define three propositional variables: Wet, Rain, and
Sprink, following the exmaple presented in class, with shorter
but still suggestive variable names, for ease of reading and
writing propositional logic expressions -- aka "propositions."

Your first task is to be sure you understand the notation we're
using. Consider the first line below:

def wet : PLExpr := {⟨0⟩}.

We break that down here. *Study this material.* It's not very
difficult, and you really do need to understand this notation
easily going forward.

def       -- keyword to bind name (wet) to a value (here {⟨0⟩})
: PLExpr  -- defines the type of value to be bound (here, PLExpr)
:=        -- separates "variable type declaration" from value
⟨ 0 ⟩     -- Lean-defined shorthand for (BoolExpr.mk 0)
{ ... }   -- our concrete syntax for PLExpr.var_expr.mk

The parts here that might cause some conflusion are ⟨ _ ⟩ and
{ _ }. First, the funny angle brackets are not on your keyboard;
they are special characters you need to enter in VSCode using
\< and \>. Enter these strings then a space to get these
characters. Second, a "structure" type in Lean is an inductive
type with *just one constructor* that defaults in name to "mk".
An example is BoolVar.mk. Rather than typing that constructor
expression each time you want a new value *of *any* structure
type), you can use this this angle bracket notation instead.
Lean just has to be able to figure out from context what type
of object is needed so that it can translate ⟨ ⟩ into a call
to the "mk" constructor for the right structure type.

Next, the {...} notation is a concrete syntax notation that we
ourselves have defined (in syntax.lean) for PLExpr.var_expr. It
in turn expects a BoolVar argument, which is how Lean know what
constructor to use for the ⟨_⟩ notation: namely BoolVar.mk.

The reading should help with the ⟨_⟩ notation. And you should be
able to understand how we've defined { } as a concrete syntax in
syntax.lean.
-/


def wet : PLExpr := {⟨0⟩}
def rain : PLExpr := {⟨1⟩}
def sprink : PLExpr := {⟨2⟩}


/-!
ENGLISH TO FORMAL PROPOSITIONAL LOGIC

Problem #1: 50 points. Using the variable names, wet, rain,
and sprink, write propositional logic expressions for each of
the given propositions (expressions) written in natural language.
For example, "it's raining and the springler is running" would be
(rain ∧ sprink). Wtite your expressions in place of the sorrys.

Once you've written your expression, add a line of "code" to
check your expressions for *validity*. Then, if the expression
is *not* valid, in English explain very briefly a situation in
which the proposition is not true. For example, you know that
raining ∧ sprinking is not valid, and in this case it would be
ok to write "if it's not raining then this proposition is false"
-/

/-!
A. It's raining and the sprinkler is running.
-/
def formal_0 : PLExpr := rain ∧ sprink

example : ¬ valid formal_0 := by tauto

-- This is not valid b/c it's false when it's not raining or the sprinkler is not running.



/-!
B. If it's raining then it's raining or the sprinkler's running.
Rememver to use \=> for the implies "connective" (expression
builder).
-/
def formal_1 : PLExpr := rain ⇒ (rain ∨ sprink)

example : valid formal_1 := by tauto

-- This  is valid, so we don't need a counterexample.

/-!
C. If the sprinkler's running then it's raining or it's sprinkling.
-/
def formal_2 : PLExpr := sprink ⇒ (rain ∨ sprink)

example : valid formal_2 := by tauto

-- This is valid, so we don't need a counterexample.

/-!
D. Whenever it's raining the streets are wet. You can express the same
idea as "if it's raining then the streets are wet." Be sure you see that
these two English-language phrases mean the same thing. You will want to
use the "whenever" form sometimes and the "if then" form sometimes when
writing logic in English.
-/
def formal_3 : PLExpr := rain ⇒ wet

example : ¬ valid formal_3 := by tauto

-- This is not valid b/c it's false when it's raining but the streets are not wet
-- (e.g it just started raining and not enough time has passed to get the street's wet yet).


/-!
E. Whenever the sprinkler's running the streets are wet.
-/
def formal_4 : PLExpr := sprink ⇒ wet

example : ¬ valid formal_4 := by tauto

-- This is not valid b/c it's false when the sprinkler is running but the streets are not wet
--  (e.g the sprinkler just started and the water hasn't reached the street yet).

/-!
Here's an example, from class, of a proposition built up in
part from several smaller *implies* propositions. This is a
reminder to help you with any similar cases that follow.

If it's raining or the sprinkler's running, then if whenever
it's raining then the streets are wet, then if whenever the
sprinkler's running then the streets are wet, then the streets
are wet.

Add a check for the validity of this expression. The *example*
keyword in Lean asks Lean to check a term without binding a
name to it.
-/
example : PLExpr :=
  (rain ∨ sprink) ⇒
  (rain ⇒ wet) ⇒
  (sprink ⇒ wet) ⇒
  wet


-- Write your validity check here


/-!
If (whenever it's raining, the streets are wet), then (whenever the
streets are wet it's raining.)
-/
def formal_5 : PLExpr := (rain ⇒ wet) ⇒ (wet ⇒ rain)

example : ¬ valid formal_5 := by tauto


/-!
If (whever it's raining then bottom)/false, then (it's not raining).
-/
def formal_7 : PLExpr := (rain ⇒ false) ⇒ (¬rain)

example : valid formal_7 := by tauto

-- This proposition is valid, so we don't need a counter example.


/-!
If whenever it's raining the streets are wet, then whenever it's not
raining the streets are not wet.
-/
def formal_8 : PLExpr := (rain ⇒ wet) ⇒ ((¬rain) ⇒ (¬wet))

example : ¬ valid formal_8 := by tauto

-- This is not valid b/c it's false when it's not raining but the streets are still wet
-- (e.g if it rained earlier but has stopped, or if the sprinkler is running).

/-!
If whenever it's raining the streets are wet, then whenever the
streets are not wet, it's not be raining.
-/
def formal_9 : PLExpr := (rain ⇒ wet) ⇒ ((¬wet) ⇒ (¬rain))

example : valid formal_9 := by tauto

-- This proposition is valid, so we don't need a counter example

/-!
PROPOSITIONAL LOGIC TO ENGLISH: 50 points

For each of the following propositions in propositional logic,
open up some space after the proposition, in a comment block
give a corresponding English-language form of that proposition;
then *think* about whether the proposition is valid or not; and
add a validity check using our validity checker. Finally, if
a proposition is not valid, in English describe a case where
the proposition is not true. Notice but don't worry (yet) about
the funny names we assign to these propositions.
-/

def and_intro := sprink ⇒ rain ⇒ sprink ∧ rain

/*
if it's sprinkling, then if it's raining, then it's both sprinkling and raining.
*/

example : valid and_intro := by tauto

-- valid b/c if both conditions are true, we can say both are happening at once

def and_elim_left := sprink ∧ rain ⇒ sprink

/*
if it's sprinkling and raining, then it's sprinkling.
*/

example : valid and_elim_left := by tauto

-- valid b/c if both are true, we can just focus on one part

def and_elim_right := sprink ∧ rain ⇒ rain

/*
if it's sprinkling and raining, then it's raining.
*/

example : valid and_elim_right := by tauto

-- valid b/c same as and_elim_left, but now for the rain part

def or_intro_left := sprink ⇒ sprink ∨ rain

/*
if it's sprinkling, then it's either sprinkling or raining.
*/

example : valid or_intro_left := by tauto

-- valid b/c we can add in another option when we know one is true

def or_intro_right := rain ⇒ sprink ∨ rain

/*
if it's raining, then it's either sprinkling or raining.
*/

example : valid or_intro_right := by tauto

-- valid b/c works like or_intro_left but from the rain side

def or_elim := rain ∨ sprink ⇒ (rain ⇒ wet) ⇒ (sprink ⇒ wet) ⇒ wet

/*
if it's raining or sprinkling, and if rain makes it wet, and if sprinkling makes it wet,
then it's wet.
*/

example : valid or_elim := by tauto

-- valid b/c we look at both scenarios and see they lead to the same result

def not_intro := (sprink ⇒ ⊥) ⇒ ¬sprink

/*
if sprinkling leads to a contradiction, then it's not sprinkling.
*/

example : valid not_intro := by tauto

-- valid b/c if sprinkling can't happen without breaking logic, then it can't happen

def not_elim := ¬¬sprink ⇒ sprink

/*
if it's not not sprinkling, then it's sprinkling.
*/

example : valid not_elim := by tauto

-- valid b/c this is just removing the double negation

def imp_intro := sprink ⇒ wet ⇒ (sprink ⇒ wet)

/*
if it's sprinkling, then if it's wet, then sprinkling implies wetness.
*/

example : valid imp_intro := by tauto

-- valid b/c this is how we set up implications logically

def imp_elim := (sprink ⇒ wet) ⇒ sprink ⇒ wet

/*
if sprinkling implies wetness, then if it's sprinkling, it's wet.
*/

example : valid imp_elim := by tauto

-- valid b/c if "if p then q" and "p" are true, then "q" has to be true too (modus ponens)

def equiv_intro := (sprink ⇒ wet) ⇒ (wet ⇒ sprink) ⇒ (sprink ↔ wet)

/*
if sprinkling implies wetness, and wetness implies sprinkling, then
sprinkling is equivalent to wetness.
*/

example : ¬ valid equiv_intro := by tauto

-- not valid b/c wetness might be caused by something else

def equiv_elim_left := (sprink ↔ wet) ⇒ (sprink ⇒ wet)

/*
if sprinkling is equivalent to wetness, then sprinkling implies wetness.
*/

example : valid equiv_elim_left := by tauto

-- valid b/c from an equivalence, we can get one direction of implication

def equiv_elim_right := (sprink ↔ wet) ⇒ (wet ⇒ sprink)

/*
if sprinkling is equivalent to wetness, then wetness implies sprinkling.
*/

example : valid equiv_elim_right := by tauto

-- valid b/c same as equiv_elim_left but for the other direction

def affirm_disjunct := (wet ∨ sprink) ⇒ wet ⇒ ¬sprink

/*
if it's wet or sprinkling, and it's wet, then it's not sprinkling.
*/

example : ¬ valid affirm_disjunct := by tauto

-- not valid b/c it can be wet and sprinkling at the same time

def affirm_consequent := (sprink ⇒ wet) ⇒ wet ⇒ sprink

/*
if sprinkling implies wetness, and it's wet, then it's sprinkling.
*/

example : ¬ valid affirm_consequent := by tauto

-- not valid b/c this is a logical mistake; there could be other reasons it's wet

def deny_antecedent := (sprink ⇒ wet) ⇒ ¬sprink ⇒ ¬wet

/*
if sprinkling implies wetness, and it's not sprinkling, then it's not wet.
*/

example : ¬ valid deny_antecedent := by tauto

-- not valid b/c there could be other things making it wet, not just sprinkling



/-
Are they valid?
-/

#eval! is_valid  and_intro
#eval! is_valid  and_elim_left
#eval! is_valid  and_elim_right

#eval! is_valid  or_intro_left
#eval! is_valid  or_intro_right
#eval! is_valid  or_elim          -- oops

#eval! is_valid  not_intro
#eval! is_valid  not_elim

#eval! is_valid  imp_intro
#eval! is_valid  imp_elim         -- oops

#eval! is_valid  equiv_intro      -- oops
#eval! is_valid  equiv_elim_left
#eval! is_valid  equiv_elim_right

#eval! is_valid  affirm_disjunct
#eval! is_valid  affirm_consequent
#eval! is_valid  deny_antecedent

end cs2120f24
