namespace cs2120f24.constructiveLogic

/-! HOMEWORK #6. COUNTS FOR TWO ASSIGNMENTS.

This is an important homework. It gives you an
opportunity to work out many of the kinks in your
understanding of predicate logic and deductive
proofs in type theory. With P, Q, and R accepted
as propositions, you are to give proofs of all of
the identities from Library/propLogic/identities,
which I've rewritten in Lean for you. There's one
of these axioms that has no constructive proof (in
just one direction). You can just identify it.
-/


-- Suppse P, Q, and R are arbitrary propositions
axiom P : Prop
axiom Q : Prop
axiom R : Prop

/-!
Give proofs in Lean that each of the following identities
is valid. We already know they're classically valid as we
validated their propositional logic analogics semantically
using our model / validity checker. To get you started with
a concrete example, we prove the first one for you and give
a little English explanation after. You should od the same
for each proposition you prove.
-/


def andIdempotent   : P ↔ (P ∧ P) :=
Iff.intro
  -- forward direction: P → P ∧ P
  -- assume p : P, show P ∧ P
  (fun (p : P) => (And.intro p p))
  -- backwards direction: P ∧ P → P
  (fun (h : And P P) => (h.right))

/-!
In English: To prove P ↔ P ∧ P it will suffice
by iff intro, to have proofs, (fw : P → (P ∧ P))
and (bw : (P ∧ P) → P). Each is proved by giving
an argument to result proof construction.

Forward direction:

To prove P → P ∧ P, we show (by defining one) that
there is a function that turns any proof of P into
a proof of P ∧ P. There just one answer: ⟨ p, p ⟩.

Backward direction:

To prove P ∧ P → P, we assume a proof, (h : P ∧ P),
and are to show P. Either h.left or h.right will do.

Summary: Whether in formal logic or English language,
you have to know that to prove any equivance, P ↔ Q,
it is both sufficient and necessary that you have or
obtain proofs (fw : P → Q) and (bw: Q → P). With these
values, the term, (Iff.intro fw bw), is a proof of the
equivalence.
-/

-- What we are to prove is that ∨ is idemponent
-- That is, that for any P, P ↔ (P ∨ P).
def orIdempotent    : P ↔ (P ∨ P) :=
-- Proof: by application if iff.intro
-- iff intro
(
  Iff.intro
  -- Proof of P → P ∨ P
  (fun (p : P) => Or.inl p)
  -- Required proof of backward implication
  (fun (h : P ∨ P) =>
    (Or.elim
      h
      (fun p => p)
      (fun p => p)
    )
  )
)

-- proving and commutative: p ∧ q ↔ q ∧ p
-- forward: if p and q, reorder as q and p
-- backward: same logic, reorder q and p as p and q
def andCommutative  : (P ∧ Q) ↔ (Q ∧ P) :=
Iff.intro
  (fun (h : P ∧ Q) => And.intro h.right h.left)
  (fun (h : Q ∧ P) => And.intro h.right h.left)

-- proving or commutative: p ∨ q ↔ q ∨ p
-- forward: if p or q, reorder as q or p
-- backward: reorder q or p as p or q
def orCommutative   : (P ∨ Q) ↔ (Q ∨ P) :=
Iff.intro
  (fun (h : P ∨ Q) => Or.elim h (fun p => Or.inr p) (fun q => Or.inl q))
  (fun (h : Q ∨ P) => Or.elim h (fun q => Or.inr q) (fun p => Or.inl p))


-- proving identity and: p ∧ true ↔ p
-- forward: p and true implies p
-- backward: p implies p and true by adding true
def identityAnd     : (P ∧ True) ↔ P :=
Iff.intro
  (fun (h : P ∧ True) => h.left)
  (fun (p : P) => And.intro p True.intro)

-- proving identity or: p ∨ false ↔ p
-- forward: p or false implies p by ignoring false
-- backward: p implies p or false by picking left side
def identityOr      : (P ∨ False) ↔ P :=
Iff.intro
  (fun (h : P ∨ False) => Or.elim h (fun p => p) (fun f => False.elim f))
  (fun (p : P) => Or.inl p)



-- proving annihilate and: p ∧ false ↔ false
-- forward: p and false is always false
-- backward: false implies p and false since it implies anything
def annhilateAnd    : (P ∧ False) ↔ False :=
Iff.intro
  (fun (h : P ∧ False) => h.right)
  (fun (h : False) => False.elim h)

-- proving annihilate or: p ∨ true ↔ true
-- forward: p or true is always true
-- backward: true implies p or true
def annhilateOr     : (P ∨ True) ↔ True :=
Iff.intro
  (fun (h : P ∨ True) => True.intro)
  (fun (h : True) => Or.inr h)


-- proving or associative: (p ∨ q) ∨ r ↔ p ∨ (q ∨ r)
-- forward: reorder (p ∨ q) ∨ r to p ∨ (q ∨ r)
-- backward: reorder p ∨ (q ∨ r) to (p ∨ q) ∨ r
def orAssociative   : ((P ∨ Q) ∨ R) ↔ (P ∨ (Q ∨ R)) :=
Iff.intro
  (fun (h : (P ∨ Q) ∨ R) =>
    Or.elim h
      (fun pq => Or.elim pq (fun p => Or.inl p) (fun q => Or.inr (Or.inl q)))
      (fun r => Or.inr (Or.inr r))
  )
  (fun (h : P ∨ (Q ∨ R)) =>
    Or.elim h
      (fun p => Or.inl (Or.inl p))
      (fun qr => Or.elim qr (fun q => Or.inl (Or.inr q)) (fun r => Or.inr r))
  )


-- proving and associative: (p ∧ q) ∧ r ↔ p ∧ (q ∧ r)
-- forward: (p ∧ q) ∧ r reordered to p ∧ (q ∧ r)
-- backward: p ∧ (q ∧ r) reordered to (p ∧ q) ∧ r
def andAssociative  : ((P ∧ Q) ∧ R) ↔ (P ∧ (Q ∧ R)) :=
Iff.intro
  (fun (h : (P ∧ Q) ∧ R) => And.intro h.left.left (And.intro h.left.right h.right))
  (fun (h : P ∧ (Q ∧ R)) => And.intro (And.intro h.left h.right.left) h.right.right)

-- proving distributive and over or: p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r)
-- forward: if p and (q ∨ r), pair p with each
-- backward: if p ∧ q or p ∧ r, use whichever applies

def distribAndOr    : (P ∧ (Q ∨ R)) ↔ ((P ∧ Q) ∨ (P ∧ R)) :=
Iff.intro
  (fun (h : P ∧ (Q ∨ R)) =>
    Or.elim h.right (fun q => Or.inl (And.intro h.left q)) (fun r => Or.inr (And.intro h.left r))
  )
  (fun (h : (P ∧ Q) ∨ (P ∧ R)) =>
    Or.elim h (fun pq => And.intro pq.left (Or.inl pq.right)) (fun pr => And.intro pr.left (Or.inr pr.right))
  )


-- proving distributive or over and: p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r)
-- forward: if p or (q ∧ r), distribute p to each side
-- backward: if p ∨ q and p ∨ r, combine cases
def distribOrAnd    : (P ∨ (Q ∧ R)) ↔ ((P ∨ Q) ∧ (P ∨ R)) :=
Iff.intro
  (fun (h : P ∨ (Q ∧ R)) =>
    Or.elim h (fun p => And.intro (Or.inl p) (Or.inl p)) (fun qr => And.intro (Or.inr qr.left) (Or.inr qr.right))
  )
  (fun (h : (P ∨ Q) ∧ (P ∨ R)) =>
    Or.elim h.left (fun p => Or.inl p) (fun q => Or.elim h.right (fun p => Or.inl p) (fun r => Or.inr (And.intro q r)))
  )



-- proving equivalence as an and of implications: p ↔ q ↔ (p → q) ∧ (q → p)
-- forward: p ↔ q gives both implications directly
-- backward: if p → q and q → p, combine to get p ↔ q
def equivalence     : (P ↔ Q) ↔ ((P → Q) ∧ (Q → P)) :=
Iff.intro
  (fun (h : P ↔ Q) => And.intro h.mp h.mpr)
  (fun (h : (P → Q) ∧ (Q → P)) => Iff.intro h.left h.right)


def implication : (P → Q) ↔ (¬P ∨ Q) :=
Iff.intro
  -- forward direction: (P → Q) → (¬P ∨ Q)
  (fun h =>
    Classical.em P |> λ
      | Or.inl p => Or.inr (h p)
      | Or.inr np => Or.inl np)
  -- backward direction: (¬P ∨ Q) → (P → Q)
  (fun h p =>
    match h with
    | Or.inl np => False.elim (np p)
    | Or.inr q => q)


-- proving exportation: (p ∧ q) → r ↔ p → q → r
-- forward: if p ∧ q implies r, each part implies r
-- backward: if p → q → r, combine p and q to get r
def exportation     : ((P ∧ Q) → R) ↔ (P → Q → R) :=
Iff.intro
  (fun (h : (P ∧ Q) → R) => fun p q => h (And.intro p q))
  (fun (h : P → Q → R) => fun pq => h pq.left pq.right)


-- proving absurdity: (p → q) ∧ (p → ¬q) implies ¬p
-- forward: if p implies q and also ¬q, p cannot hold
def absurdity       : (P → Q) ∧ (P → ¬Q) → ¬P :=
fun h p => (h.right p) (h.left p)

-- proving not distributive over and: ¬(p ∧ q) ↔ ¬p ∨ ¬q
-- forward: if ¬(p ∧ q), one of p or q must fail
-- backward: if ¬p or ¬q holds, then p ∧ q cannot hold
-- couldnt figure out how to do this without classical.em used in latter parts of the experiment, had some help from other TA.
def distribNotAnd : ¬(P ∧ Q) ↔ (¬P ∨ ¬Q) :=
Iff.intro
  (fun h =>
    match Classical.em P with
    | Or.inl p => Or.inr (fun q => h (And.intro p q))
    | Or.inr np => Or.inl np
    )
  (fun h (pq : P ∧ Q) =>
    match h with
    | Or.inl np => np pq.left
    | Or.inr nq => nq pq.right
    )

-- proving not distributive over or: ¬(p ∨ q) ↔ ¬p ∧ ¬q
-- forward: if ¬(p ∨ q), both ¬p and ¬q must hold
-- backward: if both ¬p and ¬q hold, p ∨ q cannot hold
def distribNotOr    : ¬(P ∨ Q) ↔ (¬P ∧ ¬Q) :=
Iff.intro
  (fun (h : ¬(P ∨ Q)) => And.intro (fun p => h (Or.inl p)) (fun q => h (Or.inr q)))
  (fun (h : ¬P ∧ ¬Q) => fun (pq : P ∨ Q) => Or.elim pq (fun p => h.left p) (fun q => h.right q))


/-!
EXTRA CREDIT: apply the axiom of the excluded middle
to give a classical proof of any propositions that you
identified as having no constructive proof. The axiom
is available as Classical.em (p : Prop) : p ∨ ¬p.
-/

#check Classical.em
-- Classical.em (p : Prop) : p ∨ ¬p

/-!
Given nothing but a proposition, excluded middle gives
you a proof of A ∨ ¬A 'for free". By "free" we mean that
you can have a proof of A ∨ ¬A without providing a proof
of either A or of ¬A. We call such a proof of (A ∨ ¬A)
non-constructive.
-/
def pfAorNA (A : Prop) : A ∨ ¬A := Classical.em A


/-!
The next insight you want is that with a proof of A ∨ ¬A,
you can do a case analysis on that disjunction. In one
case, you'll have the assumption A is true (with a proof
(a : A)). In the other case, you'll have the assumption
that ¬A is true (with a proof (na : ¬A)). The other case
assumes ¬A is true, with a proof, (na : ¬A).

In other words, the axiom of the excluded middle forces
every proposition to be either true or false, with no
indeterminate "middle" state where you don't have a proof
either way. (Recall that in the constructive logic of Lean
you can construct a proof of A ∨ ¬A if and only if you have
a proof one way or the other. Now we see why they call it
the "law of the excluded middle." But really it's just an
axiom.

Indeed, excluded middle is one of several non-constructive
axioms that can be added to Lean simply by stating that they
are axioms. Negation elimination, ¬¬A → A, also called proof
by contradiction, is equivalent to excluded middle (can you
prove it), so if you adopt one you get the other as well.

Additional axioms that you might need to include in Lean
for some purposes include the following:

- functional extensionality (simplified), ∀ a, f a = g a → f = g
- propositional extensionality, (P ↔ Q) ↔ P = Q
- choice: Nonempty A → A
-/

#check funext
#check propext
#check Classical.choice

/-!
The first axiom let's you conclude (and have a proof) that two
functions are equal if they return the same results on all of
their inputs. The second let's you replace bi-implication with
equality of propositions, and vice versal.

The third? It requires an understanding that when you construct
a proof of ∃ x, P x, E.g., (Exists.intro 4 (Ev 4)) the value you
provided (here 4) is forgotten. You can never get a specific value
back out of a proof of ∃. This fact mirrors the idea that all that
a proof of an existential proposition tells you is that there is
*some* value out there in the universe that satisifes the given
predicate, but not what it is. What this axiom says is that if
you can provide there's some "witness/value", then you can get
an actual value. To prove some theorems in mathematics, you need
this. The tradeoff is that Lean marks the value as non-computable,
which means you can't actually compute anything with it.

All you need to know for this class is that the axioms of the
excluded middle, and equivalently negation elimination (thus also
proof by contradiction), are not constructive and thus not in the
axioms of the *constructive* logic of Lean. However, you can add
them to the logic without making it inconsistent (introducing any
contradictions) in cases where you want to "reason classically."

So, finally, let's see in Lean what it actually looks like to use
"em" (excluded middle). Remember: from a proposition, A, first use
em to get a proof of A ∨ ¬A, then do case analysis on that proof,
yielding on case where A is true and another case where it's false,
and where there are no other possible states of affairs, e.g., not
having a proof either way.
-/

#check P                -- a proposition
#check Classical.em P   -- a proof of P or ¬P

-- And here's a partial proof showing exactly how to use em
example : P → Q :=
  match (Classical.em P) with
  | Or.inl p =>  _      -- P is true, with p a proof
  | Or.inr np => _      -- P is false, with np a proof

-- we're going to do with Implication
def implicationExtraCredit : (P → Q) ↔ (¬P ∨ Q) :=
Iff.intro

  (fun h =>
    match Classical.em P with
    | Or.inl p => Or.inr (h p)  -- if P  true, use h to get Q
    | Or.inr np => Or.inl np     -- if ¬P holds, we're done
    )
  (fun h p =>
    match h with
    | Or.inl np => False.elim (np p)  -- if ¬P, contradiction
    | Or.inr q => q                   -- if Q, return Q
    )
