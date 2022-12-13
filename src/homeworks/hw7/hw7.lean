import data.set

/- #1

Formally prove that if there's an object, a, of some 
type, α, having some property (satisfying a predicate), 
P, then not every object of type α fails to have property, 
P. Add a brief comment before each line of your proof 
script to provide what amounts to the outline of a good
English language proof.
-/

example (α : Type) (P : α → Prop) : (∃ a, P a) → (¬(∀ x, ¬ P x)) :=
begin
--Making assumption h to start the proof
assume h,
--Making assumption w to start the proof
assume w,
--breaking up the Exists clause to build up the proof
cases h with a b,
--applying notP x when given alpha to now prove P a

--have npa := w a,
--contradiction,
apply w a,
--Exacting b to because it is equivalent to the predicate
exact b,
end


/- Extra credit. 

The converse of this proposition is clasically true. If
not every object lacks propery, P, then there must be some
object that has it. If you try to prove the converse in
our constructive logic, what happens? Show you work, and
then briefly but clearly explain exactly what goes wrong.

If you try to prove the constructive logic in lean, essentially the converse of this proposition
is classically true and doesn't work in constructive logic. The law of the excludede middle essentially makes it
so that we don't have a variable of type alpha. Basically, it doesn't work because we need classical.em.
-/


/- #2

Consider the following binary relation, r, with domain
and co-domain both being ℕ. For each following question,
answer yes/no then briefly justify your answer.

( domain = ℕ, r = {(0,0),(1,1),(2,2)}, co-domain=ℕ )

A. Is this relation reflexive? 

No, it is not reflexive. This is because every value in the domain has to be reflexive and
the domain is all natural numbers. We only have 0, 1, and 2.

B. Is this relation symmetric? 

Yes, it is symmetric. This is because the same number maps to itself in both directions.
Symmetric: r a b → r b a 

C. Is this relation transitive? 

Yes, it is transitive. This is because Transitive: r a b → r b c → r a c.

D. Is this relation an equivalence relation? 

No, it is not an equivalence relation. This is because equivalence := 
  reflexive r ∧ 
  symmetric r ∧ 
  transitive r

  Because it is not reflexive, it cannot be an equivalence relation.

-/



/- #3

A binary relation, r, is said to be *anti-symetric* 
if, for all values in its domain, a and b, if r a b 
and if r b a then a = b. Give an example of a familiar
arithmetic relation that's anti-symmetric, and briefly
explain why it's so.

Anti-Symmetric : r a b → r b a → a = b
Anti-Symmetric : [Symmetric r] → (a = b)


An arithmetic relation that's anti-symmetric is equivalent because if r a b is equivalent and r b a
is equivalent then a and be must be equivalent.

Basically, "=" is anti-symmetric.

-/


/- #4
A binary relation, r, is said to be *asymmetric* if
whenever, for any a and b, if r a b then ¬ r b a. Be
careful to note that asymmetry and antisymmetry are
different properties.  Answer each of the following 
sub-questions. We give you a formal definition of anti
-/

def is_asymmetric 
  {α : Type} 
  (r : α → α → Prop) : Prop 
  := ∀ (a b : α), r a b → ¬ r b a 

/- A.

Name a familar arithmetic relation that's asymmetric
and briefly explain why you think it's asymmetric.

Answer here:

An arithmetic relation that's asymmetric is greater than or > because
in all cases where a > b then not(b > a) is always true.

-/

/- C: 

An object cannot be related to itself in an asymmetric
relation. First, complete the following informal proof
of this statement.

Proof: Assume α, r, and a are as given (and in particular
assume that r is asymmetric). Now assume r a a. <finish
the proof>.

Answer here (rest of proof): 
We have assumed r a a, and our remaining goal is to show ¬ r a a.
This is obviously a contradiction.
-/

/- D.

Now prove a closely related proposition formally. 
Add a comment to each line of your formal proof 
so as to construct a good skeleton for a fluent 
English language proof.
-/

example
  (α : Type) 
  (r : α → α → Prop)
  (h : is_asymmetric r) :
¬ ∃ (a : α), r a a :=
begin
-- proof by negation
assume p1,
cases p1 with a raa,
unfold is_asymmetric at h,
have p2 := h a a,
have nraa := p2 raa,
contradiction,
end


/- #5
Prove that equality on an inhabited (non-empty) type 
is not assymetric. In the following formalization we
assume there is a value (a : α), which establishes 
that α is inhabited.
-/

example (α : Type) (a : α): ¬ is_asymmetric (@eq α) :=
begin
unfold is_asymmetric,
assume asymEQ,
have p1 := asymEQ a a,
have neq := p1 rfl,
contradiction,
end

/- Extra credit: What exactly goes wrong in a formal 
proof if you drop the "inhabitedness" condition? Give
as much of a formal proof as you can then explain why
it can't be completed (if it can't!).
-/
example (α : Type): ¬ is_asymmetric (@eq α) :=
begin
unfold is_asymmetric,
assume asymEQ,
--NO VALUES OF TYPE α TO WORK WITH
end



/- #6
Two natural numbers, p and q, are said to be 
"equivalent mod m" if p % m = q % m, which makes
"equivalence mod m" a binary relation on natural
numbers. Here's a formal definition of this binary
relation on the natural numbers (given an m).
-/

def equiv_mod_m (m : ℕ) : ℕ → ℕ → Prop := 
  λ p q : ℕ, p % m = q % m

/-
Prove using Lean's definition of "equivalence" that 
equiv_mod_m is an equivalence relation for any natural
number, m. Here you'll also use Lean's definitions of
reflexive, symmetric, and transitive. They are as we
have covered in class. 
-/

example : ∀ m : ℕ, equivalence (equiv_mod_m m) :=
begin
assume m,
unfold equivalence equiv_mod_m,
split,
--SHOW REFLEXIVITY
unfold reflexive,
assume n,
exact rfl,
split,

unfold symmetric,
assume x y,
assume premise,
rw premise,

unfold transitive,
assume x y z,
assume p1 p2,
rw p1,
rw p2,
end



/- #7
Consider the relation, tin_rel, that associates people 
with U.S. taxpayer id numbers, which we'll represent as 
natural numbers here. 

Assume this relation is single-valued. Which of the 
following properties does this relation have? Give
a very brief justification of each answer. Assume
the domain is all living persons, and the co-domain
is all natural numbers.

-- it's a function: 

Yes, it is a function because it is single-valued.

-- it's total: 

No, it is not total because not every living person has a U.S. taxpayer ID.
(non-U.S. humans)

-- it's injective:

Yes, it is injective because two people cannot map to the same taxpayer ID number.

-- it's surjective (where the co-domain is all ℕ):

No, it is not surjective because not every natural number possible taxpayer ID number
has a person associated with it.

-- it's strictly partial:  

Yes, it is not strictly partial because not every living person has a U.S. taxpayer ID.
(non-U.S. humans)

-- it's bijective: 

No, it is not surjective.

-/



/- #8
Suppose r is the empty relation on the natural 
numbers. Which of the following properties does
it have? Explain each answer enough to show you
know why your answer is correct.

-- reflexive:

No because we cannot assume total because it is empty.

-- symmetric:

We can assume its there because we cannot prove a contradictory proof.

-- transitive:

We can assume its there because we cannot prove a contradictory proof.



-/


/- #9
Here's a formal definition of this empty relation.
That there are no constructors given here means there 
are no proofs, which is to say that no pair can be 
proved to be in this relation, so it must be empty.
-/

inductive empty_rel : ℕ → ℕ → Prop

/-
Formally state and prove you answer for each of the
three properties. That is, for each property assert
either that empty_rel does have it or does not have it, 
then prove your assertion. Include English-language 
comments on each line to give the essential elements 
of a good English language proof.
-/


example : ¬reflexive empty_rel :=
begin
unfold reflexive,
assume h,
let x := h 0,
cases x,
end

example : symmetric empty_rel :=
begin
unfold symmetric,
assume a b h,
cases h,
end

example : transitive empty_rel :=
begin
assume a b c h k,
cases h,
end

/- #10
A relation, r, is said to have the property of being 
a *partial order* if it's reflexive, anti-symmetric,
and transitive. Give a brief English language proof 
that the subset relation on the subsets of any set, 
S (of objects of some type), is a partial order. 

Pf:  
Suppose S is a set, with a ⊆ S and b ⊆ S subsets. Then

1. Reflexive, a is a subset of itself.
2. Anti-Symmetric, if a ⊆ b, and b ⊆ a, then it must be true that a = b
3. Transitive, if a ⊆ b, and b ⊆ c, then it must be true that a ⊆ c
QED.
-/



/- #11 
Finally we return again to DeMorgan's laws, but
now for sets. You'll recall that these "laws" as we
have seent them so far tell us how to distribute ¬  
over ∨ and over ∧. You will also recall that set
intersection (∩) is defined by the conjunction (∧) 
of the membership predicates, set union (∪) by the
disjunction (∨), and set complement (Sᶜ for a set,
S), by negation (¬). It makes sense to hypothesize 
that we can recast DeMorgan's laws in terms of the
distribution of complement over set union and set
intersection. Indeed we can. Your job is to state
and prove (formally) the first DeMorgan laws for 
sets, which states that the complement of a union
of any two sets equals the intersection of their 
complements.

Hint: To prove that two sets are equal, S = T, use
the ext tactic. It applies a bew axiom (called set 
extensionality) that states that to prove S = T it 
suffices to prove S ↔ T, viewing the sets as being
defined by their logical membership predicates. You
know how to handle bi-implications. The rest you 
can do by seeing "not," "and," and "or" in place 
of complement, conjunction, and disjuction, resp.  
-/

example 
  (α : Type) 
  (a b: set α) :
  (a ∪ b)ᶜ = aᶜ ∩ bᶜ := 
begin
ext,
split,

assume notAUB,
split,
assume xa,
have AUB := or.inl xa,
have f := notAUB AUB,
contradiction,

assume xb,
have AUB :=or.inr xb,
have f := notAUB AUB,
contradiction,

assume ACBC,
assume AUB,
cases AUB with A B,
have AC := ACBC.left,
contradiction,

have BC := ACBC.right,
contradiction,
end


