/-
CS 2120 F22 Homework #4. Due Oct 13.
-/

/- #1A [10 points]

Write a formal proposition stating that 
logical and (∧) is associative. That is, 
for arbitrary propositions, P, Q, and R,
P ∧ (Q ∧ R) is true *iff* (P ∧ Q) ∧ R is, 
too. Replace the placeholder (_) with your
answer.
-/

def and_associative : Prop := 
  ∀ (P Q R : Prop),
    (P ∧ (Q ∧ R)) ↔
    (P ∧ Q) ∧ R P p


/- #1B [10 points]

Give an English language proof. Identify
the inference rules of predicate logic
that you use in your reasoning.
-/

/-
Answer: The inference rules that can be used in my reasoning are the rule of iff.intro and
the elimination AND rule.

-/
/--/ #1C [5 points]

Give a formal proof of the proposition.
Hint: unfold and_associative to start.
-/

theorem and_assoc_true : and_associative :=
begin
  unfold and_associative,
  assume (p : P) (q : Q) (r : R),
  apply (iff.intro p q r),
  exact p,
  exact q,
  exact r,

end



/- #2A [10 points]

Write the proposition that ∨ is associative.,
analogous to the proposition about ∧ in #1.
-/

def or_associative : Prop := 
  ∀ (P Q R : Prop),
    (P ∨ (Q ∨ R)) ↔
    (P ∨ Q) ∨ R


/- #2B [10 points]

Write an English language proof of it, citing
the specific inference rules you use in your
reasoning.

The inference rules that can be used in my reasoning are the rule of iff.intro and
the elimination OR rule.
-/


/- #2C [5 points]

Complete the following formal proof.
-/

theorem or_associative_true : or_associative :=
begin
  unfold or_associative,
  assume (p : P) (q : Q) (r : R),
  apply (iff.intro p q r),
  exact p,
  exact q,
  exact r,
end


/- #3A [10 points]
Write a formal statement of the proposition.
-/

def arrow_transitive : Prop :=
  (X → Y) → (Y → Z) → (X → Z)


/- #3B [10 points]

Write an English language proof of the proposition
that for any propositions, X, Y, and X, it's the
case that (X → Y) → (Y → Z) → (X → Z). In other
words, implication is "transitive." Hint: Recall
that if you have a proof of, say, X → Y, and you 
have a proof of X, you can derive a proof of Y by
arrow elimination. Think of it as applying a proof
of an implication to a proof of its premise to get
yourself a proof of its conclusion.

Let X, Y, and Z be arbitrary but specific propositions. To prove (X → Y) → (Y → Z) → (X → Z),
assume (X → Y) → (Y → Z) as a hypothesis. By the introduction rule for ∀, 
we deduce X, Y, and Z. We now prove X → Z by → introduction on either side. In further English terms, when given a function that shows that for any proof of X also gives the proof of Y shows that 
whenever X is true, so is Y. This means that X implies Y. Additionally, when given a function that 
proves whenever Y is true, so is Z. By the transitive propery, this function would also serve to show 
that whenever X is true, so is Z. This means that if X implies Y, and Y implies Z, then X implies Z.
-/


/- #3C [5 points]. 
Write a formal proof of it.
-/
example : (X → Y) → (Y → Z) → (X → Z) :=
begin
assume h,
cases h with x y z,
apply iff.intro h,
end

/- #4
Suppose that if it's raining then the streets
are wet. This problem requires you to prove that
if the streets are not wet then it's not raining.
-/

/- #4A [10 points]

Start by writing the proposition in predicate
logic by completing the following answer.
-/

def contrapositive :=
  (Raining → Wet) →  (¬Raining → ¬Wet)

/-
OR
-/
  (∀ (Raining Wet : Prop), Raining → Wet)
    ∀ (Raining Wet : Prop),
      ¬Raining → ¬Wet


/- #4B [10 points]. 
-/

theorem contrapositive_valid : contrapositive :=
begin
unfold contrapositive,
assume Raining,
assume Wet,
assume nRaining,
assume nWet,
cases nWet with Raining Wet,
exact nWet,
apply neg_elim,
end

/- #4C [5 points]. 

Give an English language proof of it.
Let Raining and Wet be arbitrary but specific propositions. To prove (Raining → Wet) → (¬Raining → ¬Wet),
assume (Raining → Wet) as a hypothesis. By the rule of negation for ∀, 
we deduce Rainind and Wet. We now prove (¬Raining → ¬Wet) by negation elimination. 
-/


/- #5. Extra credit.

Complete the following formal proof of the 
proposition that if for any proposition P, 
P ∨ ¬P is true, then for any propositions, 
X and Y, if it's not the case that X or Y
is true then it is the case that ¬X and ¬Y 
is true. 
-/

theorem demorgan1 : 
  (∀ (P : Prop), P ∨ ¬ P) → 
    ∀ (X Y : Prop), 
      ¬(X ∨ Y) → (¬X ∧ ¬Y) :=
begin
assume em X Y nxory,
cases (em X) with x nx,
let foo := or.intro_left Y x,
apply false.elim foo,
end

/-
A comment on or.intro_left and or.intro_right.
In Lean each of these takes two arguments: a
proof of the disjunct -- the proposition on 
one side of the ∨ -- that is to be proven true, 
*and* it takes as an argument the proposition 
that is not being proven true. In applications 
of these rules the proposition argument (not 
being proven) comes first, while the proof 
argument comes second.

The reason is that Lean needs to know what 
overall proposition is being proved. From the
proof argument it can infer the proposition 
being proved, but it needs the other proposition
as well to know the full (X ∨ Y) disjunction to
be proved. 

Here's an example:
-/

example : 0 = 0 ∨ 0 = 1 :=
begin
apply or.intro_left (0 = 1) rfl
/-
The "rfl" serves as a proof of 0=0.
But in addition, as the first argument
to or.intro, we need to provide the
*proposition* that is not being proved.
Here's that's (0 = 1). In contexts
where Lean can infer both disuncts,
you can use the simpler or.inl or 
or.inr, each of which just takes one
argument: a proof of the left or of 
the right side, respectively.
-/
end

