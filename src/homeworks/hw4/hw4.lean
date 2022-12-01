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
  ∀ (X Y Z : Prop),
    X ∧ (Y ∧ Z) ↔ (X ∧ Y) ∧ Z



/- #1B [10 points]

Give an English language proof. Identify
the inference rules of predicate logic
that you use in your reasoning.
-/

/-
Answer: For the first proof, we assume the premise (P and Q) and R and attempt 
too prove the conclusion P and (Q and R). We use and_elimination to separate our assumption
(P and Q) and R into its components P Q and R. I then utilized and _introduction to
assumble a proof of Q and R, and then assumble a proof of P and (Q and R)

X and Y and Z is true if and only if X and Y and Z is also true. All of these need to be 
true in order for this to apply. The inference rules used are and elimation and iff elimation.
-/

/- #1C [5 points]

Give a formal proof of the proposition.
Hint: unfold and_associative to start.
-/

theorem and_assoc_true : and_associative :=
begin
unfold and_associative,
assume P Q R,

apply iff.intro _,
assume pqAndR,
let pq := pqAndR.left,
let r := pqAndR.right,
let p := pq.left,
let q := pq.right,
let qr := and.intro q r,
let pAndqr := and.intro p qr,
exact pAndqr,

assume pAndqr,
let p := pAndqr.left,
let qr := pAndqr.right,
let q := qr.left,
let r := qr.right,
let pq := and.intro p q,
let pqAndr := and.intro pq r,
exact pqAndr,
end



/- #2A [10 points]

Write the proposition that ∨ is associative.,
analogous to the proposition about ∧ in #1.
-/

def or_associative : Prop := 
  ∀ (X Y Z : Prop), 
    X ∨ (Y ∨ Z) ↔ (X ∨ Y) ∨ Z


/- #2B [10 points]

Write an English language proof of it, citing
the specific inference rules you use in your
reasoning.

X or Y or Z is true if and only if X or Y or Z is also true. If X is true, then Y or Z can be false,
which would make the statement valid throughout. If Y or Z is true, it would also make the statment
valid. Only one of the elements (X, Y, or Z) need to be true for this to work and the iff proves
whether or not it's true. X or Y or Z will only be true if the counter is also true. The inference
rules used are or elimation and iff elimation.
-/


/- #2C [5 points]

Complete the following formal proof.
-/

theorem or_associative_true : or_associative :=
begin
unfold or_associative,
assume P Q R,
apply iff.intro _ _,
 --goal 1
assume pOrqr,
cases pOrqr with p qr,
let pq := or.inl p,
let pqOrr := or.inl pq,
exact pqOrr,
cases qr with q r,
exact or.inl (or.inr q),
exact or.inr r,

--goal 2
assume pqOrr,
cases pqOrr with pq r,
cases pq with p q,
--let pq := or.inr p,
--let rqp := or.inr (or.inr p),
exact or.inl p,
let pqr := or.inr (or.inl q),
exact pqr,
let r := or.inr (or.inr r),
exact r,






/-
--start of foal 1
assume pOrqr,
cases pOrqr with p qr,
have pq := or.inl p,
have pqOrr := or.inl pq,
exact pqOrr,
cases qr with q r,
exact or.inl (or.inr q),
exact or.inr r,
--end goal 1
--start goal 2
assume pqOrr,
cases pqOrr with pq r,
cases pq with p q,

-/










end


/- #3A [10 points]
Write a formal statement of the proposition.
-/

def arrow_transitive : Prop :=
  ∀ (X Y Z : Prop), 
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

ANSWER:
Assume arbitrary proposition P Q and R. What's left to prove is an implication.
We assume the premises P → Q and Q → R. What's left to prove is that P → R. We then
assume a proof of P, and then apply it to the proof of P → Q to get a proof of Q. We then obtain 
our goal by applying the proof of Q to the proof of Q → R to get a proof of R.

If X, Y, and Z are any propositions, then if X implies Y is true then Y implies Z is true then
X implies Z is true. If X implies Y is true, Y implies Z and X implies Z must also be true.
-/


/- #3C [5 points]. 
Write a formal proof of it.
-/
theorem arrow_transitive_true : arrow_transitive :=
begin
unfold arrow_transitive,
assume P Q R,
assume PtoQ,
assume QtoR,
assume p,
have q:= PtoQ p,
have r := QtoR q,
apply r,
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

def contrapositive : Prop :=
  ∀ (Raining Wet : Prop), 
    (Raining → Wet) → (¬Wet → ¬Raining)
    

/- #4B [10 points]. 
-/

theorem contrapositive_valid : contrapositive :=
begin
unfold contrapositive,
assume Raining Wet,
assume RainingToWet,
assume notwet,
assume Raining,
let Wet := RainingToWet Raining,
-- contradiction, CAN USE THIS
let f := notWet Wet,
apply false.elim f,
end

/- #4C [5 points]. 

Give an English language proof of it.

For all propositions of Raining and Wet, if it's raining then the streets are wet then if it's
not raining then the streets are not wet

ANSWER:
Assume some abitrary propositions that it is Raining and the streets are Wet. we then assume
that we have a proof that if it's raining, then the streets are wet. We then assume that we 
have a proof that the streets are not wet. What's left to show is that it is not raining. We
can do this through proof by contradiction.

For proof by contradiction, we first assume that it is raining. We can then apply this proof 
that it's raining to the proof that if it's raining, then the streets are wet and obtain a 
proof that the streets are wet. However, we already assumed that the streets are not wet, and 
therefore we have a contraction. meaning it must be true that it is not raining.
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
    ∀ (X Y : Prop), -- law of excluded middle
      ¬(X ∨ Y) → (¬X ∧ ¬Y) :=
begin
assume em X Y nxory,
cases (em X) with x nx,
let foo := or.intro_left Y x,
--Case 1 begin
let f := nxory foo, -- not(X or Y) == (X or Y) --> false
exact false.elim f,
--Case 1 end
--Case 2 begin
--Case 2.1 begin
cases (em Y) with y ny,
have xOry := or.inr y,
let f := nxory xOry,
exact false.elim f,
--Case 2.1 end
--Case 2.2 begin
exact and.intro nx ny,
--Case 2.2 end
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

/-
Constructive:
  Person : Type
  alex : Person
  Mortal(alex)

First Order:
  o -> Person(o) -> Mortal(Person(o))

Commutative:
  P and Q == Q and P

Associative:
  (P and Q) and R == P and (Q and R)


Negation elimation: (need law of excluded middle to prove it, if you negate not p then p)
  ¬¬P → P
  ¬(P → )
-/