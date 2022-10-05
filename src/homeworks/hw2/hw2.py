#Connor Peterson
#csp8fy
from z3 import *
from telnetlib import X3PAD

# Here's a file you can often copy as a starting 
# point on a working program to solve some problem
# of interest. Here the problem is to compute and
# return a non-negative square root of argument, n 
def hw2():
    
    
    # Create z3 variable(s) representing the unknown
    X, Y, Z = Bools('X Y Z')
    
    s = Solver()
    
    # 1. X ∨ Y, X ⊢ ¬Y 
    # As proposition in PL: ((X \/ Y) /\ X) -> ~Y
    #If X ∧ Y is true, then it must be that X is true, as well."
    C1 = Implies(And(Or(X,Y),X),Not(Y))
    
    s.add(Not(C1))
    # I believe it's not valid
  
    r = s.check()
    
    # If there's a model/solution return it 
    if (r == unsat):
        print("C1 is valid")
    # otherwise return inconsistent value for error
    else :
        print("C1 is not valid. Here's a counter-example: ", s.model() )
    #If Y and X true, then it would not make sense that it would imply not Y would also be true. 

##############C2
  # Create z3 variable(s) representing the unknown

    X2, Y2, Z2 = Bools('X2 Y2 Z2')
    
    s2 = Solver()
    
    #2. X, Y ⊢ X ∧ Y
    
    # As proposition in PL: (Y /\ X) -> (X /\ Y)
    #If y is true and x is true, then x and y is true
    C2 = Implies(And(X2,Y2), And(X2,Y2))
    
    s2.add(Not(C2))
    # I believe it is valid
  
    r2 = s2.check()
    
    # If there's a model/solution return it 
    if (r2 == unsat):
        print("C2 is valid")
    # otherwise return inconsistent value for error
    else :
        print("C2 is not valid. Here's a counter-example: ", s2.model() )

##############C3
  # Create z3 variable(s) representing the unknown

    X3, Y3, Z3 = Bools('X3 Y3 Z3')
    
    s3 = Solver()
    
    #3. X ∧ Y ⊢ X  
    # As proposition in PL: (Y /\ X) -> X
    C3 = Implies(And(X3,Y3), X3)
    
    s3.add(Not(C3))
    # I believe it is valid
  
    r3 = s3.check()
    
    # If there's a model/solution return it 
    if (r3 == unsat):
        print("C3 is valid")
    # otherwise return inconsistent value for error
    else :
        print("C3 is not valid. Here's a counter-example: ", s3.model() )
        
##############C4
  # Create z3 variable(s) representing the unknown

    X4, Y4, Z4 = Bools('X4 Y4 Z4')
    
    s4 = Solver()
    
    #4. X ∧ Y ⊢ Y  
    # As proposition in PL: (Y /\ X) -> Y
    # If X and Y are true, then it implies Y is true.
    C4 = Implies(And(X4,Y4), Y4)
    
    s4.add(Not(C4))
    # I believe it is valid
  
    r4 = s4.check()
    
    # If there's a model/solution return it 
    if (r4 == unsat):
        print("C4 is valid")
    # otherwise return inconsistent value for error
    else :
        print("C4 is not valid. Here's a counter-example: ", s4.model() )
        
##############C5
  # Create z3 variable(s) representing the unknown

    X5, Y5, Z5 = Bools('X5 Y5 Z5')
    
    s5 = Solver()
    
    #5. ¬¬X ⊢ X  
    # As proposition in PL: ~~X -> X
    # If the opposite of not x(x) is true implies X is true.
    C5 = Implies(Not(Not(X5)), X5)
    
    s5.add(Not(C5))
    # I believe it is valid
  
    r5 = s5.check()
    
    # If there's a model/solution return it 
    if (r5 == unsat):
        print("C5 is valid")
    # otherwise return inconsistent value for error
    else :
        print("C5 is not valid. Here's a counter-example: ", s5.model() )
 
 ##############C6
  # Create z3 variable(s) representing the unknown

    X6, Y6, Z6 = Bools('X6 Y6 Z6')
    
    s6 = Solver()
    
    #6. ¬(X ∧ ¬X)   
    # As proposition in PL: ~(X /\ ~X)
    # The opposite of X and not X
    C6 = Not(And(X6,Not(X6)))
    
    s6.add(Not(C6))
    # I believe it is valid
  
    r6 = s6.check()
    
    # If there's a model/solution return it 
    if (r6 == unsat):
        print("C6 is valid")
    # otherwise return inconsistent value for error
    else :
        print("C6 is not valid. Here's a counter-example: ", s6.model() )
    
 ##############C7
  # Create z3 variable(s) representing the unknown

    X7, Y7, Z7 = Bools('X7 Y7 Z7')
    
    s7 = Solver()
    
    #7. X ⊢ X ∨ Y   
    # As proposition in PL: X -> (X \/ Y)
    # If X is true then it implies X or Y is true
    C7 = Implies(X7, Or(X7,Y7))
    
    s7.add(Not(C7))
    # I believe it is valid
  
    r7 = s7.check()
    
    # If there's a model/solution return it 
    if (r7 == unsat):
        print("C7 is valid")
    # otherwise return inconsistent value for error
    else :
        print("C7 is not valid. Here's a counter-example: ", s7.model() )

##############C8
  # Create z3 variable(s) representing the unknown

    X8, Y8, Z8 = Bools('X8 Y8 Z8')
    
    s8 = Solver()
    
    #8. Y ⊢ X ∨ Y   
    # As proposition in PL: Y -> (X \/ Y)
    # If Y is true then it implies X or Y is true
    C8 = Implies(Y8, Or(X8,Y8))
    
    s8.add(Not(C8))
    # I believe it is valid
  
    r8 = s8.check()
    
    # If there's a model/solution return it 
    if (r8 == unsat):
        print("C8 is valid")
    # otherwise return inconsistent value for error
    else :
        print("C8 is not valid. Here's a counter-example: ", s8.model() )
 
##############C9
  # Create z3 variable(s) representing the unknown

    X9, Y9, Z9 = Bools('X9 Y9 Z9')
    
    s9 = Solver()
    
    #9. X → Y, ¬X ⊢ ¬ Y   
    # As proposition in PL: ((X -> Y) /\ ~X) -> ~Y
    #If X implies Y and not X is true then it implies not Y is true.
    C9 = Implies(And(Implies(X9, Y9), Not(X9)), Not(Y9))
    
    s9.add(Not(C9))
    # I believe it is not valid
  
    r9 = s9.check()
    
    # If there's a model/solution return it 
    if (r9 == unsat):
        print("C9 is valid")
    # otherwise return inconsistent value for error
    else :
        print("C9 is not valid. Here's a counter-example: ", s9.model() )
 #It doesn't make sense that if X implies Y and not X is true then not Y isnt always true.
 
##############C10
  # Create z3 variable(s) representing the unknown

    X10, Y10, Z10 = Bools('X10 Y10 Z10')
    
    s10 = Solver()
    
    #10. X → Y, Y → X ⊢ X ↔ Y  
    # As proposition in PL: ((X -> Y) /\ (Y->X)) -> X==Y
    #If X implies Y and Y implies X then it implies X is equal to Y.
    C10 = Implies(And(Implies(X10,Y10), Implies(Y10,X10)), X10==Y10)
    
    s10.add(Not(C10))
    # I believe it is valid
  
    r10 = s10.check()
    
    # If there's a model/solution return it 
    if (r10 == unsat):
        print("C10 is valid")
    # otherwise return inconsistent value for error
    else :
        print("C10 is not valid. Here's a counter-example: ", s10.model() )
 
##############C11
  # Create z3 variable(s) representing the unknown

    X11, Y11, Z11 = Bools('X11 Y11 Z11')
    
    s11 = Solver()
    
    #11. X ↔ Y ⊢ X → Y    
    # As proposition in PL: (X==Y) -> (X -> Y)
    #If X is equal to Y, it implies that X implies Y.
    C11 = Implies((X11==Y11), Implies(X11,Y11))
    
    s11.add(Not(C11))
    # I believe it is valid
  
    r11 = s11.check()
    
    # If there's a model/solution return it 
    if (r11 == unsat):
        print("C11 is valid")
    # otherwise return inconsistent value for error
    else :
        print("C11 is not valid. Here's a counter-example: ", s11.model())
        
##############C12
  # Create z3 variable(s) representing the unknown

    X12, Y12, Z12 = Bools('X12 Y12 Z12')
    
    s12 = Solver()
    
    #12. X ↔ Y ⊢ Y → X    
    # As proposition in PL: (X==Y) -> (Y -> X)
    #If X is equal to Y, it implies that Y implies X.
    C12 = Implies((X12==Y12), Implies(Y12,X12))
    
    s12.add(Not(C12))
    # I believe it is valid
  
    r12 = s12.check()
    
    # If there's a model/solution return it 
    if (r12 == unsat):
        print("C12 is valid")
    # otherwise return inconsistent value for error
    else :
        print("C12 is not valid. Here's a counter-example: ", s12.model())

##############C13
  # Create z3 variable(s) representing the unknown

    X13, Y13, Z13 = Bools('X13 Y13 Z13')
    
    s13 = Solver()
    
    #13. X ∨ Y, X → Z, Y → Z ⊢ Z    
    # As proposition in PL: ((X \/ Y) /\ (X -> Z) /\ (Y -> Z)) -> Z
    #If X or Y is true and X implies Z and Y implies Z, then it means Z is true.
    C13 = Implies(And(Or(X13,Y13), Implies(X13,Z13), Implies(Y13,Z13)), Z13)
    
    s13.add(Not(C13))
    # I believe it is valid
  
    r13 = s13.check()
    
    # If there's a model/solution return it 
    if (r13 == unsat):
        print("C13 is valid")
    # otherwise return inconsistent value for error
    else :
        print("C13 is not valid. Here's a counter-example: ", s13.model())

##############C14
  # Create z3 variable(s) representing the unknown

    X14, Y14, Z14 = Bools('X14 Y14 Z14')
    
    s14 = Solver()
    
    #14. X → Y, Y ⊢ X    
    # As proposition in PL: ((X -> Y) /\ Y) -> X
    #If X implies Y and Y is true, then X is true.
    C14 = Implies(And(Implies(X14,Y14),Y14), X14)
    
    s14.add(Not(C14))
    # I believe it is not valid
  
    r14 = s14.check()
    
    # If there's a model/solution return it 
    if (r14 == unsat):
        print("C14 is valid")
    # otherwise return inconsistent value for error
    else :
        print("C14 is not valid. Here's a counter-example: ", s14.model())
#Just because X implies Y and Y is true does not mean Y implies X. For example, If an apple is a fruit, and it is in fact a fruit does not necessarily mean that a fruit is always an apple. 

##############C15
  # Create z3 variable(s) representing the unknown

    X15, Y15, Z15 = Bools('X15 Y15 Z15')
    
    s15 = Solver()
    
    #15. X → Y, X ⊢ Y      
    # As proposition in PL: ((X -> Y) /\ X) -> Y
    #If X implies Y and Y is true, then X is true.
    C15 = Implies(And(Implies(X14,Y14),X14), Y14)
    
    s15.add(Not(C15))
    # I believe it is valid
  
    r15 = s15.check()
    
    # If there's a model/solution return it 
    if (r15 == unsat):
        print("C15 is valid")
    # otherwise return inconsistent value for error
    else :
        print("C15 is not valid. Here's a counter-example: ", s15.model())

##############C16
  # Create z3 variable(s) representing the unknown

    X16, Y16, Z16 = Bools('X16 Y16 Z16')
    
    s16 = Solver()
    
    #16. X → Y, Y → Z ⊢ X → Z     
    # As proposition in PL: ((X -> Y) /\ (Y -> Z)) -> (X -> Z)
    #If X implies Y and Y implies X, then X implies Z
    C16 = Implies(And(Implies(X16,Y16), Implies(Y16,Z16)), Implies(X16, Z16))
    
    s16.add(Not(C16))
    # I believe it is valid
  
    r16 = s16.check()
    
    # If there's a model/solution return it 
    if (r16 == unsat):
        print("C16 is valid")
    # otherwise return inconsistent value for error
    else :
        print("C16 is not valid. Here's a counter-example: ", s16.model())

##############C17
  # Create z3 variable(s) representing the unknown

    X17, Y17, Z17 = Bools('X17 Y17 Z17')
    
    s17 = Solver()
    
    #17. X → Y ⊢ Y → X       
    # As proposition in PL: (X -> Y) -> (Y -> X)
    #If X implies Y, then Y implies X
    C17 = Implies(Implies(X17,Y17), Implies(Y17,X17))
    
    s17.add(Not(C17))
    # I believe it is not valid
  
    r17 = s17.check()
    
    # If there's a model/solution return it 
    if (r17 == unsat):
        print("C17 is valid")
    # otherwise return inconsistent value for error
    else :
        print("C17 is not valid. Here's a counter-example: ", s17.model())
#It does not make sense that X implies Y, Y implies X. For example, A banana may imply a fruit, but a fruit does not necessarily imply a banana.

##############C18
  # Create z3 variable(s) representing the unknown

    X18, Y18, Z18 = Bools('X18 Y18 Z18')
    
    s18 = Solver()
    
    #18. X → Y ⊢ ¬Y → ¬X       
    # As proposition in PL: (X -> Y) -> (~Y -> ~X)
    #If X implies Y, then it implies that not Y implies not X.
    C18 = Implies(Implies(X18,Y18), Implies(Not(Y18),Not(X18)))
    
    s18.add(Not(C18))
    # I believe it is valid
  
    r18 = s18.check()
    
    # If there's a model/solution return it 
    if (r18 == unsat):
        print("C18 is valid")
    # otherwise return inconsistent value for error
    else :
        print("C18 is not valid. Here's a counter-example: ", s18.model())

##############C19
  # Create z3 variable(s) representing the unknown

    X19, Y19, Z19 = Bools('X19 Y19 Z19')
    
    s19 = Solver()
    
    #19. ¬(X ∨ Y) ↔ ¬X ∧ ¬Y       
    # As proposition in PL: ~(X \/ Y) == (~X /\ ~Y)
    #If the not of X or Y is true, then it is equal to not X and not Y.
    C19 = Not(Or(X19, Y19)) == And(Not(X19), Not(Y19))
    
    s19.add(Not(C19))
    # I believe it is valid
  
    r19 = s19.check()
    
    # If there's a model/solution return it 
    if (r19 == unsat):
        print("C19 is valid")
    # otherwise return inconsistent value for error
    else :
        print("C19 is not valid. Here's a counter-example: ", s19.model())

##############C20
  # Create z3 variable(s) representing the unknown

    X20, Y20, Z20 = Bools('X20 Y20 Z20')
    
    s20 = Solver()
    
    #20. ¬(X ∧ Y) ↔ ¬X ∨ ¬Y       
    # As proposition in PL: ~(X /\ Y) == (~X \/ ~Y)
    #If the not of X and Y is true, then it is equal to not X or not Y.
    C20 = Not(And(X20, Y20)) == Or(Not(X20), Not(Y20))
    
    s20.add(Not(C20))
    # I believe it is valid
  
    r20 = s20.check()
    
    # If there's a model/solution return it 
    if (r20 == unsat):
        print("C20 is valid")
    # otherwise return inconsistent value for error
    else :
        print("C20 is not valid. Here's a counter-example: ", s20.model())


hw2()

