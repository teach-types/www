module checksize where

{-

 Lecture 5: how big is the derivation that the deduction theorem builds?

 A closed element of  nil ⊢ X  is a finite TREE of var/axK/axS/mp, so
 we can simply count its nodes with a function  size  defined by
 structural recursion.  Evaluating  size d  normalises d first, so
 this measures the NORMAL FORM of the derivation.

 Each theorem below is proved twice: once via the deduction theorem
 (dedcor2, dedW, dedcor4, dedcor5, dedcor6) and once directly, placing
 S and K by hand (flipImp, wImp, compImp, constImp, applyImp).

    theorem                        direct   via dedthm   nestings
    ---------------------------    ------   ----------   --------
    flip   (X=>Y=>Z)=>Y=>X=>Z        19        161          3
    W      (X=>X=>Y)=>X=>Y           11         59          2
    comp   (A=>B)=>(B=>C)=>A=>C      27        161          3
    const  A=>B=>C=>A                 7         29          3
    apply  A=>(A=>B)=>B              25         35          2

 The table is checked by the ten equations at the end of this file:
 they typecheck only if the numbers are right.

-}

open import deduction

{-# BUILTIN NATURAL Nat #-}

size : {G : context} -> {X : Form} -> G ⊢ X -> Nat
size (var x)   = 1
size axK       = 1
size axS       = 1
size (mp d1 d2) = suc (size d1 + size d2)

A0 A1 A2 : Form
A0 = atom 0
A1 = atom 1
A2 = atom 2

-- flip
t1 : Id Nat (size (flipImp {nil} {A0} {A1} {A2})) 19
t1 = refl 19
t2 : Id Nat (size (dedcor2 {nil} {A0} {A1} {A2})) 161
t2 = refl 161

-- W (contraction)
t3 : Id Nat (size (wImp {nil} {A0} {A1})) 11
t3 = refl 11
t4 : Id Nat (size (dedW {nil} {A0} {A1})) 59
t4 = refl 59

-- composition
t5 : Id Nat (size (compImp {nil} {A0} {A1} {A2})) 27
t5 = refl 27
t6 : Id Nat (size (dedcor4 {nil} {A0} {A1} {A2})) 161
t6 = refl 161

-- constant
t7 : Id Nat (size (constImp {nil} {A0} {A1} {A2})) 7
t7 = refl 7
t8 : Id Nat (size (dedcor5 {nil} {A0} {A1} {A2})) 29
t8 = refl 29

-- apply
t9 : Id Nat (size (applyImp {nil} {A0} {A1})) 25
t9 = refl 25
t10 : Id Nat (size (dedcor6 {nil} {A0} {A1})) 35
t10 = refl 35
