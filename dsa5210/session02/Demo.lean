import Mathlib

/-!
# DSA5210 Session 2 Demo

Complete classroom demo for:

* terms, types, and judgments
* definitional equality and `rfl`
* overloaded notation and a first typeclass-instance example
* propositions and judgments
* product and sum types
* `And`, `Or`, implication, `forall`
* `Σ`, `Subtype`, and `∃`
* inductive data, inductive propositions, recursion, and induction

The file is intentionally linear: in class, open it from top to bottom and
evaluate/check the declarations as they appear.

Teaching rhythm:

1. Read the type of each object before evaluating it.
2. For each constructor, ask what data it needs.
3. For each `match` or `induction`, connect the branches back to the
   constructors.
4. Treat proofs as very small examples of using constructors and eliminators,
   not as the main topic of the session.
-/

namespace DSA5210
namespace Session02

/-!
## 1. Terms, types, and judgments
-/

#check 42
-- 42 : ℕ
#check "hello"
-- "hello" : String
#check true
-- Bool.true : Bool
#check Nat
-- Nat : Type
#check Bool
-- Bool : Type
#check Type
-- Type : Type 1
#check Type 1
-- Type 1 : Type 2

-- Sort 0 is Prop
-- Sort 1 is Type
-- Sort 2 is Type 1

#check Type -> Type
-- Type → Type : Type 1
#check Type × Type
-- Type × Type : Type 1
#check Sigma (fun A : Type => A)
-- (A : Type) × A : Type 1
#check (ULift.{1,0} Nat)
-- ULift Nat : Type 1

universe u v
variable (A : Type u) (B : Type v)

#check A -> B
-- A → B : Type (max u v)
#check A × B
-- A × B : Type (max u v)
#check A ⊕ B
-- A ⊕ B : Type (max u v)
#check Type -> Type
-- Type → Type : Type 1
#check Type ⊕ Type
-- Type ⊕ Type : Type 1
#check Type 1 -> Type
-- Type 1 → Type : Type 2
#check Type 1 ⊕ Type
-- Type 1 ⊕ Type : Type 2
#check Type -> Type 1
-- Type → Type 1 : Type 2
#check Nat -> Bool
-- ℕ → Bool : Type
#check Nat ⊕ Bool
-- Nat ⊕ Bool : Type

#check Set
-- Set.{u} (α : Type u) : Type u
#check ({n : Nat | n ≠ n} : Set Nat)
-- {n | n ≠ n} : Set ℕ

/-!
The following expected error is only the Lean symptom of trying to use
set-theoretic self-membership syntax. The foundational point is universe
stratification: `Type : Type 1`, not `Type : Type`.

Expected error if uncommented:

```lean
#check (fun X : Type => X ∈ X)
```

Lean cannot synthesize:

```text
failed to synthesize instance of type class
  Membership Type Type
```
-/

#check 42 + 1
-- 42 + 1 : ℕ

/-!
Expected error if uncommented:

```lean
#check 42 + "hi"
```

Lean tries to synthesize an addition operation for `Nat` and `String`:

```text
failed to synthesize instance of type class
  HAdd ℕ String ?m.5
```
-/

/-!
## 2. Definitional equality and `rfl`
-/

example : 0 = 0 :=
  rfl

example (n : Nat) : n = n :=
  rfl

#reduce (fun n : Nat => n + 1) 3
-- 4
#reduce 2 + 3
-- 5

def onePlusOne : Nat := 1 + 1

#check onePlusOne
-- DSA5210.Session02.onePlusOne : ℕ
#reduce onePlusOne
-- 2
#print onePlusOne

def fact : Nat -> Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

#check fact
-- DSA5210.Session02.fact : ℕ → ℕ
#reduce fact 5
-- 120
#eval fact 5
-- 120
#eval fact 20
-- 2432902008176640000

/-!
Optional classroom extension:
-/

#eval Nat.factorization (fact 10) 2
-- 8
#eval Nat.factorization (fact 10) 3
-- 4

example : (fun n : Nat => n + 1) 3 = 4 :=
  rfl

example : 2 + 3 = 5 :=
  rfl

example : onePlusOne = 2 :=
  rfl

/-!
Expected error if uncommented:

```lean
example : 2 + 2 = 5 := rfl
```

Lean cannot close this by reflexivity because the two sides do not reduce to
the same expression.
-/

/-!
## 3. Overloaded notation and typeclass instances
-/

namespace HAddDemo

instance instHAddNatString : HAdd Nat String String where
  hAdd n s := toString n ++ s

#synth HAdd Nat String String
-- instHAddNatString
#check 42 + "hi"
-- 42 + "hi" : String
#eval 42 + "hi"
-- "42hi"

end HAddDemo

/-!
## 4. Propositions, proofs, and judgments
-/

#check Prop
-- Prop : Type
#check Type
-- Type : Type 1
#check Nat
-- Nat : Type
#check Bool
-- Bool : Type
#check true
-- Bool.true : Bool
#check false
-- Bool.false : Bool
#check 2 + 3 = 5
-- 2 + 3 = 5 : Prop
#check decide (2 + 3 = 5)
-- decide (2 + 3 = 5) : Bool
#eval decide (2 + 3 = 5)
-- true
#eval decide (2 + 3 = 6)
-- false
#check True
-- True : Prop
#check False
-- False : Prop

section Propositions

variable (P Q R : Prop)

/-!
Expected error if uncommented:

```lean
#check decide P
```

Lean cannot synthesize:

```text
failed to synthesize instance of type class
  Decidable P
```
-/

#check Classical.propDecidable
-- Classical.propDecidable (a : Prop) : Decidable a
#check Classical.propDecidable P
-- Classical.propDecidable P : Decidable P

noncomputable example : Decidable P :=
  Classical.propDecidable P

noncomputable def classicalDecision (P : Prop) : Bool :=
  @decide P (Classical.propDecidable P)

#check classicalDecision P
-- classicalDecision P : Bool

#check P
-- P : Prop
#check P -> Q
-- P → Q : Prop
#check ¬ P
-- ¬P : Prop
#check P -> False
-- P → False : Prop

example (hp : P) : P := hp

example (hp : P) (f : P -> Q) : Q :=
  f hp

example (hp : P) (f : P -> Q) : Q := by
  exact f hp

example (f : P -> Q) : P -> Q :=
  fun hp => f hp

example (f : P -> Q) : P -> Q := by
  intro hp
  exact f hp

#check (Nat -> Bool)
-- ℕ → Bool : Type
#check ((n : Nat) -> Fin (n + 1))
-- (n : ℕ) → Fin (n + 1) : Type
#check (Π n : Nat, Fin (n + 1))
-- (n : ℕ) → Fin (n + 1) : Type

example : Nat -> Nat :=
  fun n => n + 1

#eval (fun n : Nat => n + 1) 11
-- 12

example : (Π n : Nat, Fin (n + 1)) :=
  fun n => ⟨0, Nat.succ_pos n⟩

example : P -> P :=
  fun hp => hp

example (hp : P) (hpq : P -> Q) : Q :=
  hpq hp

example (hpq : P -> Q) : P -> Q := by
  intro hp
  exact hpq hp

example (hpq : P -> Q) (hqr : Q -> R) : P -> R :=
  fun hp => hqr (hpq hp)

example (hnot : ¬ P) (hp : P) : False :=
  hnot hp

example (h : P -> False) : ¬ P :=
  h

example (h : ¬ P) : P -> False :=
  h

#check False.elim
-- False.elim.{u} {C : Sort u} (h : False) : C
#check (False.elim : False -> P)
-- False.elim : False → P
#check (False.elim : False -> Nat)
-- False.elim : False → ℕ

example (hnot : ¬ P) (hp : P) : Q :=
  False.elim (hnot hp)

example (hnot : ¬ P) (hp : P) : Q := by
  exfalso
  exact hnot hp

end Propositions

/-!
## 5. Lean inspection commands
-/

def double (n : Nat) : Nat := n + n

#check double
-- double (n : ℕ) : ℕ
#eval double 21
-- 42
#reduce double (10 + 11)
-- 42
#print double

/-!
## 6. Product types
-/

def pair : Nat × Bool := Prod.mk 3 true
def pair' : Nat × Bool := ⟨3, true⟩

#check pair
-- pair : ℕ × Bool
#eval pair.1
-- 3
#eval pair.2
-- true
#eval pair'.1
-- 3
#eval pair'.2
-- true

def swapPair (x : Nat × Bool) : Bool × Nat :=
  ⟨x.2, x.1⟩

#eval (swapPair pair).1
-- true
#eval (swapPair pair).2
-- 3

section ProductAnd

variable (P Q : Prop)

#check P ∧ Q
-- P ∧ Q : Prop

example (hp : P) (hq : Q) : P ∧ Q :=
  And.intro hp hq

example (hp : P) (hq : Q) : P ∧ Q :=
  ⟨hp, hq⟩

example (h : P ∧ Q) : P :=
  h.left

example (h : P ∧ Q) : Q :=
  h.right

end ProductAnd

/-!
## 7. Sum types
-/

#check (Nat ⊕ String)
-- ℕ ⊕ String : Type

example : Nat ⊕ String := .inl 5
example : Nat ⊕ String := .inr "hi"

theorem inlOne_ne_inrOne :
    (Sum.inl 1 : Nat ⊕ Nat) ≠ Sum.inr 1 := by
  intro h
  cases h

/-!
Proof reading:

* `A ≠ B` means `A = B -> False`.
* The theorem compares the tags directly: `Sum.inl 1` versus `Sum.inr 1`.
* `intro h` assumes an equality between the two tagged values.
* `cases h` asks Lean to analyze that equality.
* There is no case: `Sum.inl` and `Sum.inr` are different constructors.
-/

section SumOr

variable (P Q R : Prop)

#check P ∨ Q
-- P ∨ Q : Prop

example (hp : P) : P ∨ Q :=
  Or.inl hp

example (hq : Q) : P ∨ Q :=
  Or.inr hq

example (h : P ∨ Q) (hp : P -> R) (hq : Q -> R) : R :=
  match h with
  | Or.inl proofOfP => hp proofOfP
  | Or.inr proofOfQ => hq proofOfQ

example (h1 h2 : P ∨ Q) : h1 = h2 :=
  Subsingleton.elim h1 h2

example (hp : P) (hq : Q) : (Or.inl hp : P ∨ Q) = Or.inr hq :=
  Subsingleton.elim (Or.inl hp) (Or.inr hq)

end SumOr

/-!
## 8. Types depending on values, Pi types, and universal quantification
-/

#check Fin
-- Fin (n : ℕ) : Type
#check Fin 0
-- Fin 0 : Type
#check Fin 1
-- Fin 1 : Type
#check Fin 3
-- Fin 3 : Type
#check (0 : Fin 1)
-- 0 : Fin 1
#check (2 : Fin 3)
-- 2 : Fin 3
#eval ((2 : Fin 3).val)
-- 2

#check Fin.castSucc
-- Fin.castSucc {n : ℕ} : Fin n → Fin (n + 1)
#eval (Fin.castSucc (2 : Fin 3)).val
-- 2

#check Fin.equivSubtype
-- Fin.equivSubtype {n : ℕ} : Fin n ≃ { i // i < n }
#eval (Fin.equivSubtype (2 : Fin 3)).val
-- 2
#eval (Fin.equivSubtype.symm (⟨2, by decide⟩ : {i : Nat // i < 3})).val
-- 2

#check ((n : Nat) -> Fin (n + 1))
-- (n : ℕ) → Fin (n + 1) : Type
#check (Π n : Nat, Fin (n + 1))
-- (n : ℕ) → Fin (n + 1) : Type

#check ((n : Nat) -> Fin n)
-- (n : ℕ) → Fin n : Type

example : ((n : Nat) -> Fin (n + 1)) :=
  fun n => ⟨0, Nat.succ_pos n⟩

example : (Π n : Nat, Fin (n + 1)) :=
  fun n => ⟨0, Nat.succ_pos n⟩

example : (Nat -> Nat) :=
  fun n => n + 1

#check (∀ n : Nat, n = n)
-- ∀ (n : ℕ), n = n : Prop

example : (∀ n : Nat, n = n) :=
  fun n => Eq.refl n

example : (∀ n : Nat, n = n) := by
  intro n
  rfl

example (P : Nat -> Prop) (h : ∀ n : Nat, P n) : P 3 :=
  h 3

def applyTwice (f : Nat -> Nat) (n : Nat) : Nat :=
  f (f n)

#eval applyTwice (fun n => n + 1) 10
-- 12

/-!
## 9. `Σ`, Subtype, and `∃`
-/

#check Sigma
-- Sigma.{u, v} {α : Type u} (β : α → Type v) : Type (max u v)
#check Subtype
-- Subtype.{u} {α : Sort u} (p : α → Prop) : Sort (max 1 u)
#check Exists
-- Exists.{u} {α : Sort u} (p : α → Prop) : Prop

#check (Σ n : Nat, Fin (n + 1))
-- (n : ℕ) × Fin (n + 1) : Type

/-!
Expected error if uncommented:

```lean
#check (Σ n : Nat, n > 5)
```

`Σ` expects a type-valued family, but `n > 5` is a proposition.

Expected error if uncommented:

```lean
#check (∃ n : Nat, Fin (n + 1))
```

`∃` expects a proposition-valued predicate, but `Fin (n + 1)` is a type.
-/

def sigmaExample : (Σ n : Nat, Fin (n + 1)) :=
  ⟨2, ⟨1, by decide⟩⟩

#eval sigmaExample.1
-- 2
#eval sigmaExample.2.val
-- 1
#check sigmaExample.2
-- sigmaExample.2 : Fin (sigmaExample.1 + 1)

def twoSigma : (Σ n : Nat, Fin (n + 1)) :=
  ⟨2, ⟨1, by decide⟩⟩

def threeSigma : (Σ n : Nat, Fin (n + 1)) :=
  ⟨3, ⟨1, by decide⟩⟩

theorem twoSigma_ne_threeSigma : twoSigma ≠ threeSigma := by
  intro h
  have hfst : twoSigma.1 = threeSigma.1 := congrArg Sigma.fst h
  norm_num [twoSigma, threeSigma] at hfst

def sixSubtype : {n : Nat // n > 5} :=
  ⟨6, by decide⟩

def sevenSubtype : {n : Nat // n > 5} :=
  ⟨7, by decide⟩

#eval sixSubtype.val
-- 6
#check sixSubtype.property
-- sixSubtype.property : ↑sixSubtype > 5

theorem sixSubtype_ne_sevenSubtype : sixSubtype ≠ sevenSubtype := by
  intro h
  have hval : sixSubtype.val = sevenSubtype.val := congrArg Subtype.val h
  norm_num [sixSubtype, sevenSubtype] at hval

def sixExists : ∃ n : Nat, n > 5 :=
  ⟨6, by decide⟩

def sevenExists : ∃ n : Nat, n > 5 :=
  ⟨7, by decide⟩

example : sixExists = sevenExists :=
  Subsingleton.elim sixExists sevenExists

example : ∃ n : Nat, n > 5 :=
  Exists.intro 6 (by decide)

theorem my_and_intro {P Q : Prop} (hp : P) (hq : Q) : P ∧ Q :=
  And.intro hp hq

theorem my_and_intro' : ∀ {P Q : Prop}, P -> Q -> P ∧ Q :=
  fun hp hq => And.intro hp hq

#check my_and_intro
-- DSA5210.Session02.my_and_intro {P Q : Prop} (hp : P) (hq : Q) : P ∧ Q
#check (∀ {P Q : Prop}, P -> Q -> P ∧ Q)
-- (∀ {P Q : Prop}, P → Q → P ∧ Q) : Prop
#check @my_and_intro
-- @my_and_intro : ∀ {P Q : Prop}, P → Q → P ∧ Q

def idExplicit (α : Type) (x : α) : α := x
def idImplicit {α : Type} (x : α) : α := x

#check idExplicit Nat 3
-- DSA5210.Session02.idExplicit ℕ 3 : ℕ
#check idImplicit 3
-- DSA5210.Session02.idImplicit 3 : ℕ
#check @idImplicit
-- @idImplicit : {α : Type} → α → α
#check idExplicit _ 3
-- idExplicit ℕ 3 : ℕ
#check @idImplicit _ 3
-- idImplicit 3 : ℕ

example {P Q : Prop} (hp : P) (hq : Q) : P ∧ Q :=
  @my_and_intro _ _ hp hq

/-!
Classroom point:

* `Σ` keeps data in `Type`.
* `Subtype` keeps the value as data and stores the property in `Prop`.
* `∃` is itself a proposition; proofs of the same proposition are not
  computational data you should inspect.
* `twoSigma` and `threeSigma` are distinguishable data.
* `sixExists` and `sevenExists` are equal as proofs of the same proposition.
* A useful classroom phrase: `∃` behaves like the proof-irrelevant quotient or
  truncation of a dependent-pair shape, not like inspectable witness data.
-/

/-!
## 10. Traditional inductive types
-/

inductive MyBool where
  | false : MyBool
  | true : MyBool
deriving Repr, DecidableEq

namespace MyBool

def not : MyBool -> MyBool
  | false => true
  | true => false

#eval not true
#eval not false

end MyBool

inductive MyNat where
  | zero : MyNat
  | succ : MyNat -> MyNat
deriving Repr

namespace MyNat

def two : MyNat :=
  succ (succ zero)

def toNat : MyNat -> Nat
  | zero => 0
  | succ n => toNat n + 1

#eval toNat zero
#eval toNat two

end MyNat

inductive MyList (α : Type) where
  | nil : MyList α
  | cons : α -> MyList α -> MyList α
deriving Repr

namespace MyList

def sample : MyList Nat :=
  cons 1 (cons 2 (cons 3 nil))

def length {α : Type} : MyList α -> Nat
  | nil => 0
  | cons _ xs => length xs + 1

def map {α β : Type} (f : α -> β) : MyList α -> MyList β
  | nil => nil
  | cons x xs => cons (f x) (map f xs)

#eval length sample
#eval map (fun n => n + 10) sample

end MyList

inductive Tree (α : Type) where
  | leaf : α -> Tree α
  | node : Tree α -> Tree α -> Tree α
deriving Repr

namespace Tree

def sample : Tree Nat :=
  node (leaf 1) (node (leaf 2) (leaf 3))

def size {α : Type} : Tree α -> Nat
  | leaf _ => 1
  | node l r => size l + size r + 1

#eval size sample

end Tree

/-!
## 11. Inductive propositions
-/

inductive MyEven : Nat -> Prop where
  | zero : MyEven 0
  | add_two {n : Nat} : MyEven n -> MyEven (n + 2)

namespace MyEven

example : MyEven 0 :=
  zero

example : MyEven 2 :=
  add_two zero

example : MyEven 4 :=
  add_two (add_two zero)

theorem four_even : MyEven 4 :=
  add_two (add_two zero)

end MyEven

/-!
## 12. Induction principles
-/

#check Nat.rec
#check List.rec
#check Nat.strongRec
#check Nat.strong_induction_on

theorem zero_add_demo (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Nat.add_succ, ih]

theorem MyList.length_map {α β : Type} (f : α -> β) (xs : MyList α) :
    MyList.length (MyList.map f xs) = MyList.length xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp [MyList.map, MyList.length, ih]

/-!
## 13. Termination and well-foundedness
-/

def countdown : Nat -> List Nat
  | 0 => [0]
  | n + 1 => (n + 1) :: countdown n

#eval countdown 5

def factorial : Nat -> Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

#eval factorial 5

def halfSteps : Nat -> Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => halfSteps (n + 1) + 1

#eval halfSteps 10

def euclid : Nat -> Nat -> Nat
  | a, 0 => a
  | a, b + 1 => euclid (b + 1) (a % (b + 1))
termination_by _ b => b
decreasing_by
  exact Nat.mod_lt a (Nat.succ_pos b)

#eval euclid 30 12

/-!
Lean accepts these definitions because recursive calls are on smaller data.
It will reject unrestricted loops such as:

```
def badLoop (n : Nat) : Nat := badLoop n
```

This is the operational side of well-foundedness: recursive definitions need a
reason why computation eventually terminates.
-/

end Session02
end DSA5210
