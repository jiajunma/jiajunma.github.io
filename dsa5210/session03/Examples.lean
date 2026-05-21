import Mathlib

/-!
# DSA5210 Session 3 Lean Examples

This file collects the runnable Lean examples discussed in the Session 3 notes
and slides. It is intended as the student-facing companion file: every active
declaration below should typecheck. Examples that are meant to fail in class
are left in comments.

Run from the course root with:

```bash
./scripts/lean-nus.sh nus-dsa/lean/Session03/Examples.lean
```
-/

namespace DSA5210
namespace Session03Examples

/-!
## Structures, proof fields, and `Fin`
-/

structure Point2D where
  x : Int
  y : Int
  deriving Repr

def p : Point2D where
  x := 3
  y := -2

def q : Point2D := ⟨1, 1⟩

#check Point2D.mk
#eval Point2D.mk 1 2
#eval p.x + p.y

def Point2D.sumxy (p : Point2D) : Int :=
  p.x + p.y

def Point2D.add (p q : Point2D) : Point2D :=
  ⟨p.x + q.x, p.y + q.y⟩

#eval p.sumxy
#eval p.add q

structure ClosedInterval where
  left : Nat
  right : Nat
  valid : left ≤ right

def intervalFrom (n : Nat) : ClosedInterval where
  left := n
  right := n + 2
  valid := by simp only [le_add_iff_nonneg_right, zero_le]

example (I : ClosedInterval) :
    ∃ i, I.left ≤ i ∧ i ≤ I.right := by
  use I.left
  constructor
  · simp only [Std.le_refl]
  · exact I.valid

def secondOfFive : Fin 5 :=
  ⟨2, by decide⟩

#check Fin
#check (2 : Fin 5) = (2 : Nat)
#eval (Finset.univ : Finset (Fin 5))
#eval secondOfFive.val
#check secondOfFive.isLt

/-!
Expected failure if uncommented: `Fin 5` and `Fin 6` are different types.

```lean
#check (2 : Fin 5) = (2 : Fin 6)
```
-/

namespace HEqDemo

def finTypeAddComm (n : Nat) : Fin (1 + n) = Fin (n + 1) := by
  grind

example (n : Nat) : HEq (0 : Fin (n + 1)) (0 : Fin (1 + n)) := by
  grind

theorem fin_heq_ext_iff {k l : Nat} (h : k = l) {i : Fin k} {j : Fin l} :
    i ≍ j ↔ (i : Nat) = (j : Nat) := by
  subst h
  constructor
  · intro h
    have := eq_of_heq h
    rw [this]
  · intro h
    have := Fin.eq_of_val_eq h
    exact heq_of_eq this

#print fin_heq_ext_iff

end HEqDemo

/-!
## Classes, notation, inheritance, and instance search
-/

#eval 42 + 2
#check HAdd
#check HAdd.hAdd
#synth HAdd Nat Nat Nat

/-!
Expected failure if uncommented: Lean has no active `HAdd Nat String ?m`
instance before we register one.

```lean
#check 42 + "hi"
```
-/

instance haddNatString : HAdd Nat String String where
  hAdd := fun a b => toString a ++ b

#synth HAdd Nat String String
#eval 42 + "hi"

instance stringToNat : Coe String Nat where
  coe s := s.length

#eval ("hi" : Nat)
#eval (42 + "hi" : Nat)
#eval (42 + "hi" : String)

#check OfNat
#synth OfNat (Fin 5) 2
#check (2 : Fin 5)

#check LE
#check LE.le
#synth LE Nat

variable {α : Type}

#check Preorder
#check le_rfl
#check le_trans

example [Preorder α] (a : α) : a ≤ a :=
  le_rfl

example [Preorder α] {a b c : α}
    (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c :=
  le_trans hab hbc

namespace DiamondDemo

class HasLabel (α : Type) where
  label : String

class AsNat (α : Type) extends HasLabel α where
  n : Nat

class AsBool (α : Type) extends HasLabel α where
  b : Bool

inductive Token where
  | token

instance I2 : AsBool Token where
  label := "Bool path"
  b := true

instance I1 : AsNat Token where
  label := "Nat path"
  n := 0

def t1 : String :=
  letI : HasLabel Token := I1.toHasLabel
  (inferInstance : HasLabel Token).label

def t2 : String :=
  (inferInstance : HasLabel Token).label

#eval t1
#eval t2

end DiamondDemo

/-!
## Inductive types and induction
-/

inductive MyBool where
  | false : MyBool
  | true : MyBool

#check MyBool.false
#check MyBool.true

inductive MyTree (α : Type) where
  | nil : MyTree α
  | node : α → MyTree α → MyTree α → MyTree α
  deriving Repr

namespace MyTree

def t1 : MyTree Nat :=
  node 3 nil nil

def leftOnly : MyTree Nat :=
  node 2 (node 1 nil nil) nil

def rightOnly : MyTree Nat :=
  node 2 nil (node 3 nil nil)

def t3 : MyTree Nat :=
  node 5 leftOnly rightOnly

def depth : MyTree α → Nat
  | nil => 0
  | node _ l r => Nat.max (depth l) (depth r) + 1

def size : MyTree α → Nat
  | nil => 0
  | node _ l r => 1 + size l + size r

def mirror : MyTree α → MyTree α
  | nil => nil
  | node a l r => node a (mirror r) (mirror l)

#eval t1
#eval leftOnly
#eval rightOnly
#eval depth t3
#eval size t3
#eval mirror t3

theorem size_mirror (t : MyTree α) :
    size (mirror t) = size t := by
  induction t with
  | nil =>
      rfl
  | node a l r ihl ihr =>
      simp [mirror, size, ihl, ihr]
      omega

end MyTree

inductive BadTree (α : Type) where
  | leaf : α → BadTree α
  | node : BadTree α → BadTree α → BadTree α
  deriving Repr

namespace BadTree

def b1 : BadTree Nat :=
  leaf 3

def b2 : BadTree Nat :=
  node (leaf 1) (leaf 2)

end BadTree

inductive GTree (α : Type) where
  | node : α → List (GTree α) → GTree α
  deriving Repr

namespace GTree

def leaf (a : α) : GTree α :=
  node a []

def gt1 : GTree Nat :=
  node 3 []

def gt2 : GTree Nat :=
  node 1 [node 2 [], node 3 []]

def gt3 : GTree Nat :=
  node 0 [gt1, gt2]

def size : GTree α → Nat
  | node _ children => 1 + children.foldl (fun acc t => acc + size t) 0

def depth : GTree α → Nat
  | node _ children => 1 + children.foldl (fun acc t => Nat.max acc (depth t)) 0

#eval gt1
#eval gt2
#eval size gt3
#eval depth gt3

end GTree

theorem add_one_eq_one_add (i : Nat) :
    i + 1 = 1 + i := by
  induction i with
  | zero =>
      rfl
  | succ i ih =>
      calc
        (i + 1) + 1 = (1 + i) + 1 := by rw [ih]
        _ = 1 + (i + 1) := by rw [Nat.add_assoc]

/-!
## Recursion, `termination_by`, and `decreasing_by`
-/

def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

#eval factorial 5

namespace Sharkovskii

def oddPart : Nat → Nat
  | 0 => 0
  | n + 1 =>
      if (n + 1) % 2 = 0 then
        oddPart ((n + 1) / 2)
      else
        n + 1
termination_by k => k
decreasing_by
  exact Nat.div_lt_self (Nat.succ_pos n) (by decide)

def twoAdic : Nat → Nat
  | 0 => 0
  | n + 1 =>
      if (n + 1) % 2 = 0 then
        twoAdic ((n + 1) / 2) + 1
      else
        0
termination_by k => k
decreasing_by
  exact Nat.div_lt_self (Nat.succ_pos n) (by decide)

#eval oddPart 0
#eval oddPart 12
#eval twoAdic 12
#eval oddPart 40
#eval twoAdic 40

def stripTwosAux : Nat → Nat → Nat
  | 0, n => n
  | fuel + 1, n =>
      if n % 2 = 0 && n != 0 then
        stripTwosAux fuel (n / 2)
      else
        n

def oddPartWithFuel (n : Nat) : Nat :=
  stripTwosAux n n

#eval oddPartWithFuel 40

end Sharkovskii

/-!
Expected failure if uncommented: the recursive call is made on exactly the same
input in the successor branch.

```lean
def bad : Nat → Nat
  | 0 => 0
  | n + 1 => bad (n + 1)
```
-/

def euclid : Nat → Nat → Nat
  | a, 0 => a
  | a, b + 1 => euclid (b + 1) (a % (b + 1))
termination_by _ b => b
decreasing_by
  exact Nat.mod_lt a (Nat.succ_pos b)

#eval euclid 30 12

/-!
## Well-founded induction
-/

#check Acc
#check Acc.intro
#check WellFounded

example {α : Type} {r : α → α → Prop}
    (wf : WellFounded r)
    (P : α → Prop)
    (step : ∀ x, (∀ y, r y x → P y) → P x)
    (x : α) : P x :=
  wf.induction x step

#check Tree
#check Tree.node
#check Tree.numNodes

example (P : Tree α → Prop)
    (step : ∀ t : Tree α,
      (∀ s : Tree α, Tree.numNodes s < Tree.numNodes t → P s) → P t) :
    ∀ t : Tree α, P t := by
  intro t
  exact (InvImage.wf Tree.numNodes wellFounded_lt).induction t step

#check Nat.strong_induction_on

example (P : Nat → Prop)
    (step : ∀ n, (∀ m, m < n → P m) → P n) :
    ∀ n, P n := by
  intro n
  exact Nat.strong_induction_on n step

/-!
## Dynamics and Sharkovskii-style period order
-/

namespace Dynamics

def iterate {X : Type} (f : X → X) : Nat → X → X
  | 0, x => x
  | n + 1, x => f (iterate f n x)

def orbit {X : Type} (f : X → X) (x : X) : Set X :=
  Set.range (fun n : Nat => iterate f n x)

noncomputable def exactPeriod {X : Type} (f : X → X) (x : X) : Nat :=
  (orbit f x).ncard

def HasPointOfExactPeriod {X : Type} (f : X → X) (n : Nat) : Prop :=
  ∃ x : X, exactPeriod f x = n

def ReturnsAfter {X : Type} (f : X → X) (n : Nat) (x : X) : Prop :=
  iterate f n x = x

def IsPeriodicPoint {X : Type} (f : X → X) (n : Nat) (x : X) : Prop :=
  0 < n ∧ ReturnsAfter f n x

def HasExactPeriodByReturnTime {X : Type} (f : X → X) (n : Nat) (x : X) : Prop :=
  IsPeriodicPoint f n x ∧
    ∀ m : Nat, 0 < m → m < n → ¬ ReturnsAfter f m x

end Dynamics

namespace Sharkovskii

abbrev SharOrder (m n : Nat) : Prop :=
  (1 < oddPart m ∧ oddPart n = 1) ∨
    (1 < oddPart m ∧ 1 < oddPart n ∧
      (twoAdic m < twoAdic n ∨
        (twoAdic m = twoAdic n ∧ oddPart m ≤ oddPart n))) ∨
    (oddPart m = 1 ∧ oddPart n = 1 ∧ n ≤ m)

infix:50 " ≼ₛ " => SharOrder

#check SharOrder
#check (3 ≼ₛ 5)
#eval decide (3 ≼ₛ 5)
#eval decide (5 ≼ₛ 6)
#eval decide (6 ≼ₛ 5)
#eval decide (8 ≼ₛ 4)
#eval decide (4 ≼ₛ 8)

def SharkovskiiTheoremStatement
    {I : Type}
    (IsContinuousIntervalMap : (I → I) → Prop) : Prop :=
  ∀ f : I → I, IsContinuousIntervalMap f →
    ∀ m n : Nat, 0 < m → 0 < n → m ≼ₛ n →
      Dynamics.HasPointOfExactPeriod f m →
      Dynamics.HasPointOfExactPeriod f n

#check SharkovskiiTheoremStatement

end Sharkovskii

#check PartialOrder
#check le_antisymm

example [PartialOrder α] {a b : α}
    (hab : a ≤ b) (hba : b ≤ a) : a = b :=
  le_antisymm hab hba

#check Nat.instPreorder
#check Nat.instPartialOrder
#check LinearOrder

end Session03Examples
end DSA5210
