import Mathlib

/-!
# DSA5210 Session 3 Demo

Complete classroom demo for:

* structures with data fields and proof fields;
* classes, instance search, notation, coercions, and inheritance;
* inductive types and structural induction;
* recursive functions, `termination_by`, and `decreasing_by`;
* a Sharkovskii-style period-order running example.

The file is meant to be run locally from the course root with:

```bash
./scripts/lean-nus.sh nus-dsa/lean/Session03/Demo.lean
```

Expected failures from the slides are kept as comments so the whole file
typechecks.
-/

namespace DSA5210
namespace Session03

/-!
## 1. Structures package data and proof fields
-/

structure Point2D where
  x : Int
  y : Int
  deriving Repr

#check Point2D.mk
#eval Point2D.mk 1 2

def p : Point2D where
  x := 3
  y := -2

def q : Point2D := ⟨1, 1⟩

#print q
#eval q
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

variable (n : Nat)

def I1 : ClosedInterval where
  left := 3
  right := 5
  valid := by decide

def intervalFrom (n : Nat) : ClosedInterval where
  left := n
  right := n + 2
  valid := by simp only [le_add_iff_nonneg_right, zero_le]

#check intervalFrom
#check (intervalFrom n).valid

example (I : ClosedInterval) :
    ∃ i, I.left ≤ i ∧ i ≤ I.right := by
  use I.left
  constructor
  · simp only [Std.le_refl]
  · exact I.valid

#check Fin
#print Fin

def secondOfFive : Fin 5 :=
  ⟨2, by decide⟩

/-!
Expected error if uncommented: `Fin 5` and `Fin 6` are different types.

```lean
#check (2 : Fin 5) = (2 : Fin 6)
```
-/

#check (2 : Fin 5) = (2 : Nat)
#eval (Finset.univ : Finset (Fin 5))
#check (2 : Fin 5)
#synth OfNat (Fin 5) 2
#eval secondOfFive.val
#check secondOfFive.isLt

/-!
## 2. Classes, notation, and instance search
-/

/-!
Expected error if uncommented: no addition interface between `Nat` and
`String` has been registered yet.

```lean
#check 42 + "hi"
```
-/

#eval 42 + 2
#check HAdd
#check HAdd.hAdd
#synth HAdd Nat Nat Nat

/-!
The following instance would make `Nat + String` return a `Nat`.
Keep it commented so the classroom file has only one active `HAdd Nat String`
instance.

```lean
instance haddNatString1 : HAdd Nat String Nat where
  hAdd := fun a b => a + b.length
```
-/

instance haddNatString2 : HAdd Nat String String where
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

variable {alpha : Type}

#check Preorder
#check le_rfl
#check le_trans

example [Preorder alpha] (a : alpha) : a ≤ a :=
  le_rfl

example [Preorder alpha] {a b c : alpha}
    (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c :=
  le_trans hab hbc

namespace DiamondDemo

/-!
This is a real diamond-shaped class hierarchy. `AsNat` and `AsBool` both
extend `HasLabel`. If they are installed independently with different inherited
`HasLabel` data, asking for only `[HasLabel Token]` leaves Lean to choose an
available path by instance search.
-/

class HasLabel (α : Type) where
  label : String

class AsNat (α : Type) extends HasLabel α where
  n : Nat

class AsBool (α : Type) extends HasLabel α where
  b : Bool

inductive Token where
  | token

instance : AsNat Token where
  label := "Nat path"
  n := 0

instance : AsBool Token where
  label := "Bool path"
  b := true

#check (inferInstance : AsNat Token)
#check (inferInstance : AsBool Token)
#check (inferInstance : HasLabel Token)
#eval (inferInstance : HasLabel Token).label

end DiamondDemo

/-!
## 3. Inductive types
-/

inductive MyBool where
  | false : MyBool
  | true : MyBool

#check MyBool.false
#check MyBool.true

inductive MyTree (alpha : Type) where
  | nil : MyTree alpha
  | node : alpha -> MyTree alpha -> MyTree alpha -> MyTree alpha
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

#eval t1
#eval leftOnly
#eval rightOnly

end MyTree

inductive BadTree (alpha : Type) where
  | leaf : alpha -> BadTree alpha
  | node : BadTree alpha -> BadTree alpha -> BadTree alpha
  deriving Repr

namespace BadTree

def b1 : BadTree Nat :=
  leaf 3

def b2 : BadTree Nat :=
  node (leaf 1) (leaf 2)

end BadTree

inductive GTree (alpha : Type) where
  | node : alpha -> List (GTree alpha) -> GTree alpha
  deriving Repr

namespace GTree

def leaf (a : alpha) : GTree alpha :=
  node a []

def gt1 : GTree Nat :=
  node 3 []

def gt2 : GTree Nat :=
  node 1 [node 2 [], node 3 []]

def gt3 : GTree Nat :=
  node 0 [gt1, gt2]

#eval gt1
#eval gt2

end GTree

/-!
## 4. Natural-number induction
-/

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
## 5. Recursion from constructors
-/

namespace Sharkovskii

def oddPart : Nat -> Nat
  | 0 => 0
  | n + 1 =>
      if (n + 1) % 2 = 0 then
        oddPart ((n + 1) / 2)
      else
        n + 1
termination_by k => k
decreasing_by
  exact Nat.div_lt_self (Nat.succ_pos n) (by decide)

def twoAdic : Nat -> Nat
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

/-!
Bad generated style from the notes. It typechecks, but the extra `fuel`
argument hides the mathematical operation.
-/

def stripTwosAux : Nat -> Nat -> Nat
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

namespace MyTree

def depth : MyTree alpha -> Nat
  | nil => 0
  | node _ l r => Nat.max (depth l) (depth r) + 1

def size : MyTree alpha -> Nat
  | nil => 0
  | node _ l r => 1 + size l + size r

def mirror : MyTree alpha -> MyTree alpha
  | nil => nil
  | node a l r => node a (mirror r) (mirror l)

#eval depth t3
#eval size t3
#eval mirror t3

theorem size_mirror (t : MyTree alpha) :
    size (mirror t) = size t := by
  induction t with
  | nil =>
      rfl
  | node a l r ihl ihr =>
      simp [mirror, size, ihl, ihr]
      omega

end MyTree

namespace GTree

def size : GTree alpha -> Nat
  | node _ children => 1 + children.foldl (fun acc t => acc + size t) 0

def depth : GTree alpha -> Nat
  | node _ children => 1 + children.foldl (fun acc t => Nat.max acc (depth t)) 0

#eval size gt3
#eval depth gt3

end GTree

/-!
## 6. Termination
-/

def factorial : Nat -> Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

#eval factorial 5

/-!
Expected failure if uncommented: the recursive call is made on exactly the
same input in the successor branch.

```lean
def bad : Nat -> Nat
  | 0 => 0
  | n + 1 => bad (n + 1)
```
-/

/-!
## 7. Well-founded induction and general recursion
-/

#check Acc
#check Acc.intro
#check WellFounded

example {α : Type} {r : α -> α -> Prop}
    (wf : WellFounded r)
    (P : α -> Prop)
    (step : ∀ x, (∀ y, r y x -> P y) -> P x)
    (x : α) : P x :=
  wf.induction x step

#check Tree
#check Tree.node
#check Tree.numNodes

example (P : Tree α -> Prop)
    (step : ∀ t : Tree α,
      (∀ s : Tree α, Tree.numNodes s < Tree.numNodes t -> P s) -> P t) :
    ∀ t : Tree α, P t := by
  intro t
  exact (InvImage.wf Tree.numNodes wellFounded_lt).induction t step

def euclid : Nat -> Nat -> Nat
  | a, 0 => a
  | a, b + 1 => euclid (b + 1) (a % (b + 1))
termination_by _ b => b
decreasing_by
  exact Nat.mod_lt a (Nat.succ_pos b)

#eval euclid 30 12

#check Nat.strong_induction_on

example (P : Nat -> Prop)
    (step : ∀ n, (∀ m, m < n -> P m) -> P n) :
    ∀ n, P n := by
  intro n
  exact Nat.strong_induction_on n step

/-!
## 8. Sharkovskii-style period order
-/

namespace Dynamics

def iterate {X : Type} (f : X -> X) : Nat -> X -> X
  | 0, x => x
  | n + 1, x => f (iterate f n x)

def ReturnsAfter {X : Type} (f : X -> X) (n : Nat) (x : X) : Prop :=
  iterate f n x = x

def IsPeriodicPoint {X : Type} (f : X -> X) (n : Nat) (x : X) : Prop :=
  0 < n ∧ ReturnsAfter f n x

def HasExactPeriod {X : Type} (f : X -> X) (n : Nat) (x : X) : Prop :=
  IsPeriodicPoint f n x ∧
    ∀ m : Nat, 0 < m -> m < n -> ¬ ReturnsAfter f m x

def HasPointOfExactPeriod {X : Type} (f : X -> X) (n : Nat) : Prop :=
  ∃ x : X, HasExactPeriod f n x

end Dynamics

namespace Sharkovskii

abbrev sharkLE (m n : Nat) : Prop :=
  n = 0 ∨
    (1 < oddPart m ∧ oddPart n = 1) ∨
    (1 < oddPart m ∧ 1 < oddPart n ∧
      (twoAdic m < twoAdic n ∨
        (twoAdic m = twoAdic n ∧ oddPart m ≤ oddPart n))) ∨
    (oddPart m = 1 ∧ oddPart n = 1 ∧ n ≤ m)

infix:50 " ≼ₛ " => sharkLE

#check sharkLE
#check (3 ≼ₛ 5)

#eval decide (3 ≼ₛ 5)
#eval decide (5 ≼ₛ 6)
#eval decide (6 ≼ₛ 5)
#eval decide (8 ≼ₛ 4)
#eval decide (4 ≼ₛ 8)
#eval decide (1 ≼ₛ 0)
#eval decide (0 ≼ₛ 1)

def SharkovskiiTheoremStatement
    {I : Type}
    (IsContinuousIntervalMap : (I -> I) -> Prop) : Prop :=
  ∀ f : I -> I, IsContinuousIntervalMap f ->
    ∀ m n : Nat, 0 < n -> m ≼ₛ n ->
      Dynamics.HasPointOfExactPeriod f m ->
      Dynamics.HasPointOfExactPeriod f n

#check SharkovskiiTheoremStatement

end Sharkovskii

/-!
## 9. Order interfaces
-/

#check PartialOrder
#check le_antisymm

example [PartialOrder alpha] {a b : alpha}
    (hab : a ≤ b) (hba : b ≤ a) : a = b :=
  le_antisymm hab hba

#check Nat.instPreorder
#check Nat.instPartialOrder
#check LinearOrder

end Session03
end DSA5210
