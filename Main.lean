-- Chapter 1 --
def add1 (n : Nat) : Nat := n + 1

def maximum (n : Nat) (k : Nat) : Nat :=
  if n > k then n else k

def joinStringsWidth (a b c : String) : String :=
  String.append b (String.append a c)

#eval joinStringsWidth ", " "one" "and another"
#check joinStringsWidth ": "

def Str : Type := String
def aStr : Str := "This is a string."
#check aStr

abbrev N : Type := Nat
def thirtyNine : N := 39

#check thirtyNine

structure Point where
  x : Float
  y : Float
deriving Repr

def origin : Point := { x := 0.0, y := 0.0 }

def distance (p1 p2 : Point) :=
  let dx := p1.x - p2.x
  let dy := p1.y - p2.y
  Float.sqrt (dx*dx + dy*dy)

structure Point3D where
  x : Float
  y : Float
  z : Float
deriving Repr

#eval { x := 0, y := 0 : Point }

def zeroX (p : Point) : Point := { p with x := 0 }

#eval zeroX { x := 10, y := 20 }

#check Point.mk

def fourAndThree : Point :=
  { x := 4.3, y := 3.4 }

def Point.modifyBoth (f : Float → Float) (p : Point) : Point :=
  { x := f p.x, y := f p.y }

#eval Point.modifyBoth Float.floor fourAndThree

#eval fourAndThree.modifyBoth Float.floor

structure RectanglarPrism where
  height : Float
  width : Float
  depth : Float
deriving Repr

def volume (p : RectanglarPrism) : Float :=
  p.height * p.width * p.depth

#eval volume { height := 3, width := 4, depth := 5 }

structure Segment where
  p1 : Point
  p2 : Point
deriving Repr

def length (s : Segment) : Float :=
  distance s.p1 s.p2

#eval length { p1 := { x := 0, y := 0 }, p2 := { x := 3, y := 4 } }

-- 1.5 Datatypes and Patterns

def pred (n : Nat) : Nat :=
  match n with
  | Nat.zero => Nat.zero
  | Nat.succ k => k

#eval pred 800

def depth (p : Point3D) : Float :=
  match p with
  | { x := _, y := _, z := z } => z

def plus (n k : Nat) : Nat :=
  match k with
  | Nat.zero => n
  | Nat.succ k₂ => Nat.succ (plus n k₂)

#eval plus 3 4

-- 1.6 Polymorphism

structure PPoint (α : Type) where
  x : α
  y : α
deriving Repr

def natOrigin : PPoint Nat :=
  { x := 0, y := 0 }

def replaceX (α : Type) (point : PPoint α) (newX : α) : PPoint α :=
  { point with x := newX }

#check (replaceX)

inductive Sign where
  | pos
  | neg

def posOrNegThree (s : Sign) : match s with | Sign.pos => Nat | Sign.neg => Int :=
  match s with
  | Sign.pos => 3
  | Sign.neg => -3

#check posOrNegThree Sign.pos

inductive MyList (α : Type) where
  | nil : MyList α
  | cons : α → MyList α → MyList α

def explicitPrimesUnder10 : MyList Nat :=
  MyList.cons 2 (MyList.cons 3 (MyList.cons 5 (MyList.cons 7 MyList.nil)))

def mylength (α : Type) (xs : MyList α) : Nat :=
  match xs with
  | MyList.nil => 0
  | MyList.cons _ xs => 1 + mylength α xs

#eval mylength Nat explicitPrimesUnder10

def replaceX₂ {α : Type} (point : PPoint α) (newX : α) : PPoint α :=
  { point with x := newX }

#eval replaceX₂ natOrigin 5

def mylength₂ {α : Type} (xs : List α) : Nat :=
  match xs with
  | [] => 0
  | _ :: ys => Nat.succ (mylength₂ ys)

def List.head?₂ {α : Type} : List α → Option α
  | [] => none
  | x :: _ => some x

#eval List.head?₂ [] (α := Nat)

def List.last? {α : Type} : List α → Option α
  | [] => none
  | [x] => some x
  | _ :: xs => List.last? xs

#eval List.last? [1, 2, 3, 4, 5]
#eval List.last? [1]
#eval List.last? ([] : List Nat)

def List.findFirst? {α : Type} (p : α → Bool) : List α → Option α
  | [] => none
  | x :: xs => if p x then some x else List.findFirst? p xs

#eval List.findFirst? (λ x => x > 3) [1, 2, 3, 4, 5]
#eval List.findFirst? (λ x => x > 3) [1, 2, 3]

def Prod.swap {α β : Type} : Prod α β → Prod β α
  | (a, b) => (b, a)

#eval Prod.swap (1, 2)
#check Prod.swap (1, 2)

def zip {α β : Type} (xs : List α) (ys : List β) : List (Prod α β) :=
  match xs, ys with
  | [], _ => []
  | _, [] => []
  | x :: xs, y :: ys => (x, y) :: zip xs ys

#eval zip [1, 2, 3] ["one", "two", "three"]

def take {α : Type} : Nat → List α → List α
  | 0, _ => []
  | _, [] => []
  | n+1, x :: xs => x :: take n xs

#eval take 3 [1, 2, 3, 4, 5]
#eval take 3 [1, 2]

-- Using the analogy between types and arithmetic, write a function that distributes products over sums. In other words, it should have type α × (β ⊕ γ) → (α × β) ⊕ (α × γ).
def distribute {α β γ : Type} : Prod α (Sum β γ) → Sum (Prod α β) (Prod α γ)
  | (a, Sum.inl b) => Sum.inl (a, b)
  | (a, Sum.inr c) => Sum.inr (a, c)

#check distribute

-- Using the analogy between types and arithmetic, write a function that turns multiplication by two into a sum. In other words, it should have type Bool × α → α ⊕ α.
def doubleToSum {α : Type} : Prod Bool α → Sum α α
  | (true, a) => Sum.inl a
  | (false, a) => Sum.inr a

#check doubleToSum
#check Sum.inl 3 (β := String)

-- 1.7 Additional Conveniences

def length₃ (xs : List α) : Nat :=
  match xs with
  | [] => 0
  | _ :: ys => Nat.succ (length₃ ys)

#eval length₃ [1, 2, 3, 4, 5]

def length₄ : List α → Nat
  | [] => 0
  | _ :: ys => Nat.succ (length₄ ys)

#eval length₄ [1, 2, 3, 4, 5]

def unzip : List (α × β) → List α × List β
  | [] => ([], [])
  | (x, y) :: xyz =>
    let unzipped : List α × List β := unzip xyz
    (x :: unzipped.fst, y :: unzipped.snd)

def unzip₂ (pairs : List (α × β)) :=
  match pairs with
  | [] => ([], [])
  | (x, y) :: xyz =>
    let (xs, ys) := unzip₂ xyz
    (x :: xs, y :: ys)

def even₂ : Nat → Bool
  | 0 => true
  | n + 1 => not (even₂ n)

def halve : Nat → Nat
  | 0 => 0
  | 1 => 0
  | n + 2 => halve n + 1

#eval (fun x => x + 1) 4
#eval (· + 1) 4

namespace NewNamespace
  def triple (x : Nat) : Nat := 3 * x
  def quadruple (x : Nat) : Nat := 4 * x
end NewNamespace

#check NewNamespace.triple

def timesTwelve (x : Nat) :=
  open NewNamespace in
  quadruple (triple x)

inductive Inline : Type where
  | lineBreak
  | string : String → Inline
  | emph : Inline → Inline
  | strong : Inline → Inline

def Inline.string? (inline : Inline) : Option String :=
  match inline with
  | Inline.string s => some s
  | _ => none

def Inline.string?₂ (inline : Inline) : Option String :=
  if let Inline.string s := inline then
    some s
  else none

#eval (⟨1, 2⟩ : Point)

#eval s!"three fives is {NewNamespace.triple 5}"

-- Chapter 2 --
def main₁ : IO Unit := IO.println "Hello, world!"

-- lean --run chapter2.lean
-- Hello, world!

def main₂ : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout

  stdout.putStrLn "How would you like to be addressed?"
  -- Using an arrow means that the value of the expression is an IO action that
  -- should be executed, with the result of the action saved in the local
  -- variable.
  let input ← stdin.getLine
  let name := input.dropRightWhile Char.isWhitespace

  stdout.putStrLn s!"Hello, {name}!"

-- #eval "Hello!!!".dropRightWhile (· == '!')

def nTimes (action : IO Unit) : Nat → IO Unit
  | 0 => pure ()
  | n + 1 => do
    action
    nTimes action n

def main₃ := nTimes (IO.println "Hello, world!") 3

def main₄ : IO Unit := do
  (← IO.getStdout).putStrLn "Hello, world!!"

-- Watch out for execution order with this convenience!
def getNumA : IO Nat := do
  (← IO.getStdout).putStrLn "A"
  pure 5

def getNumB : IO Nat := do
  (← IO.getStdout).putStrLn "B"
  pure 6

def main₅ : IO Unit := do
  let a : Nat := if (← getNumA) == 5 then 0 else (← getNumB)
  (← IO.getStdout).putStrLn s!"Is {a}!"
-- A
-- B
-- Is 0!

def main := main₅

-- Chapter 3 --
def onePlusOneIsTwo : 1 + 1 = 2 := rfl

def OnePlusOneIsTwo : Prop := 1 + 1 = 2
theorem onePlusOneIsTwo₂ : OnePlusOneIsTwo := rfl

theorem onePlusOneIsTwo₃ : 1 + 1 = 2 := by
  simp

theorem addAndAppend : 1 + 1 = 2 ∧ "Str".append "ing" = "String" := by simp

theorem andImpliesOr : A ∧ B → A ∨ B :=
  fun andEvidence =>
    match andEvidence with
    | And.intro a _ => Or.inl a

def third (xs : List α) (ok : xs.length > 2) : α := xs[2]
#eval third [1, 2, 3] (by simp)

-- exercises
theorem twoPlusThreeIsFive : 2 + 3 = 5 := rfl
theorem fifteenMinusEightIsSeven : 15 - 8 = 7 := rfl
theorem helloWorldAppend : "Hello, ".append "world!" = "Hello, world!" := rfl
-- rfl checks =, we need simp
theorem fiveLessThanEighteen : 5 < 18 := by simp

theorem twoPlusThreeIsFive₂ : 2 + 3 = 5 := by simp
theorem fifteenMinusEightIsSeven₂ : 15 - 8 = 7 := by simp
theorem helloWorldAppend₂ : "Hello, ".append "world!" = "Hello, world!" := by simp

def fifth (xs : List α) (ok : xs.length > 4) : α := xs[4]

-- Chapter 4 --
class Plus (α : Type) where
  plus : α → α → α

instance : Plus Nat where
  plus := Nat.add

inductive Pos : Type where
  | one : Pos
  | succ : Pos -> Pos

def seven : Pos :=
  Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ Pos.one)))))

def Pos.plus : Pos → Pos → Pos
  | Pos.one, k => Pos.succ k
  | Pos.succ n, k => Pos.succ (n.plus k)

instance : Plus Pos where
  plus := Pos.plus

open Plus (plus)

def fourteen : Pos := plus seven seven

-- Gain access to `+`
instance : Add Pos where
  add := plus

def fourteen₂ : Pos := seven + seven

def posToString (atTop : Bool) (p : Pos) : String :=
  let paren s := if atTop then s else "(" ++ s ++ ")"
  match p with
  | Pos.one => "Pos.one"
  | Pos.succ n => paren s!"Pos.succ {posToString false n}"

instance : ToString Pos where
  toString := posToString true

#eval s!"There are {seven}"

-- Probably better to just convert to a Nat, which has a toString
def Pos.toNat : Pos → Nat
  | Pos.one => 1
  | Pos.succ n => n.toNat + 1

instance : ToString Pos where
  toString x := toString (x.toNat)

#eval s!"There are {seven}"

def Pos.mul : Pos → Pos → Pos
  | Pos.one, k => k
  | Pos.succ n, k => k + n.mul k

instance : Mul Pos where
  mul := Pos.mul

#eval seven * seven

inductive LT4 where
  | zero
  | one
  | two
  | three
deriving Repr

instance : OfNat LT4 0 where
  ofNat := LT4.zero

instance : OfNat LT4 1 where
  ofNat := LT4.one

instance : OfNat LT4 2 where
  ofNat := LT4.two

instance : OfNat LT4 3 where
  ofNat := LT4.three

#eval (3 : LT4)
-- #eval (4 : LT4)

instance : OfNat Pos (n + 1) where
  ofNat :=
    let rec natPlusOne : Nat → Pos
      | 0 => Pos.one
      | n + 1 => Pos.succ (natPlusOne n)
    natPlusOne n

#eval (3 : Pos)
-- #eval (0 : Pos)

structure Pos₂ where
  succ ::
  pred : Nat

def Pos₂.plus : Pos₂ → Pos₂ → Pos₂
  | Pos₂.succ n, Pos₂.succ m => Pos₂.succ (n + m + 1)

instance : Add Pos₂ where
  add := Pos₂.plus

def nine := Pos₂.succ 3 + Pos₂.succ 4
#eval nine.pred

def Pos₂.mul : Pos₂ → Pos₂ → Pos₂
  | Pos₂.succ n, Pos₂.succ m => Pos₂.succ (n * m + n + m)

instance : Mul Pos₂ where
  mul := Pos₂.mul

def thirtyThree := Pos₂.succ 2 * Pos₂.succ 10
#eval thirtyThree.pred

def Pos₂.toNat : Pos₂ → Nat
  | Pos₂.succ n => n + 1

def pos₂ToString : Pos₂ → String
  | Pos₂.succ n => toString (n + 1)

instance : ToString Pos₂ where
  toString := pos₂ToString

#eval thirtyThree

instance : OfNat Pos₂ (n + 1) where
  ofNat := Pos₂.succ n

#eval (12 : Pos₂)
-- #eval (0 : Pos₂)   -- so cool lol

inductive Even where
  | zero
  | plusTwo : Even → Even

def two := Even.plusTwo Even.zero

def Even.add : Even → Even → Even
  | Even.zero, m => m
  | n, Even.zero => n
  | Even.plusTwo n, Even.plusTwo m => Even.plusTwo (Even.plusTwo (Even.add n m))
instance : Add Even where
  add := Even.add

def four := two + two

def Even.mul : Even → Even → Even
  | Even.zero, _ => Even.zero
  | _, Even.zero => Even.zero
  | Even.plusTwo n, Even.plusTwo m =>
    -- (n + 2)(m + 2) = nm + 2n + 2m + 4
    Even.mul n m + (Even.add n n) + (Even.add m m) + four
instance : Mul Even where
  mul := Even.mul

def sixteen := four * four

def Even.toNat : Even → Nat
  | Even.zero => 0
  | Even.plusTwo n => n.toNat + 2

instance : ToString Even where
  toString n := toString (Even.toNat n)

#eval sixteen

-- can't do OfNat quite yet, because we can't destruct n * 2

def List.sum [Add α] [OfNat α 0] : List α → α
  | [] => 0
  | x :: xs => x + xs.sum

#eval [1, 2, 3, 4].sum
-- #eval ([1, 2, 3, 4] : List Pos).sum

instance [Add α] : Add (PPoint α) where
  add p1 p2 := { x := p1.x + p2.x, y := p1.y + p2.y }

instance : OfNat Even Nat.zero where
  ofNat := Even.zero

#eval (0 : Even)

instance [OfNat Even n] : OfNat Even (n + 2) where
  ofNat := Even.plusTwo (OfNat.ofNat n)

#eval (42 : Even)
-- #eval (3 : Even)
-- #eval (88888 : Even)
-- maximum number of heartbeats (20000) has been reached

def addNatPos : Nat → Pos → Pos
  | 0, p => p
  | n + 1, p => Pos.succ (addNatPos n p)

def addPosNat : Pos → Nat → Pos
  | p, 0 => p
  | p, n + 1 => Pos.succ (addPosNat p n)

-- Sadly these cannot be used with Add
#check @Add.add
-- {α : Type u_1} → [self : Add α] → α → α → α

-- we can use HAdd, though!
#check @HAdd.hAdd
-- {α : Type u_1} → {β : Type u_2} → {γ : outParam (Type u_3)} → [self : HAdd α β γ] → α → β → γ

instance : HAdd Nat Pos Pos where
  hAdd := addNatPos
instance : HAdd Pos Nat Pos where
  hAdd := addPosNat

#eval (3 : Pos) + (5 : Nat)

-- outParam!
class HPlus (α : Type) (β : Type) (γ : outParam Type) where
  hPlus : α → β → γ

instance : HPlus Nat Pos Pos where
  hPlus := addNatPos
instance : HPlus Pos Nat Pos where
  hPlus := addPosNat

#eval HPlus.hPlus (3 : Pos) (5 : Nat)

instance [Add α] : HPlus α α α where
  hPlus := Add.add

#eval HPlus.hPlus (3 : Pos) (5 : Nat)
#check HPlus.hPlus (3 : Pos) (5 : Nat)
-- HPlus.hPlus 3 5 : Pos
#check HPlus.hPlus (3 : Pos)
-- HPlus.hPlus 3 : ?m.148395 → ?m.148397
-- weird!!

@[default_instance]
instance [Add α] : HPlus α α α where
  hPlus := Add.add

#check HPlus.hPlus (3 : Pos)
-- HPlus.hPlus 3 : Pos → Pos

instance [Mul α]: HMul (PPoint α) α (PPoint α) where
  hMul p n := { x := p.x * n, y := p.y * n }

#eval ({ x := 3, y := 4 } : PPoint Nat) * 5
#eval ({ x := 2.5, y := 3.7 } : PPoint Float) * 2.0
#check HMul.hMul ({ x := 3, y := 4 } : PPoint Nat)
-- HMul.hMul { x := 3, y := 4 } : ?m.154201 → ?m.154203

@[default_instance]
instance [Mul α]: HMul (PPoint α) α (PPoint α) where
  hMul p n := { x := p.x * n, y := p.y * n }

#check HMul.hMul ({ x := 3, y := 4 } : PPoint Nat)
-- HMul.hMul { x := 3, y := 4 } : Nat → PPoint Nat

def northernTrees : Array String :=
  #["sloe", "birch", "elm", "oak"]
#eval northernTrees[2]
-- #eval northernTrees[8]

structure NonEmptyList (α : Type) : Type where
  head : α
  tail : List α

def idahoSpiders : NonEmptyList String := {
  head := "Banded Garden Spider",
  tail := [
    "Long-legged Sac Spider",
    "Wolf Spider",
    "Hobo Spider",
    "Cat-faced Spider"
  ]
}

def NonEmptyList.get? : NonEmptyList α → Nat → Option α
  | xs, 0 => some xs.head
  | xs, n + 1 => xs.tail.get? n

abbrev NonEmptyList.inBounds (xs : NonEmptyList α) (i : Nat) : Prop :=
  i ≤ xs.tail.length

theorem atLeastThreeSpiders : idahoSpiders.inBounds 2 := by simp
theorem notSixSpiders : ¬idahoSpiders.inBounds 5 := by simp

def NonEmptyList.get (xs : NonEmptyList α) (i : Nat) (ok : xs.inBounds i) : α :=
  match i with
  | 0 => xs.head
  | n + 1 => xs.tail[n]

instance : GetElem (NonEmptyList α) Nat α NonEmptyList.inBounds where
  getElem := NonEmptyList.get

instance : GetElem (List α) Pos α (fun list n => list.length > n.toNat) where
  getElem (xs : List α) (i : Pos) ok := xs[i.toNat]

instance : GetElem (PPoint α) Bool α (fun _ _ => true) where
  getElem (p : PPoint α) (i : Bool) _ :=
    if ¬i then p.x else p.y

def Pos.comp : Pos → Pos → Ordering
  | Pos.one, Pos.one => Ordering.eq
  | Pos.one, _ => Ordering.lt
  | _, Pos.one => Ordering.gt
  | Pos.succ n, Pos.succ k => comp n k

instance : Ord Pos where
  compare := Pos.comp

def hashPos : Pos → UInt64
  | Pos.one => 1
  | Pos.succ n => mixHash 1 (hashPos n)

instance : Hashable Pos where
  hash := hashPos

instance [Hashable α] : Hashable (NonEmptyList α) where
  hash xs := mixHash (hash xs.head) (hash xs.tail)

inductive BinTree (α : Type) where
  | leaf : BinTree α
  | branch : BinTree α → α → BinTree α → BinTree α

def eqBinTree [BEq α] : BinTree α → BinTree α → Bool
  | BinTree.leaf, BinTree.leaf => true
  | BinTree.branch l x r, BinTree.branch l₂ x₂ r₂ =>
    x == x₂ && eqBinTree l l₂ && eqBinTree r r₂
  | _, _ => false

def hashBinTree [Hashable α] : BinTree α → UInt64
  | BinTree.leaf => 0
  | BinTree.branch l x r =>
    mixHash 1 (mixHash (hashBinTree l) (mixHash (hash x) (hashBinTree r)))

instance [Hashable α] : Hashable (BinTree α) where
  hash := hashBinTree

-- We can add a few standard classes easily
deriving instance BEq, Hashable, Repr for NonEmptyList

instance : Append (NonEmptyList α) where
  append xs ys := {
    head := xs.head,
    tail := xs.tail ++ ys.head :: ys.tail
  }

#eval idahoSpiders ++ idahoSpiders

instance : HAppend (NonEmptyList α) (List α) (NonEmptyList α) where
  hAppend xs ys := {
    head := xs.head,
    tail := xs.tail ++ ys
  }

#eval idahoSpiders ++ ["Trapdoor Spider"]

#eval (· + 5) <$> [1, 2, 3]

instance : Functor NonEmptyList where
  map f xs := {
    head := f xs.head,
    tail := f <$> xs.tail
  }

instance : Functor PPoint where
  map f p := {
    x := f p.x,
    y := f p.y
  }

def concat [Append α] (xs : NonEmptyList α) : α :=
  let rec catList (start : α) : List α → α
    | [] => start
    | z :: zs => catList (start ++ z) zs
  catList xs.head xs.tail

instance : HAppend (List α) (NonEmptyList α) (NonEmptyList α) where
  hAppend xs ys :=
    match xs with
      | [] => ys
      | z :: zs => {
        head := z,
        tail := zs ++ ys.head :: ys.tail
      }

#eval (["Trapdoor Spider"] ++ idahoSpiders)
#eval (([] : List String) ++ idahoSpiders)

deriving instance BEq, Hashable, Repr for BinTree

def BinTree.map (f : α → β) : BinTree α → BinTree β
  | BinTree.leaf => BinTree.leaf
  | BinTree.branch l x r =>
    BinTree.branch (BinTree.map f l) (f x) (BinTree.map f r)

instance : Functor BinTree where
  map := BinTree.map

#eval (· + 5) <$> BinTree.branch BinTree.leaf 3 BinTree.leaf

instance : Coe Pos Nat where
  coe x := x.toNat

#eval [1, 2, 3, 4].drop (2 : Pos)

def oneInt : Int := Pos.one
-- This is possible because Coe Nat Int exists!

inductive A where | a
inductive B where | b deriving Repr
instance : Coe A B where
  coe _ := B.b
instance : Coe B A where
  coe _ := A.a
instance : Coe Unit A where
  coe _ := A.a

def coercedToB : B := ()
#eval coercedToB

def List.last?₂ : List α → Option α
  | [] => none
  | [x] => x  -- no need to use `some x`!
  | _ :: x :: xs => last?₂ (x :: xs)

def perhapsPerhapsPerhaps : Option (Option (Option String)) :=
  "Please don't tell me"

def perhapsPerhapsPerhapsNat : Option (Option (Option Nat)) :=
  (392 : Nat)

def perhapsPerhapsPerhapsNat₂ : Option (Option (Option Nat)) :=
  ↑(392 : Nat)

instance : Coe (NonEmptyList α) (List α) where
  coe
    | { head := x, tail := xs } => x :: xs

instance : CoeDep (List α) (x :: xs) (NonEmptyList α) where
  coe := { head := x, tail := xs }

#eval ([1, 2, 3] : NonEmptyList Nat)
--#eval ([] : NonEmptyList Nat)

structure Monoid where
  Carrier : Type
  neutral : Carrier
  op : Carrier → Carrier → Carrier

def natMulMonoid : Monoid :=
  { Carrier := Nat, neutral := 1, op := (· * ·) }

def natAddMonoid : Monoid :=
  { Carrier := Nat, neutral := 0, op := (· + ·) }

def stringMonoid : Monoid :=
  { Carrier := String, neutral := "", op := (· ++ ·) }

def listMonoid (α : Type) : Monoid :=
  { Carrier := List α, neutral := [], op := (· ++ ·) }

def foldMap (M : Monoid) (f : α → M.Carrier) (xs : List α) : M.Carrier :=
  let rec go (soFar : M.Carrier) : List α → M.Carrier
    | [] => soFar
    | y :: ys => go (M.op soFar (f y)) ys
  go M.neutral xs

instance : CoeSort Monoid Type where
  coe m := m.Carrier

-- now we can avoid M.Carrier
def foldMap₂ (M : Monoid) (f : α → M) (xs : List α) : M :=
  let rec go (soFar : M) : List α → M
    | [] => soFar
    | y :: ys => go (M.op soFar (f y)) ys
  go M.neutral xs

-- coerce booleans into `= true` propositions
instance : CoeSort Bool Prop where
  coe b := b = true

-- coerce into functions with CoeFun
structure Adder where howMuch : Nat
def add5 : Adder := ⟨5⟩

instance : CoeFun Adder (fun _ => Nat → Nat ) where
  coe a := (· + a.howMuch)

#eval add5 3

inductive JSON where
  | true : JSON
  | false : JSON
  | null : JSON
  | string : String → JSON
  | number : Float → JSON
  | object : List (String × JSON) → JSON
  | array : List JSON → JSON
deriving Repr

structure Serializer where
  Contents : Type
  serialize : Contents → JSON

def Str₂ : Serializer :=
  { Contents := String,
    serialize := JSON.string
  }

instance : CoeFun Serializer (fun s => s.Contents → JSON) where
  coe s := s.serialize

def buildResponse (title : String) (R : Serializer) (record : R.Contents) : JSON :=
  JSON.object [
    ("title", JSON.string title),
    ("status", JSON.number 200),
    ("record", R record)
  ]

#eval buildResponse "Hello" Str₂ "World"

-- Neat, we can write a Pos serializer as well
def Pos' : Serializer :=
  { Contents := Pos,
    serialize := fun x => JSON.number (x.toNat.toFloat)
  }

#eval buildResponse "Hello" Pos' (392 : Pos)

structure Tree : Type where
  latinName : String
  commonNames : List String

-- The following syntaxes are equivalent
def oak : Tree :=
  ⟨"Quercus robur", ["common oak", "European oak"]⟩

def birch : Tree :=
  { latinName := "Betula pendula",
    commonNames := ["silver birch", "qarty birch"]
  }

def sloe : Tree where
  latinName := "Prunus spinosa"
  commonNames := ["sloe", "blackthorn"]

class Display (α : Type) where
  displayName : α → String

-- Similarly, for typeclass instances
instance : Display Tree :=
  ⟨Tree.latinName⟩

instance : Display Tree :=
  { displayName := Tree.latinName }

instance : Display Tree where
  displayName := Tree.latinName

-- example is helpful
example : NonEmptyList String :=
  { head := "Sparrow",
    tail := ["Robin", "Blackbird"]
  }
example (n : Nat) (k : Nat) : Bool :=
  n + k == k + n
