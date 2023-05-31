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