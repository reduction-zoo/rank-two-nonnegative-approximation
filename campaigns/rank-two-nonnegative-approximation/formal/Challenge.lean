module

public import Mathlib.Computability.TuringMachine.Computable
public import Mathlib.Analysis.Real.Sqrt

@[expose] public section

namespace RankTwoNonnegativeApproximation

/-- Q001's self-delimiting binary natural; length is logarithmic, not unary. -/
def encodeNat (n : Nat) : List Bool :=
  let bits := (Nat.toDigits 2 n).map (fun c => c == '1')
  List.replicate bits.length true ++ [false] ++ bits

def encodeList {α : Type} (encode : α → List Bool) (xs : List α) : List Bool :=
  encodeNat xs.length ++ xs.flatMap encode

def encodeOption {α : Type} (encode : α → List Bool) : Option α → List Bool
  | none => [false]
  | some x => true :: encode x

/-- None denotes mathematical nonexistence, never an execution error. -/
def searchOutput {I W : Type} (legal : I → Bool) (witness : I → W → Bool)
    (x : I) : Option W → Prop
  | some w => legal x = true ∧ witness x w = true
  | none => legal x = true ∧ ¬ ∃ w, witness x w = true

/-- Relational version for witnesses with quantified real or optimality conditions. -/
def relationalOutput {I W : Type} (legal : I → Bool) (witness : I → W → Prop)
    (x : I) : Option W → Prop
  | some w => legal x = true ∧ witness x w
  | none => legal x = true ∧ ¬ ∃ w, witness x w

structure Formula where
  n : Nat
  clauses : List (List (Nat × Bool))
  deriving Repr

def legalSource (x : Formula) : Bool :=
  x.clauses.all (fun c => c.length ≤ 3 && c.all (fun l => l.1 < x.n))

def sourceWitness (x : Formula) (a : List Bool) : Bool :=
  a.length == x.n && x.clauses.all (fun c => c.any (fun l => a[l.1]? == some l.2))

def encodeSource (x : Formula) : List Bool :=
  encodeNat x.n ++ encodeList (encodeList (fun l => encodeNat l.1 ++ [l.2])) x.clauses

def validSourceOutput := searchOutput legalSource sourceWitness
def encodeInt (z : Int) : List Bool := [decide (z < 0)] ++ encodeNat z.natAbs
def encodeRat (q : Rat) : List Bool := encodeInt q.num ++ encodeNat q.den

structure Instance where
  rows : Nat
  cols : Nat
  matrix : List (List Rat)
  threshold : Rat
  deriving Repr
def shape {α : Type} (rows cols : Nat) (a : List (List α)) : Bool :=
  a.length == rows && a.all (fun row => row.length == cols)
def legalTarget (x : Instance) : Bool := shape x.rows x.cols x.matrix &&
  x.matrix.all (fun row => row.all (· ≥ 0)) && x.threshold ≥ 0
def realEntry (a : List (List ℝ)) (i j : Nat) : ℝ := (a[i]?.getD [])[j]?.getD 0
def squaredError (x : Instance) (w h : List (List ℝ)) : ℝ :=
  ((List.range x.rows).flatMap (fun i => (List.range x.cols).map (fun j =>
    ((((x.matrix[i]?.getD [])[j]?.getD 0 : Rat) : ℝ) -
      (realEntry w i 0 * realEntry h 0 j + realEntry w i 1 * realEntry h 1 j))^2))).sum
def targetYes (x : Instance) : Prop := ∃ w h : List (List ℝ),
  shape x.rows 2 w = true ∧ shape 2 x.cols h = true ∧
  (∀ row ∈ w, ∀ value ∈ row, 0 ≤ value) ∧ (∀ row ∈ h, ∀ value ∈ row, 0 ≤ value) ∧
  squaredError x w h ≤ (x.threshold : ℝ)
def validTargetOutput (x : Instance) (answer : Bool) : Prop := legalTarget x = true ∧ (answer = true ↔ targetYes x)
def encodeTarget (x : Instance) := encodeList encodeNat (List.range x.rows) ++ encodeList encodeNat (List.range x.cols) ++
  encodeList (encodeList encodeRat) x.matrix ++ encodeRat x.threshold

def Reduction (forward : Formula → Instance) : Prop :=
  Nonempty (Turing.TM2ComputableInPolyTime encodeSource encodeTarget forward) ∧
  (∃ bound : Polynomial Nat, ∀ x, (encodeTarget (forward x)).length ≤ bound.eval (encodeSource x).length) ∧
  (∀ x, legalSource x = true → legalTarget (forward x) = true) ∧
  (∀ x, legalSource x = true → ((∃ a, sourceWitness x a = true) ↔ targetYes (forward x)))

def Goal : Prop := ∃ forward, Reduction forward

/-- Open question only; this placeholder is not a solution. -/
theorem solve : Goal := by
  sorry

end RankTwoNonnegativeApproximation
