namespace Synthesis

/-- SI base-dimension exponents; quantities are expressed in coherent SI units. -/
structure Dimension where
  length : Int := 0
  mass : Int := 0
  time : Int := 0
  current : Int := 0
  temperature : Int := 0
  amount : Int := 0
  luminosity : Int := 0
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

namespace Dimension

def scalar : Dimension := {}
def lengthDim : Dimension := { length := 1 }
def timeDim : Dimension := { time := 1 }
def temperatureDim : Dimension := { temperature := 1 }
def massDim : Dimension := { mass := 1 }
def currentDim : Dimension := { current := 1 }
def amountDim : Dimension := { amount := 1 }
def energy : Dimension := { length := 2, mass := 1, time := -2 }
def power : Dimension := { length := 2, mass := 1, time := -3 }
def force : Dimension := { length := 1, mass := 1, time := -2 }
def pressure : Dimension := { length := -1, mass := 1, time := -2 }
def charge : Dimension := { current := 1, time := 1 }
def resistance : Dimension := { length := 2, mass := 1, time := -3, current := -2 }
def thermalConductance : Dimension := { length := 2, mass := 1, time := -3, temperature := -1 }
def voltage : Dimension := { length := 2, mass := 1, time := -3, current := -1 }
def mul (a b : Dimension) : Dimension :=
  ⟨a.length + b.length, a.mass + b.mass, a.time + b.time,
   a.current + b.current, a.temperature + b.temperature,
   a.amount + b.amount, a.luminosity + b.luminosity⟩

theorem mul_assoc (a b c : Dimension) : (a.mul b).mul c = a.mul (b.mul c) := by
  cases a; cases b; cases c
  simp [mul, Int.add_assoc]

theorem mul_comm (a b : Dimension) : a.mul b = b.mul a := by
  cases a; cases b
  simp [mul, Int.add_comm]

theorem mul_scalar (a : Dimension) : a.mul scalar = a := by
  cases a
  simp [mul, scalar]

end Dimension

/-- A small embedded expression language. Addition is dimension preserving by construction.
Variables are symbolic; binding and numerical evaluation belong to future elaboration passes. -/
inductive Expr : Dimension → Type where
  | literal {d} (value : Int) : Expr d
  | symbol {d} (name : String) : Expr d
  | add {d} : Expr d → Expr d → Expr d
  | mul {a b} : Expr a → Expr b → Expr (a.mul b)

end Synthesis
