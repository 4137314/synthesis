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

/-- Electrical conductance, the reciprocal dimension of resistance (siemens). -/
def conductance : Dimension := { length := -2, mass := -1, time := 3, current := 2 }

/-- Capacitance, charge per voltage (farad). -/
def capacitance : Dimension := { length := -2, mass := -1, time := 4, current := 2 }

/-- Inductance, magnetic flux linkage per current (henry). -/
def inductance : Dimension := { length := 2, mass := 1, time := -2, current := -2 }

/-- Magnetic flux (weber); distinct from energy despite sharing no exponent pattern. -/
def magneticFlux : Dimension := { length := 2, mass := 1, time := -2, current := -1 }

/-- Frequency and angular frequency share reciprocal-time exponents. Radians are
dimensionless, so this tag does not separate hertz from radian per second. -/
def frequency : Dimension := { time := -1 }

/-- Electric field strength, voltage per length. -/
def electricField : Dimension := { length := 1, mass := 1, time := -3, current := -1 }

def mul (a b : Dimension) : Dimension :=
  ⟨a.length + b.length, a.mass + b.mass, a.time + b.time,
   a.current + b.current, a.temperature + b.temperature,
   a.amount + b.amount, a.luminosity + b.luminosity⟩

/-- Reciprocal dimension; every SI exponent is negated. -/
def inv (a : Dimension) : Dimension :=
  ⟨-a.length, -a.mass, -a.time, -a.current, -a.temperature, -a.amount, -a.luminosity⟩

/-- Quotient dimension, defined through multiplication by the reciprocal. -/
def div (a b : Dimension) : Dimension := a.mul b.inv

theorem mul_assoc (a b c : Dimension) : (a.mul b).mul c = a.mul (b.mul c) := by
  cases a; cases b; cases c
  simp [mul, Int.add_assoc]

theorem mul_comm (a b : Dimension) : a.mul b = b.mul a := by
  cases a; cases b
  simp [mul, Int.add_comm]

theorem mul_scalar (a : Dimension) : a.mul scalar = a := by
  cases a
  simp [mul, scalar]

theorem scalar_mul (a : Dimension) : scalar.mul a = a := by
  rw [mul_comm, mul_scalar]

theorem mul_inv_cancel (a : Dimension) : a.mul a.inv = scalar := by
  cases a
  simp only [mul, inv, scalar, Dimension.mk.injEq]
  omega

theorem inv_mul_cancel (a : Dimension) : a.inv.mul a = scalar := by
  rw [mul_comm, mul_inv_cancel]

theorem inv_inv (a : Dimension) : a.inv.inv = a := by
  cases a
  simp [inv]

theorem inv_scalar : scalar.inv = scalar := by decide

theorem div_self (a : Dimension) : a.div a = scalar := mul_inv_cancel a

theorem div_scalar (a : Dimension) : a.div scalar = a := by
  rw [div, inv_scalar, mul_scalar]

/-- Cancellation makes a quotient dimension recover its numerator factor. -/
theorem mul_div_cancel (a b : Dimension) : (a.mul b).div b = a := by
  rw [div, mul_assoc, mul_inv_cancel, mul_scalar]

theorem div_mul_cancel (a b : Dimension) : (a.div b).mul b = a := by
  rw [div, mul_assoc, inv_mul_cancel, mul_scalar]

theorem inv_mul (a b : Dimension) : (a.mul b).inv = a.inv.mul b.inv := by
  cases a; cases b
  simp only [mul, inv, Dimension.mk.injEq]
  omega

/-- Ohm's law, Joule's law and the reactive constitutive laws are dimensionally exact. -/
theorem resistance_current : resistance.mul currentDim = voltage := by decide

theorem voltage_current : voltage.mul currentDim = power := by decide

theorem voltage_over_current : voltage.div currentDim = resistance := by decide

theorem conductance_voltage : conductance.mul voltage = currentDim := by decide

theorem conductance_inv_resistance : resistance.inv = conductance := by decide

theorem resistance_inv_conductance : conductance.inv = resistance := by decide

theorem capacitance_voltage : capacitance.mul voltage = charge := by decide

theorem charge_over_voltage : charge.div voltage = capacitance := by decide

theorem inductance_current : inductance.mul currentDim = magneticFlux := by decide

theorem flux_over_current : magneticFlux.div currentDim = inductance := by decide

theorem charge_over_time : charge.div timeDim = currentDim := by decide

theorem voltage_charge : voltage.mul charge = energy := by decide

theorem energy_over_time : energy.div timeDim = power := by decide

theorem resistance_capacitance_time : resistance.mul capacitance = timeDim := by decide

theorem inductance_over_resistance : inductance.div resistance = timeDim := by decide

/-- The angular resonance frequency of an LC pair squares to the reciprocal product. -/
theorem inductance_capacitance : (inductance.mul capacitance) = timeDim.mul timeDim := by decide

theorem inductance_frequency : inductance.mul frequency = resistance := by decide

theorem capacitance_frequency : (capacitance.mul frequency).inv = resistance := by decide

theorem electric_field_length : electricField.mul lengthDim = voltage := by decide

end Dimension

/-- A small embedded expression language. Addition is dimension preserving by construction.
Variables are symbolic; binding and numerical evaluation belong to future elaboration passes. -/
inductive Expr : Dimension → Type where
  | literal {d} (value : Int) : Expr d
  | symbol {d} (name : String) : Expr d
  | add {d} : Expr d → Expr d → Expr d
  | mul {a b} : Expr a → Expr b → Expr (a.mul b)

end Synthesis
