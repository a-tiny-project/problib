namespace Foundations.Linear.Rational

structure Dual where
  primal : Rat
  tangent : Rat
deriving DecidableEq, Repr

namespace Dual

def constant (value : Rat) : Dual :=
  { primal := value, tangent := 0 }

def add (left right : Dual) : Dual :=
  { primal := left.primal + right.primal
    tangent := left.tangent + right.tangent }

def mul (left right : Dual) : Dual :=
  { primal := left.primal * right.primal
    tangent := left.tangent * right.primal + left.primal * right.tangent }

def scale (constant : Rat) (value : Dual) : Dual :=
  { primal := constant * value.primal
    tangent := constant * value.tangent }

@[simp] theorem constant_primal (value : Rat) :
    (constant value).primal = value :=
  rfl

@[simp] theorem constant_tangent (value : Rat) :
    (constant value).tangent = 0 :=
  rfl

@[simp] theorem add_primal (left right : Dual) :
    (add left right).primal = left.primal + right.primal :=
  rfl

@[simp] theorem add_tangent (left right : Dual) :
    (add left right).tangent = left.tangent + right.tangent :=
  rfl

@[simp] theorem mul_primal (left right : Dual) :
    (mul left right).primal = left.primal * right.primal :=
  rfl

@[simp] theorem mul_tangent (left right : Dual) :
    (mul left right).tangent =
      left.tangent * right.primal + left.primal * right.tangent :=
  rfl

@[simp] theorem scale_primal (constant : Rat) (value : Dual) :
    (scale constant value).primal = constant * value.primal :=
  rfl

@[simp] theorem scale_tangent (constant : Rat) (value : Dual) :
    (scale constant value).tangent = constant * value.tangent :=
  rfl

end Dual

end Foundations.Linear.Rational
