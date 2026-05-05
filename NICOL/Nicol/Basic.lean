import Mathlib.Tactic

namespace Nicol

def A0 : Int := 407389224418
def A1 : Int := 76343678551

def C : Int := A1^2 - A0*A1 - A0^2

def A : Nat -> Int
| 0 => A0
| 1 => A1
| n+2 => A (n+1) + A n

def Q (n : Nat) : Int :=
  (A (n+1))^2 - (A (n+1)) * (A n) - (A n)^2

@[simp]
theorem A_rec (n : Nat) : A (n+2) = A (n+1) + A n := by
  rfl

theorem Q_succ_neg (n : Nat) : Q (n+1) = - Q n := by
  unfold Q
  rw [A_rec n]
  ring

theorem Q_zero : Q 0 = C := by
  unfold Q C A A0 A1
  norm_num

theorem Q_closed (n : Nat) : Q n = C * (-1 : Int)^n := by
  induction n with
  | zero =>
      rw [Q_zero]
      norm_num
  | succ n ih =>
      rw [Q_succ_neg n, ih]
      rw [pow_succ]
      ring

theorem completed_square_identity (n : Nat) :
    (2 * A (n+1) - A n)^2 =
      5 * (A n)^2 + 4 * C * (-1 : Int)^n := by
  have h := Q_closed n
  unfold Q at h
  nlinarith

end Nicol
