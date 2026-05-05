import Mathlib.Tactic
import Nicol.Basic
import Nicol.Covering

namespace Nicol

/-
  Modular certificates for the equation

      z^2 = 5 * p^(2k) + 4*C*epsilon

  where epsilon = +1 for even n and epsilon = -1 for odd n.

  The strategy is:
  - reduce modulo auxiliary primes ell;
  - compute p^(2k) modulo ell;
  - check whether the right-hand side is a square modulo ell;
  - eliminate all possible residue classes of k.

  The finite checks below certify all (p, parity) pairs arising from
  singly-covered classes in Nicol's original covering.

  In addition, we verify that each modulus M used for k is a valid period:
      (p^2)^M = 1 mod ell
  for every auxiliary prime ell in the corresponding certificate.
-/

def epsOfParity (par : Nat) : Int :=
  if par = 0 then 1 else -1

def modInt (a : Int) (m : Nat) : Nat :=
  Int.toNat (a.emod (m : Int))

/--
  Slow reference version:
      powModSlow a k m = a^k mod m.

  This is mathematically direct but inefficient for large k.
-/
def powModSlow (a k m : Nat) : Nat :=
  Nat.mod (a ^ k) m

/--
  Fast modular exponentiation by repeated squaring.

  This is the version used by the finite certificate checker. The previous
  slow definition `powModSlow` was also used successfully in an earlier
  full build of the same certificates.

  Informal invariant:
      acc * base^exp ≡ original_base^original_exp mod m.
-/
def powModFastAux (base acc m : Nat) : Nat → Nat
| 0 => acc % m
| e + 1 =>
    let exp := e + 1
    let base' := (base * base) % m
    if exp % 2 = 1 then
      powModFastAux base' ((acc * base) % m) m (exp / 2)
    else
      powModFastAux base' acc m (exp / 2)
termination_by exp => exp
decreasing_by
  all_goals
    apply Nat.div_lt_self
    · omega
    · decide

/--
  Fast version used by the modular certificate checker.
-/
def powMod (a k m : Nat) : Nat :=
  if m = 0 then 0 else powModFastAux (a % m) 1 m k

def rhsMod (p par k ell : Nat) : Nat :=
  let eps := epsOfParity par
  let p2 := (p * p) % ell
  let term1 : Int := 5 * (powMod p2 k ell : Int)
  let term2 : Int := 4 * C * eps
  modInt (term1 + term2) ell

def squaresMod (ell : Nat) : List Nat :=
  (List.range ell).map (fun z => (z * z) % ell)

def isSquareMod (x ell : Nat) : Bool :=
  (squaresMod ell).contains (x % ell)

def rhsIsSquareMod (p par k ell : Nat) : Bool :=
  isSquareMod (rhsMod p par k ell) ell

/--
  A single auxiliary prime ell eliminates exponent k
  if the right-hand side is not a square modulo ell.
-/
def eliminatedBy (p par k ell : Nat) : Bool :=
  !(rhsIsSquareMod p par k ell)

/--
  A list of auxiliary primes eliminates exponent k
  if at least one auxiliary prime eliminates it.
-/
def eliminatedBySome (p par k : Nat) (aux : List Nat) : Bool :=
  aux.any (fun ell => eliminatedBy p par k ell)

/--
  For a finite modulus M, a certificate is valid if every residue class
  k = 0,...,M-1 is eliminated by at least one auxiliary prime.
-/
def certValidForModulus (p par M : Nat) (aux : List Nat) : Bool :=
  (List.range M).all (fun k => eliminatedBySome p par k aux)

/--
  The finite check modulo M is justified if, for every auxiliary prime ell,
  the value p^2 has period dividing M modulo ell.

  We do not need M to be the minimal period. It is enough to verify

      (p^2)^M = 1 mod ell.

  The additional nonzero check rules out the degenerate case p^2 = 0 mod ell.
-/
def periodValidForAux (p M ell : Nat) : Bool :=
  (!(((p * p) % ell) == 0)) &&
  (powMod ((p * p) % ell) M ell == 1)

def periodsValidForAuxList (p M : Nat) (aux : List Nat) : Bool :=
  aux.all (fun ell => periodValidForAux p M ell)

/-
  Modular certificates for all singly-covered (p, parity) pairs.
-/

def cert_23_odd : Bool :=
  certValidForModulus 23 1 1 [11]

def cert_47_odd : Bool :=
  certValidForModulus 47 1 1 [23]

def cert_53_even : Bool :=
  certValidForModulus 53 0 1 [13]

def cert_109_even : Bool :=
  certValidForModulus 109 0 1 [11]

def cert_1103_odd : Bool :=
  certValidForModulus 1103 1 1 [19]

def cert_2521_even : Bool :=
  certValidForModulus 2521 0 1 [13]

def cert_5779_even : Bool :=
  certValidForModulus 5779 0 1 [17]

example : cert_23_odd = true := by native_decide
example : cert_47_odd = true := by native_decide
example : cert_53_even = true := by native_decide
example : cert_109_even = true := by native_decide
example : cert_1103_odd = true := by native_decide
example : cert_2521_even = true := by native_decide
example : cert_5779_even = true := by native_decide

def cert_11_even : Bool :=
  certValidForModulus 11 0 2 [61]

def cert_19_even : Bool :=
  certValidForModulus 19 0 2 [181]

def cert_31_even : Bool :=
  certValidForModulus 31 0 2 [37]

example : cert_11_even = true := by native_decide
example : cert_19_even = true := by native_decide
example : cert_31_even = true := by native_decide

def cert_17_even : Bool :=
  certValidForModulus 17 0 15 [7, 11, 13]

def cert_61_even : Bool :=
  certValidForModulus 61 0 360 [7, 11, 13, 17, 19]

def cert_41_even : Bool :=
  certValidForModulus 41 0 3960 [11, 13, 17, 19, 23, 29]

example : cert_17_even = true := by native_decide
example : cert_61_even = true := by native_decide
example : cert_41_even = true := by native_decide

def cert_2_even : Bool :=
  certValidForModulus 2 0 6930 [7, 11, 13, 19, 23, 29, 31]

def cert_5_even : Bool :=
  certValidForModulus 5 0 27720 [7, 11, 13, 17, 19, 23, 29, 31, 37, 41]

example : cert_2_even = true := by native_decide
example : cert_5_even = true := by native_decide

def cert_7_odd : Bool :=
  certValidForModulus 7 1 27720 [11, 13, 17, 19, 23, 29, 37, 41, 43]

def cert_2_odd : Bool :=
  certValidForModulus 2 1 318780 [7, 11, 13, 17, 19, 23, 29, 31, 37, 43, 47, 61]

def cert_3_odd : Bool :=
  certValidForModulus 3 1 637560 [7, 11, 17, 19, 23, 29, 31, 37, 41, 43, 47, 67, 71, 73]

example : cert_7_odd = true := by native_decide
example : cert_2_odd = true := by native_decide
example : cert_3_odd = true := by native_decide

/-
  Period checks for the corresponding moduli M.

  These checks verify that each chosen M is a genuine period for the modular
  tests used in the corresponding certificate.
-/

def period_23_odd : Bool :=
  periodsValidForAuxList 23 1 [11]

def period_47_odd : Bool :=
  periodsValidForAuxList 47 1 [23]

def period_53_even : Bool :=
  periodsValidForAuxList 53 1 [13]

def period_109_even : Bool :=
  periodsValidForAuxList 109 1 [11]

def period_1103_odd : Bool :=
  periodsValidForAuxList 1103 1 [19]

def period_2521_even : Bool :=
  periodsValidForAuxList 2521 1 [13]

def period_5779_even : Bool :=
  periodsValidForAuxList 5779 1 [17]

def period_11_even : Bool :=
  periodsValidForAuxList 11 2 [61]

def period_19_even : Bool :=
  periodsValidForAuxList 19 2 [181]

def period_31_even : Bool :=
  periodsValidForAuxList 31 2 [37]

def period_17_even : Bool :=
  periodsValidForAuxList 17 15 [7, 11, 13]

def period_61_even : Bool :=
  periodsValidForAuxList 61 360 [7, 11, 13, 17, 19]

def period_41_even : Bool :=
  periodsValidForAuxList 41 3960 [11, 13, 17, 19, 23, 29]

def period_2_even : Bool :=
  periodsValidForAuxList 2 6930 [7, 11, 13, 19, 23, 29, 31]

def period_5_even : Bool :=
  periodsValidForAuxList 5 27720 [7, 11, 13, 17, 19, 23, 29, 31, 37, 41]

def period_7_odd : Bool :=
  periodsValidForAuxList 7 27720 [11, 13, 17, 19, 23, 29, 37, 41, 43]

def period_2_odd : Bool :=
  periodsValidForAuxList 2 318780 [7, 11, 13, 17, 19, 23, 29, 31, 37, 43, 47, 61]

def period_3_odd : Bool :=
  periodsValidForAuxList 3 637560 [7, 11, 17, 19, 23, 29, 31, 37, 41, 43, 47, 67, 71, 73]

example : period_23_odd = true := by native_decide
example : period_47_odd = true := by native_decide
example : period_53_even = true := by native_decide
example : period_109_even = true := by native_decide
example : period_1103_odd = true := by native_decide
example : period_2521_even = true := by native_decide
example : period_5779_even = true := by native_decide
example : period_11_even = true := by native_decide
example : period_19_even = true := by native_decide
example : period_31_even = true := by native_decide
example : period_17_even = true := by native_decide
example : period_61_even = true := by native_decide
example : period_41_even = true := by native_decide
example : period_2_even = true := by native_decide
example : period_5_even = true := by native_decide
example : period_7_odd = true := by native_decide
example : period_2_odd = true := by native_decide
example : period_3_odd = true := by native_decide

/--
  All modular certificates used for the singly-covered cases.
-/
def allModularCertificatesVerified : Bool :=
  cert_23_odd &&
  cert_47_odd &&
  cert_53_even &&
  cert_109_even &&
  cert_1103_odd &&
  cert_2521_even &&
  cert_5779_even &&
  cert_11_even &&
  cert_19_even &&
  cert_31_even &&
  cert_17_even &&
  cert_61_even &&
  cert_41_even &&
  cert_2_even &&
  cert_5_even &&
  cert_7_odd &&
  cert_2_odd &&
  cert_3_odd

/--
  All period checks for the moduli M used in the certificates.

  This verifies that the finite checks over k = 0,...,M-1 really cover all
  integer exponents k.
-/
def allPeriodsVerified : Bool :=
  period_23_odd &&
  period_47_odd &&
  period_53_even &&
  period_109_even &&
  period_1103_odd &&
  period_2521_even &&
  period_5779_even &&
  period_11_even &&
  period_19_even &&
  period_31_even &&
  period_17_even &&
  period_61_even &&
  period_41_even &&
  period_2_even &&
  period_5_even &&
  period_7_odd &&
  period_2_odd &&
  period_3_odd

/--
  Complete computational verification of the modular-certificate part:
  every residue class modulo the chosen M is eliminated, and every chosen M
  is verified to be a genuine period for its auxiliary modular tests.
-/
def allCertificateDataVerified : Bool :=
  allModularCertificatesVerified && allPeriodsVerified

example : allModularCertificatesVerified = true := by native_decide
example : allPeriodsVerified = true := by native_decide
example : allCertificateDataVerified = true := by native_decide

end Nicol
