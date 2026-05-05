import Mathlib.Tactic
import Vsemirnov.Basic

namespace Vsemirnov

structure Triple where
  p : Nat
  m : Nat
  r : Nat
deriving DecidableEq, Repr

def triples : List Triple :=
[
  ⟨3,4,3⟩,
  ⟨2,3,1⟩,
  ⟨5,5,4⟩,
  ⟨7,8,5⟩,
  ⟨17,9,2⟩,
  ⟨11,10,6⟩,
  ⟨47,16,9⟩,
  ⟨19,18,14⟩,
  ⟨61,15,12⟩,
  ⟨23,24,17⟩,
  ⟨107,36,8⟩,
  ⟨31,30,0⟩,
  ⟨1103,48,33⟩,
  ⟨181,90,80⟩,
  ⟨41,20,18⟩,
  ⟨541,90,62⟩,
  ⟨2521,60,48⟩
]

def L : Nat := 720

def computedL : Nat :=
  triples.foldl (fun acc T => Nat.lcm acc T.m) 1

example : computedL = L := by
  native_decide

def covers (T : Triple) (n : Nat) : Bool :=
  n % T.m == T.r % T.m

def coveringPrimes (n : Nat) : List Nat :=
  (triples.filter (fun T => covers T n)).map (fun T => T.p)

def classes : List Nat :=
  List.range L

def isCovered (n : Nat) : Bool :=
  !(coveringPrimes n).isEmpty

def isSinglyCovered (n : Nat) : Bool :=
  (coveringPrimes n).length == 1

def isMultiCovered (n : Nat) : Bool :=
  (coveringPrimes n).length >= 2

def singlyClasses : List Nat :=
  classes.filter isSinglyCovered

def multiClasses : List Nat :=
  classes.filter isMultiCovered

def allClassesCovered : Bool :=
  classes.all isCovered

example : classes.length = 720 := by
  native_decide

example : allClassesCovered = true := by
  native_decide

example : singlyClasses.length = 384 := by
  native_decide

example : multiClasses.length = 336 := by
  native_decide

def parity (n : Nat) : Nat :=
  n % 2

def uniqueCoveringPrime? (n : Nat) : Option Nat :=
  match coveringPrimes n with
  | [p] => some p
  | _ => none

def singlyPairs : List (Nat × Nat) :=
  singlyClasses.filterMap (fun n =>
    match uniqueCoveringPrime? n with
    | some p => some (p, parity n)
    | none => none)

def countPair (p par : Nat) : Nat :=
  (singlyPairs.filter (fun q => q = (p, par))).length

example : countPair 2 0 = 60 := by native_decide
example : countPair 2 1 = 12 := by native_decide
example : countPair 3 1 = 68 := by native_decide
example : countPair 5 0 = 28 := by native_decide
example : countPair 7 1 = 34 := by native_decide
example : countPair 11 0 = 28 := by native_decide
example : countPair 17 0 = 20 := by native_decide
example : countPair 19 0 = 20 := by native_decide
example : countPair 23 1 = 8 := by native_decide
example : countPair 31 0 = 24 := by native_decide
example : countPair 41 0 = 16 := by native_decide
example : countPair 47 1 = 9 := by native_decide
example : countPair 61 0 = 24 := by native_decide
example : countPair 107 0 = 4 := by native_decide
example : countPair 181 0 = 4 := by native_decide
example : countPair 541 0 = 4 := by native_decide
example : countPair 1103 1 = 9 := by native_decide
example : countPair 2521 0 = 12 := by native_decide

def allowedPairs : List (Nat × Nat) :=
[
  (2,0), (2,1), (3,1), (5,0), (7,1), (11,0),
  (17,0), (19,0), (23,1), (31,0), (41,0),
  (47,1), (61,0), (107,0), (181,0), (541,0),
  (1103,1), (2521,0)
]

def allSinglyPairsAllowed : Bool :=
  singlyPairs.all (fun pair => allowedPairs.contains pair)

example : allSinglyPairsAllowed = true := by native_decide

/-
  Arithmetic validation of Vsemirnov's covering triples.

  For a triple (p,m,r), the covering claim is that
      p ∣ A_n whenever n ≡ r mod m.

  We verify the finite arithmetic seeds:
      A_r     ≡ 0 mod p,
      A_{r+m} ≡ 0 mod p.

  The paper explains why this is enough: the subsequence
      B_t = A_{r+tm}
  satisfies a second-order linear recurrence, so two consecutive zero
  values modulo p force all B_t to vanish modulo p.
-/

def modIntNat (a : Int) (m : Nat) : Nat :=
  Int.toNat (a.emod (m : Int))

def stepMod (p : Nat) (s : Nat × Nat) : Nat × Nat :=
  (s.2, (s.1 + s.2) % p)

def stateMod (p : Nat) : Nat → Nat × Nat
| 0 => (modIntNat A0 p, modIntNat A1 p)
| n+1 => stepMod p (stateMod p n)

def Amod (p n : Nat) : Nat :=
  (stateMod p n).1

def tripleSeedValid (T : Triple) : Bool :=
  (Amod T.p T.r == 0) &&
  (Amod T.p (T.r + T.m) == 0)

def allTripleSeedsValid : Bool :=
  triples.all tripleSeedValid

example : allTripleSeedsValid = true := by
  native_decide

end Vsemirnov
