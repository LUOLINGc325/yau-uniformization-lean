import Yau.LeafProofs.L05PucciHarnackCube

open MeasureTheory Set
open scoped InnerProductSpace
noncomputable section
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

abbrev harnackGridIndex (n : ℕ) := ℕ × (Yau.RIdx n → ℤ) × ℤ

def harnackGridSide (h0 : ℝ) (k : ℕ) : ℝ := h0/(2 : ℝ)^k

def harnackGridCenter {n : ℕ} (h0 : ℝ) (k : ℕ) (i : Yau.RIdx n → ℤ) : Space n :=
  ∑ q, (((i q : ℝ)+1/2)*harnackGridSide h0 k) • Yau.realVec q

def harnackGridBottom (h0 : ℝ) (k : ℕ) (j : ℤ) : ℝ := (j : ℝ)*(harnackGridSide h0 k)^2

def harnackGridCube {n : ℕ} (h0 : ℝ) (k : ℕ) (i : Yau.RIdx n → ℤ) : Set (Space n) :=
  {x | ∀ q : Yau.RIdx n,
    (i q : ℝ)*harnackGridSide h0 k ≤ inner ℝ x (Yau.realVec q) ∧
      inner ℝ x (Yau.realVec q) < ((i q : ℝ)+1)*harnackGridSide h0 k}

def harnackGridBox {n : ℕ} (h0 : ℝ) (k : ℕ) (i : Yau.RIdx n → ℤ) (j : ℤ) : Set (Point n) :=
  harnackGridCube h0 k i ×ˢ Ioc (harnackGridBottom h0 k j)
    (harnackGridBottom h0 k j+(harnackGridSide h0 k)^2)

def harnackGridNodeBox {n : ℕ} (h0 : ℝ) (Q : harnackGridIndex n) : Set (Point n) :=
  harnackGridBox h0 Q.1 Q.2.1 Q.2.2

def harnackGridParent {n : ℕ} (Q : harnackGridIndex n) : harnackGridIndex n :=
  (Q.1-1,(fun q => Q.2.1 q/2),Q.2.2/4)

def harnackGridAncestor {n : ℕ} (k : ℕ) (Q : harnackGridIndex n) : harnackGridIndex n :=
  (k,(fun q => Q.2.1 q/(2 : ℤ)^(Q.1-k)),Q.2.2/(4 : ℤ)^(Q.1-k))

end Yau.LeafProofs.L05Aux
