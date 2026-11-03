import Yau.Geometry.Flat
import Yau.Blueprint.Types

/-! Planning targets. These definitions state mathematical obligations; they are
not proofs. An omitted ID is a blocked obligation in the source ledger, never a
replacement by an elementary shell. -/
noncomputable section
namespace Yau.BlueprintContracts
open Yau Yau.Blueprint
open scoped Manifold Topology ContDiff Matrix ComplexOrder
set_option autoImplicit false
variable {n : ℕ} {M : ComplexManifold n}

def G0_contract (n : ℕ) (hn : 1 ≤ n) : Prop := Nonempty (ComplexManifold n)
def G1_contract (h : HermitianField M) : Prop := ∀ x u, 0 ≤ hermitianNormSq (h x) u
def G2_contract (g : SmoothMetric M) : Prop :=
  (∀ x y, 0 ≤ inducedDistance g.form x y) ∧
  (∀ x y, inducedDistance g.form x y = 0 ↔ x = y) ∧
  (∀ x y, inducedDistance g.form x y = inducedDistance g.form y x) ∧
  (∀ x y z, inducedDistance g.form x z ≤ inducedDistance g.form x y + inducedDistance g.form y z) ∧
  IsInducedDistanceTopology (inducedDistance g.form)
def G3_contract (g : SmoothMetric M) : Prop :=
  KahlerCoordinateCondition g.form ∧ HermitianFieldChartTransition g.form
def G4_contract : Prop := G01
def G5_contract (n : ℕ) (hn : 1 ≤ n) : Prop :=
  ∀ x i j k l, flatCurvatureComponent n x i j k l = 0
def G6_contract (n : ℕ) (hn : 1 ≤ n) : Prop := ¬ PaperPositiveBisectional (flatHermitianField hn)
def G01_contract : Prop := G01
def G02_contract : Prop := G02
def G03_contract : Prop := G03
def G04_contract : Prop := G04

def P01_contract : Prop := P01
def P02_contract : Prop := P02
def P03_contract : Prop := P03
def P04_contract : Prop := P04
def P05_contract : Prop := P05
/-- Bounded closed-form and Lipschitz/current heat clauses; all are unproved targets. -/
def P06_contract : Prop := P06
def P07_contract : Prop := P07
def P08_contract : Prop := P08

def F01_contract : Prop := F01
def F02_contract : Prop := F02
def F03_contract : Prop := F03
def F04_contract : Prop := F04
def F05_contract : Prop := F05

def D01_contract : Prop := D01
def D02_contract : Prop := D02
/-- Original arbitrary Hermitian holomorphic bundle, without a global frame. -/
def B01_contract : Prop := B01
def D03_contract : Prop := D03
def D04_contract : Prop := D04
def D05_contract : Prop := D05
def D06_contract : Prop := D06

def V01_contract : Prop := V01
def V02_contract : Prop := V02
def V03_contract : Prop := V03
def V04_contract : Prop := V04
def V05_contract : Prop := V05

def E01_contract : Prop := E01
def E02_contract : Prop := E02
def E03_contract : Prop := E03

def C01_contract : Prop := C01
def C02_contract : Prop := C02
def C03_contract : Prop := C03
def C04_contract : Prop := C04
def C05_contract : Prop := C05

/-- Reviewed C05 derivation entry: produce its exact same-manifold inlet
and the unchanged universal C05 conclusion from the four registered parents.
This definition is a target, not a proof or an extra assumption. -/
def C05_step_contract : Prop :=
  F01_contract → F04_contract → C01_contract → C04_contract →
    C05InputProducer ∧ C05_contract
def C06_contract : Prop := C06
def C07_contract : Prop := C07

def Y01_contract : Prop := Y01
def Y02_contract : Prop := Y02
def Y03_contract : Prop := Y03
def Y05_contract : Prop := Y05
def Y06_contract : Prop := Y06
def Y07_contract : Prop := Y07
def Y04_contract : Prop := Y04

def U01_contract : Prop := U01
def U02_contract : Prop := U02
/-- Universal producer goal; the parameterized API is `Blueprint.U03`.
The estimates and degrees still concern precisely the same map, G and s. -/
def U03_contract : Prop := U03Goal
/-- Universal packaging goal; `Blueprint.U04` retains the parameterized API. -/
def U04_contract : Prop := U04Goal

/-- Existence on the original X, with the SAME global/U03Output witness. -/
def U05_contract : Prop := U05

def I01_contract : Prop :=
  ∀ (n : ℕ) (M : ComplexManifold n) (global : Uniformization.OpenCoordinateData n M)
    (out : U03Output global), U04 global out → BiholomorphicToComplexEuclidean M

def END_contract : Prop := END

end Yau.BlueprintContracts
