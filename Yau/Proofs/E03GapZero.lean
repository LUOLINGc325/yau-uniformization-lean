import Yau.Proofs.E03GapViscosity
import Yau.Proofs.E03GapUpperSemicontinuity
import Yau.Proofs.E03GapCompactBound

/-! Apply the supplied original scalar comparison on a strictly shorter horizon. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter Set

namespace Yau.NodeProofs.E03Aux
open Yau Yau.Blueprint
variable {n : ℕ} {X : KahlerManifold n}

theorem scalarGap_eq_zero (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ) (hopt : OptimizerContacts X h ρ)
    (hcomp : EllipsoidComparison X h) (hscalar : ScalarComparison X h ρ)
    (T : ℝ) (hT : 0 < T) (x : Pt X) (t : ℝ) (ht : 0 < t) (htT : t < T) :
    scalarGap X h T x t = 0 := by
  obtain ⟨S, hS, htS, hST⟩ := exists_shorter_comparison_horizon ht htT
  exact (hscalar S hS).2.2.2 (scalarGap X h T)
    (scalarGap_upperSemicontinuousOn o h U P ρ hloc hopt T hT S hS hST)
    (scalarGap_compact_bound o h U P ρ hloc hopt T hT S hST)
    (scalarGap_bounds o h U P ρ hloc hopt T hT S hST)
    (scalarGap_nonlinearViscositySub o h U P ρ hloc hopt hcomp T hT S hST)
    x t ⟨ht.le, htS⟩

theorem volumeGap_eq_zero (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ) (hopt : OptimizerContacts X h ρ)
    (hcomp : EllipsoidComparison X h) (hscalar : ScalarComparison X h ρ)
    (T : ℝ) (hT : 0 < T) (c : Pt X) (z : ComplexVector n) (t : ℝ)
    (hz : z ∈ chartTarget c) (ht : t ∈ Ioo 0 T) : volumeGap X h T c z t = 0 := by
  rw [← scalarGap_fixed_chart h ρ hopt T hT c z t hz ht]
  exact scalarGap_eq_zero o h U P ρ hloc hopt hcomp hscalar T hT (chartInv c z) t ht.1 ht.2

end Yau.NodeProofs.E03Aux
