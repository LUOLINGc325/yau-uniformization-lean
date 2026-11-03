import Yau.Proofs.F01MetricRayleighContinuity
import Yau.Proofs.F01DiagonalRayleigh

/-! The actual relative maximum is positive and equals one for the same
metric. Its logarithm is continuous on the original full time set. -/
noncomputable section
open Set
open scoped Manifold Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

theorem largestMatrixRayleigh_pos {G H : Matrix (Fin n) (Fin n) ℂ}
    (hG : G.PosDef) (hH : H.PosDef) (j : Fin n) :
    0 < largestMatrixRayleigh G H := by
  have hv : (Pi.single j (1 : ℂ) : Fin n → ℂ) ≠ 0 := by
    intro h
    have hh := congrFun h j
    simpa using hh
  have hq : 0 < matrixRayleigh G H (Pi.single j 1) :=
    div_pos (matrixQuadraticValue_pos hH hv) (matrixQuadraticValue_pos hG hv)
  exact hq.trans_le (matrixRayleigh_le_largest hG hH _)

theorem largestMatrixRayleigh_self {G : Matrix (Fin n) (Fin n) ℂ}
    (hG : G.PosDef) (j : Fin n) : largestMatrixRayleigh G G = 1 := by
  apply le_antisymm
  · apply largestMatrixRayleigh_le_of_order hG (by norm_num)
    rw [Complex.ofReal_one, one_smul, sub_self]
    exact Matrix.PosSemidef.zero
  · have hv : (Pi.single j (1 : ℂ) : Fin n → ℂ) ≠ 0 := by
      intro h
      have hh := congrFun h j
      simpa using hh
    have hr := matrixRayleigh_le_largest hG hG (Pi.single j 1)
    simpa only [matrixRayleigh, div_self (matrixQuadraticValue_pos hG hv).ne'] using hr

theorem metricLargestRayleigh_pos (g k : HermitianField M) (p : M.Carrier) :
    0 < metricLargestRayleigh g k p := by
  let j : Fin n := ⟨0, Yau.LeafProofs.L12Aux.manifold_dimension_pos M⟩
  exact largestMatrixRayleigh_pos
    (Yau.LeafProofs.L12Aux.hMat_posDef g p (chartPt p p) (mem_extChartAt_target p))
    (Yau.LeafProofs.L12Aux.hMat_posDef k p (chartPt p p) (mem_extChartAt_target p)) j

theorem metricLargestRayleigh_self (g : HermitianField M) (p : M.Carrier) :
    metricLargestRayleigh g g p = 1 := by
  let j : Fin n := ⟨0, Yau.LeafProofs.L12Aux.manifold_dimension_pos M⟩
  exact largestMatrixRayleigh_self
    (Yau.LeafProofs.L12Aux.hMat_posDef g p (chartPt p p) (mem_extChartAt_target p)) j

theorem metricFamily_logLargestRayleigh_continuousOn
    (g k : ℝ → HermitianField M) {I : Set ℝ}
    (hg : MetricFamilySmooth g I) (hk : MetricFamilySmooth k I) :
    ContinuousOn (fun p : M.Carrier × ℝ =>
      Real.log (metricLargestRayleigh (g p.2) (k p.2) p.1)) (univ ×ˢ I) :=
  (metricFamily_largestRayleigh_continuousOn g k hg hk).log
    (fun p _ => (metricLargestRayleigh_pos (g p.2) (k p.2) p.1).ne')

end Yau.NodeProofs.F01Aux
