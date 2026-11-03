import Yau.Proofs.F03DirichletEnergyIdentity

/-! Closedness of the constructed scalar/one-form energy graph. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace

namespace Yau.Proofs.F03Aux
open Yau
open LeafProofs.L03 LeafProofs.L18Aux LeafProofs.L19Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : ComplexManifold n}

def dirichletGraphMap (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) :
    DirichletEnergy g μ hμ O →L[ℝ]
      (Lp ℝ 2 (μ.restrict O) × L2FormHilbert g (μ.restrict O) 1) :=
  (dirichletL2 g μ hμ O).prod (dirichletD g μ hμ O)

theorem dirichletGraphMap_bound (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier)
    (v : DirichletEnergy g μ hμ O) :
    ‖v‖ ≤ 2 * ‖dirichletGraphMap g μ hμ O v‖ := by
  have hJ : ‖dirichletL2 g μ hμ O v‖ ≤ ‖dirichletGraphMap g μ hμ O v‖ :=
    le_max_left _ _
  have hD : ‖dirichletD g μ hμ O v‖ ≤ ‖dirichletGraphMap g μ hμ O v‖ :=
    le_max_right _ _
  have hJsq := pow_le_pow_left₀ (norm_nonneg (dirichletL2 g μ hμ O v)) hJ 2
  have hDsq := pow_le_pow_left₀ (norm_nonneg (dirichletD g μ hμ O v)) hD 2
  have hidentity := dirichletEnergy_norm_sq g μ hμ O v
  nlinarith [norm_nonneg v, norm_nonneg (dirichletGraphMap g μ hμ O v)]

theorem dirichletGraphMap_isClosed_range (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) :
    IsClosed (Set.range (dirichletGraphMap g μ hμ O)) := by
  letI := dirichletEnergy_completeSpace g μ hμ O
  exact ((dirichletGraphMap g μ hμ O).antilipschitz_of_bound
    (K := 2) (dirichletGraphMap_bound g μ hμ O)).isClosed_range
      (dirichletGraphMap g μ hμ O).uniformContinuous

end Yau.Proofs.F03Aux
