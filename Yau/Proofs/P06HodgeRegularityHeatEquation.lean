import Yau.Proofs.P06HodgeRegularityTimeRealization
import Yau.Proofs.P06HodgeRegularityComputedGraph

/-! The original strong graph law gives the original calculated heat PDE
for the actual jointly smooth realization, at every positive time and chart. -/
noncomputable section
open MeasureTheory Filter Module
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux
open Yau Yau.LeafProofs Yau.LeafProofs.L03

variable {n k : ℕ} {M : ComplexManifold n}

theorem hodgeStrongPath_smooth_realization_heatEquation
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (h : ℝ → L2FormHilbert g μ k)
    (hheat : ∀ t, 0 < t → ∃ w, HasDerivAt h w t ∧
      (h t,(-2 : ℝ) • w) ∈ (hodgeCoreOperator g μ hμ k).closure.graph)
    (U : ℝ → RealForm M k) (hU : SmoothFormTime U (Set.Ioi 0))
    (hUs : ∀ t, 0 < t → ∃ hUs : L2RealForm g.form μ (U t), realizeActualForm g μ (U t) hUs = h t) :
    Blueprint.FormHeatEquation g.form U := by
  intro x z hz t ht I
  obtain ⟨w,hw,hgraph⟩ := hheat t ht
  obtain ⟨hUt,hreal⟩ := hUs t ht
  obtain ⟨hD,hDr⟩ := regularityTimeDerivativeForm_realizes g μ h U hU hUs ht hw
  let D := regularityTimeDerivativeForm U t
  have hW : L2RealForm g.form μ ((-2 : ℝ) • D) := l2RealForm_smul g μ (-2) D hD
  have hWr : realizeActualForm g μ ((-2 : ℝ) • D) hW = (-2 : ℝ) • w := by
    change realizeL2Form g μ ((-2 : ℝ) • L2FormSpace.ofSection D hD) = _
    rw [regularityRealizeL2Form_smul]
    exact congrArg (fun v => (-2 : ℝ) • v) hDr
  have hG : (realizeActualForm g μ (U t) hUt,realizeActualForm g μ ((-2 : ℝ) • D) hW) ∈
      (hodgeCoreOperator g μ hμ k).closure.graph := by
    rw [hreal,hWr]
    exact hgraph
  have hrep := hodgeClosureGraph_smooth_represents g μ hμ (U t) ((-2 : ℝ) • D)
    (regularitySmoothFormTime_slice U hU ht)
    (smoothRealForm_smul (-2) D (regularityTimeDerivativeForm_smooth U hU ht)) hUt hW hG
  have hcalc := hrep x z hz I
  simp only [formComponents_smul,Pi.smul_apply,smul_eq_mul] at hcalc
  have hgenerator : hodgeGeneratorComponents g.form x (formComponents (U t) x) z I =
      formComponents (regularityTimeDerivativeForm U t) x z I := by
    unfold hodgeGeneratorComponents
    dsimp only [D] at hcalc
    linarith
  rw [hgenerator]
  exact regularityTimeDerivativeForm_hasDerivAt U hU ht x hz I

/-- The frozen original strong-path geometric regularity exit. -/
theorem hodgeStrongPath_geometric_regularity
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (h : ℝ → L2FormHilbert g μ k)
    (hheat : ∀ t, 0 < t → ∃ w, HasDerivAt h w t ∧
      (h t,(-2 : ℝ) • w) ∈ (hodgeCoreOperator g μ hμ k).closure.graph) :
    ∃ U : ℝ → RealForm M k, SmoothFormTime U (Set.Ioi 0) ∧ Blueprint.FormHeatEquation g.form U ∧
      ∀ t, 0 < t → ∃ hUt : L2RealForm g.form μ (U t), realizeActualForm g μ (U t) hUt = h t := by
  obtain ⟨U,hU,hUs⟩ := hodgeStrongPath_exists_joint_smooth_realization g μ hμ h hheat
  exact ⟨U,hU,hodgeStrongPath_smooth_realization_heatEquation g μ hμ h hheat U hU hUs,hUs⟩

end Yau.NodeProofs.P06Aux
