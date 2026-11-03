import Yau.LeafProofs.L17LocalizedSchauderActualGraph
import Yau.LeafProofs.L17LocalizedSchauderScalarHolders
import Yau.LeafProofs.L17LocalizedSchauderDerivativeHolders
import Yau.LeafProofs.L17LocalizedSchauderPhysicalDerivatives

open Set Metric Filter
open scoped Topology
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17LocalizedSchauderAux
open Yau.LeafProofs.L17Aux Yau.LeafProofs.L17HolderAux Yau.LeafProofs.L17SchauderAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable (P : UniformChartPartition g) (T gamma : ℝ) (hT : 0 < T)
    (v : P.centers → ComplexVector n × Time T → ℝ)
    (D : P.centers → ComplexVector n × Time T → D1 n)
    (H : P.centers → ComplexVector n × Time T → D2 n)
    (b : P.centers → ComplexVector n × Time T → ℝ)
    (hTrue : LocalTrueJets P T hT.le v D H b) {F B : ℝ} (hF : 0 ≤ F) (hB : 0 ≤ B)
    (hBounds : LocalScaledJetBounds P T gamma F v D H b)
    (hLocal : LocalizedFourJetBounds P T gamma B v b) (hγ : 0 < gamma)

def assembledAmbient : SchauderAmbient P T gamma :=
  ((rawValueHolder P T hT.le v D H b hTrue hF hB hBounds hLocal,
    rawGradientHolder P T hT.le v D H b hTrue hB hLocal hγ),
   (rawHessianHolder P T hT.le v D H b hTrue hB hLocal hγ,
    actualTimeHolder P T hT.le v D H b hTrue hF hB hBounds hLocal))

include hTrue hF hB hBounds hLocal hγ

theorem assembledAmbient_value (q : Cylinder M T) :
    ambientValueCLM P T gamma (assembledAmbient P T gamma hT v D H b hTrue hF hB hBounds hLocal hγ) q =
      globalSum P T v q := by
  change P.radius^2 • holderFun (rawValueHolder P T hT.le v D H b hTrue hF hB hBounds hLocal) q = _
  rw [rawValueHolder_value,smul_smul,mul_inv_cancel₀ (pow_ne_zero _ P.radius_pos.ne'),one_smul]

theorem assembledAmbient_gradient (q : LocalCylinder P T) :
    ambientGradientCLM P T gamma (assembledAmbient P T gamma hT v D H b hTrue hF hB hBounds hLocal hγ) q =
      P.radius • rawGradientField P T v q := rfl

theorem assembledAmbient_hessian (q : LocalCylinder P T) :
    ambientHessianCLM P T gamma (assembledAmbient P T gamma hT v D H b hTrue hF hB hBounds hLocal hγ) q =
      rawHessianField P T v q := rfl

theorem assembledAmbient_time (q : Cylinder M T) :
    ambientTimeCLM P T gamma (assembledAmbient P T gamma hT v D H b hTrue hF hB hBounds hLocal hγ) q =
      globalSum P T b q := rfl

theorem assembledAmbient_mem_schauderSpace :
    assembledAmbient P T gamma hT v D H b hTrue hF hB hBounds hLocal hγ ∈ SchauderSpace P T gamma hT := by
  apply ambient_mem_schauderSpace_of_actual_derivatives P T gamma hT
  · intro p t z hz
    simpa only [assembledAmbient_value,assembledAmbient_gradient,rawGradientField] using
      globalSum_chart_hasFDerivAt P T hT.le v D H b hTrue p t hz
  · intro p t z hz
    rw [assembledAmbient_hessian]
    apply (globalSum_chart_gradient_hasFDerivAt P T hT.le v D H b hTrue p t hz).congr_of_eventuallyEq
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw
    simp only [ambientChartGradient,dite_eq_left hw,assembledAmbient_gradient,rawGradientField]
  · intro x t
    simpa only [assembledAmbient_value,assembledAmbient_time,closedTimePath] using
      globalSum_hasDerivWithinAt P T hT.le v b hTrue.2.2.1 x t
  · intro x
    simpa only [assembledAmbient_value] using globalSum_initial P T hT.le v hTrue.2.2.2 x

def assembledSchauder : SchauderSpace P T gamma hT :=
  ⟨assembledAmbient P T gamma hT v D H b hTrue hF hB hBounds hLocal hγ,
    assembledAmbient_mem_schauderSpace P T gamma hT v D H b hTrue hF hB hBounds hLocal hγ⟩

theorem assembledSchauder_value :
    schauderFun (assembledSchauder P T gamma hT v D H b hTrue hF hB hBounds hLocal hγ) = globalSum P T v := by
  funext q
  exact assembledAmbient_value P T gamma hT v D H b hTrue hF hB hBounds hLocal hγ q

theorem assembledSchauder_norm_le :
    ‖assembledSchauder P T gamma hT v D H b hTrue hF hB hBounds hLocal hγ‖ ≤
      max ((P.overlapBudget : ℝ)*F) ((2*(P.overlapBudget : ℝ))*B) := by
  change max (max ‖rawValueHolder P T hT.le v D H b hTrue hF hB hBounds hLocal‖
    ‖rawGradientHolder P T hT.le v D H b hTrue hB hLocal hγ‖)
    (max ‖rawHessianHolder P T hT.le v D H b hTrue hB hLocal hγ‖
      ‖actualTimeHolder P T hT.le v D H b hTrue hF hB hBounds hLocal‖) ≤ _
  apply max_le (max_le _ _) (max_le _ _)
  · exact rawValueHolder_norm_le P T hT.le v D H b hTrue hF hB hBounds hLocal
  · exact (rawGradientHolder_norm_le P T hT.le v D H b hTrue hB hLocal hγ).trans (le_max_right _ _)
  · exact (rawHessianHolder_norm_le P T hT.le v D H b hTrue hB hLocal hγ).trans (le_max_right _ _)
  · exact actualTimeHolder_norm_le P T hT.le v D H b hTrue hF hB hBounds hLocal

end Yau.LeafProofs.L17LocalizedSchauderAux
