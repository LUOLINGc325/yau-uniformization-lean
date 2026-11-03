import Yau.LeafProofs.L17BootstrapMetricAction
import Yau.LeafProofs.L17NormalizedPotential

noncomputable section
open Set
open scoped Topology ContDiff Matrix.Norms.Frobenius
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BootstrapMetricAux
open L17Aux L17HolderAux L17SchauderAux L17LocalHolderAlgebraAux
open L17LocalHolderBanachAlgebraAux
local instance metricCoefficientMatrixTopology (n : ℕ) :
    TopologicalSpace (Matrix (Fin n) (Fin n) ℂ) := leviMatrixTopology n
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable (P : UniformChartPartition g) (T gamma : ℝ) (hT : 0<T)

/-- The spatial part uses the actual first and second derivatives stored in X. -/
def metricPotentialCLM
    (c1 : LocalHolderBanach (D1 n →L[ℝ] Matrix (Fin n) (Fin n) ℂ) P T gamma)
    (c2 : LocalHolderBanach (D2 n →L[ℝ] Matrix (Fin n) (Fin n) ℂ) P T gamma) :
    SchauderSpace P T gamma hT →L[ℝ]
      LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T gamma :=
  (coefficientActionCLM P T gamma c1).comp (gradientHolderCLM P T gamma hT) +
    (coefficientActionCLM P T gamma c2).comp (hessianHolderCLM P T gamma hT)

theorem metricPotentialCLM_value
    (c1 : LocalHolderBanach (D1 n →L[ℝ] Matrix (Fin n) (Fin n) ℂ) P T gamma)
    (c2 : LocalHolderBanach (D2 n →L[ℝ] Matrix (Fin n) (Fin n) ℂ) P T gamma)
    (u : SchauderSpace P T gamma hT) (q : LocalCylinder P T) :
    metricPotentialCLM P T gamma hT c1 c2 u q=
      c1 q (gradientFun u q)+c2 q (hessianFun u q) := rfl

/-- At the unshifted coefficient the real operator is exactly the original Levi map. -/
theorem metricPotentialCLM_unshifted :
    metricPotentialCLM P T gamma hT 0
      (const (D2 n →L[ℝ] Matrix (Fin n) (Fin n) ℂ) P T gamma (leviHessianCLM n)) =
      potentialLeviBanachCLM P T gamma hT := by
  apply ContinuousLinearMap.ext
  intro u
  apply L17LocalHolderBanachAlgebraAux.ext
  intro q
  change (0 : D1 n →L[ℝ] Matrix (Fin n) (Fin n) ℂ) (gradientFun u q) +
    leviHessianCLM n (hessianFun u q) = _
  simp only [_root_.zero_apply,zero_add]
  rfl

def metricFromCoefficients
    (c0 : LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T gamma)
    (c1 : LocalHolderBanach (D1 n →L[ℝ] Matrix (Fin n) (Fin n) ℂ) P T gamma)
    (c2 : LocalHolderBanach (D2 n →L[ℝ] Matrix (Fin n) (Fin n) ℂ) P T gamma)
    (u : SchauderSpace P T gamma hT) :
    LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T gamma :=
  c0+metricPotentialCLM P T gamma hT c1 c2 u

theorem metricFromCoefficients_value
    (c0 : LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T gamma)
    (c1 : LocalHolderBanach (D1 n →L[ℝ] Matrix (Fin n) (Fin n) ℂ) P T gamma)
    (c2 : LocalHolderBanach (D2 n →L[ℝ] Matrix (Fin n) (Fin n) ℂ) P T gamma)
    (u : SchauderSpace P T gamma hT) (q : LocalCylinder P T) :
    metricFromCoefficients P T gamma hT c0 c1 c2 u q=
      c0 q+c1 q (gradientFun u q)+c2 q (hessianFun u q) := by
  change c0 q+(c1 q (gradientFun u q)+c2 q (hessianFun u q))=_
  exact (add_assoc _ _ _).symm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E}

theorem metricFromCoefficients_contDiffOn
    {c0 : E → LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T gamma}
    {c1 : E → LocalHolderBanach (D1 n →L[ℝ] Matrix (Fin n) (Fin n) ℂ) P T gamma}
    {c2 : E → LocalHolderBanach (D2 n →L[ℝ] Matrix (Fin n) (Fin n) ℂ) P T gamma}
    {v : E → SchauderSpace P T gamma hT}
    (hc0 : ContDiffOn ℝ ∞ c0 s) (hc1 : ContDiffOn ℝ ∞ c1 s)
    (hc2 : ContDiffOn ℝ ∞ c2 s) (hv : ContDiffOn ℝ ∞ v s) :
    ContDiffOn ℝ ∞ (fun a => metricFromCoefficients P T gamma hT
      (c0 a) (c1 a) (c2 a) (v a)) s := by
  have h1 := ((coefficientActionCLM P T gamma).contDiff.comp_contDiffOn hc1).clm_apply
    ((gradientHolderCLM P T gamma hT).contDiff.comp_contDiffOn hv)
  have h2 := ((coefficientActionCLM P T gamma).contDiff.comp_contDiffOn hc2).clm_apply
    ((hessianHolderCLM P T gamma hT).contDiff.comp_contDiffOn hv)
  exact hc0.add (h1.add h2)

end Yau.LeafProofs.L17BootstrapMetricAux
