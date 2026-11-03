import Yau.LeafProofs.L16TraceTimeJet
import Yau.LeafProofs.L16HalfSpaceHolderExtension

open MeasureTheory Filter Set
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates
local instance traceSpatialLayer_dualGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance traceSpatialLayer_dualSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance
local instance traceSpatialLayer_bilinearGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance
local instance traceSpatialLayer_bilinearSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance

/-- The actual trace-source layer in the original Euclidean spatial variables.
    It is used on the nonnegative half space before second-order extension. -/
def boundaryTraceLayer {n : ℕ} (e : Space n) (B : Point n → ℝ) (p : Point n) : ℝ :=
  normalTraceLayer B (halfSpaceBoundaryProjection e p.1) p.2 (inner ℝ e p.1)

def traceSpatialGradientKernel {n : ℕ} (e : Space n) (B : Point n → ℝ)
    (t : ℝ) (x : Space n) (r : ℝ) : Space n →L[ℝ] ℝ :=
  normalHeatProfile r (inner ℝ e x) •
    (fderiv ℝ (heatAverage r (fun y => B (y,t-r))) (halfSpaceBoundaryProjection e x)).comp
      (halfSpaceBoundaryProjection e) +
  (2*normalGaussianKernel r (inner ℝ e x)*
    heatAverage r (fun y => B (y,t-r)) (halfSpaceBoundaryProjection e x)) • innerSL ℝ e

theorem halfSpaceBoundaryProjection_norm_le {n : ℕ} (e : Space n) :
    ‖halfSpaceBoundaryProjection e‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  simpa only [map_zero,sub_zero,one_mul] using halfSpaceBoundaryProjection_nonexpansive e x 0

/-- The genuine first spatial kernel has an integrable uniform age bound on
    the closed half space. -/
theorem traceSpatialGradientKernel_bound {n : ℕ} :
    ∃ C : ℝ, 0 < C ∧ ∀ (e : Space n), ‖e‖ = 1 → ∀ (B : Point n → ℝ) (F : ℝ),
      Continuous B → (∀ p, |B p| ≤ F) → ∀ r : ℝ, 0 < r → ∀ t : ℝ,
      ∀ x : Space n, 0 ≤ inner ℝ e x → ‖traceSpatialGradientKernel e B t x r‖ ≤ C*F*r^(-(1/2 : ℝ)) := by
  obtain ⟨C,hC,hGrad⟩ := heatAverage_fderiv_bound_of_bounded (n := n)
  let Cg : ℝ := 2*(Real.sqrt (4*Real.pi))⁻¹
  have hCg : 0 < Cg := by dsimp only [Cg]; positivity
  refine ⟨C+Cg,by positivity,?_⟩
  intro e he B F hB hF r hr t x hx
  have hF0 : 0 ≤ F := (abs_nonneg (B (0,0))).trans (hF (0,0))
  obtain ⟨hh0,hh1⟩ := normalHeatProfile_bounds hr hx
  have hN : ‖innerSL ℝ e‖ = 1 := by rw [innerSL_apply_norm,he]
  have hT : ‖normalHeatProfile r (inner ℝ e x) •
      (fderiv ℝ (heatAverage r (fun y => B (y,t-r))) (halfSpaceBoundaryProjection e x)).comp
        (halfSpaceBoundaryProjection e)‖ ≤ C*F*r^(-(1/2 : ℝ)) := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hh0]
    apply (mul_le_of_le_one_left (norm_nonneg _) hh1).trans
    apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
    apply (mul_le_of_le_one_right (norm_nonneg _) (halfSpaceBoundaryProjection_norm_le e)).trans
    exact hGrad r hr (fun y => B (y,t-r)) F
      (hB.comp (continuous_id.prodMk continuous_const)) (fun y => hF (y,t-r)) _
  have hP : 0 ≤ 2*normalGaussianKernel r (inner ℝ e x) :=
    mul_nonneg (by norm_num) (normalGaussianKernel_pos hr _).le
  have hK : 2*normalGaussianKernel r (inner ℝ e x) ≤ Cg*r^(-(1/2 : ℝ)) := by
    simpa only [Cg,mul_assoc] using
      mul_le_mul_of_nonneg_left (normalGaussianKernel_le_rpow hr (inner ℝ e x)) (by norm_num : (0 : ℝ) ≤ 2)
  have hNormal : ‖(2*normalGaussianKernel r (inner ℝ e x)*
      heatAverage r (fun y => B (y,t-r)) (halfSpaceBoundaryProjection e x)) • innerSL ℝ e‖ ≤
      Cg*F*r^(-(1/2 : ℝ)) := by
    rw [norm_smul,hN,mul_one,Real.norm_eq_abs,abs_mul,abs_of_nonneg hP]
    have hA := heatAverage_bound hr (hB.comp (continuous_id.prodMk continuous_const))
      (fun y => hF (y,t-r)) (halfSpaceBoundaryProjection e x)
    change |heatAverage r (fun y => B (y,t-r)) (halfSpaceBoundaryProjection e x)| ≤ F at hA
    have h := mul_le_mul hK hA (abs_nonneg _) (by positivity)
    convert h using 1 <;> ring
  exact ((norm_add_le _ _).trans (add_le_add hT hNormal)).trans_eq (by ring)

end Yau.LeafProofs.L16Aux
