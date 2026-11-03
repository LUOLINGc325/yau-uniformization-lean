import Yau.Proofs.F05FlowScalarSmooth

/-! The paper's literal corrected boundary formula is already a smooth
global extension with the required initial equation jet. -/

open Set
open scoped ContDiff
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.Blueprint
variable {n : ℕ} {X : KahlerManifold n}

theorem F05_flow_corner_smooth (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ) {S : ℝ} (hS : 0 < S) (a δ : ℝ) (ζ : ℝ → ℝ)
    (hζ : ContDiff ℝ ∞ ζ) : SmoothSpaceTime (flowCornerBoundary X ρ a δ ζ) (Icc 0 S) := by
  have hR := F05_flow_scalar_smooth o h U P ρ hloc hS
  have hR0 : SmoothFn (fun x => scalarCurvature X.metric.form x) := by
    simpa only [hloc.1.1] using smoothFn_slice hR (show (0 : ℝ) ∈ Icc 0 S from ⟨le_rfl,hS.le⟩)
  intro x
  have hρ : ContDiffOn ℝ ∞ (fun q : ComplexVector n × ℝ => ρ (chartInv x q.1) q.2)
      (chartTarget x ×ˢ Icc 0 S) :=
    (hloc.2.2.2.1 x).mono (fun q hq => ⟨hq.1,hq.2.1⟩)
  have hRg : ContDiffOn ℝ ∞ (fun q : ComplexVector n × ℝ => scalarCurvature X.metric.form (chartInv x q.1))
      (chartTarget x ×ˢ Icc 0 S) :=
    (hR0 x).comp contDiffOn_fst (fun q hq => hq.1)
  have hTime : ContDiffOn ℝ ∞ (fun q : ComplexVector n × ℝ => q.2) (chartTarget x ×ˢ Icc 0 S) := contDiffOn_snd
  have hCut := hζ.comp_contDiffOn (hTime.div_const δ)
  unfold flowCornerBoundary cornerBoundary
  exact (hρ.add contDiffOn_const).sub (((contDiffOn_const.mul hRg).mul hTime).mul hCut)

end Yau.Proofs.F05Aux
