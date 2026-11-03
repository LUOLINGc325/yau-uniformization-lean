import Yau.Proofs.F01ShiftedBackgroundJets

/-! The actual affine background is jointly smooth at every clock,
including the terminal clock. No clamping or time extension is used. -/
noncomputable section
open Set Metric
open scoped ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

theorem shiftedComplexBackground_joint_smooth (A : BoundedChartFamily g)
    {ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ ≤ A.radius) (τ : ℝ) (a : M.Carrier) :
    ContDiffOn ℝ ∞ (shiftedComplexBackground A a ρ τ)
      (ball 0 1 ×ˢ (univ : Set ℝ)) := by
  have hd : ContDiffOn ℝ ∞ (fun p : Point n => ρ • p.1)
      (ball 0 1 ×ˢ (univ : Set ℝ)) := by fun_prop
  have hm := (background_matrix_frobenius_smooth A a).comp hd
    (fun p hp => spatialDilation_mem_ball hρ hρr hp.1)
  have hr := (backgroundRicci_frobenius_smooth A a).comp hd
    (fun p hp => spatialDilation_mem_ball hρ hρr hp.1)
  have hc : ContDiffOn ℝ ∞ (fun p : Point n => τ + ρ ^ 2 * p.2)
      (ball 0 1 ×ˢ (univ : Set ℝ)) := by fun_prop
  have hProd : ContDiffOn ℝ ∞ (fun p : Point n =>
      (τ + ρ ^ 2 * p.2) • backgroundRicci (pullbackMatrix g (A.chart a)) (ρ • p.1))
      (ball 0 1 ×ˢ (univ : Set ℝ)) := hc.smul hr
  have hh : ContDiffOn ℝ ∞ (fun p : Point n => pullbackMatrix g (A.chart a) (ρ • p.1) -
      (τ + ρ ^ 2 * p.2) • backgroundRicci (pullbackMatrix g (A.chart a)) (ρ • p.1))
      (ball 0 1 ×ˢ (univ : Set ℝ)) := hm.sub hProd
  apply hh.congr
  intro p hp
  simp only [shiftedComplexBackground, chartAffineBackground, affineParabolicPoint,
    add_zero, Complex.coe_smul]

end Yau.NodeProofs.F01Aux
