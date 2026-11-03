import Yau.Proofs.C05GradientFlowDefinitions
import Yau.LeafProofs.L23FieldMetric

/-! The computed gradient is smooth in each fixed real chart and is the metric dual of df. -/
noncomputable section
open Filter
open scoped Topology Manifold ContDiff Matrix
namespace Yau.Proofs.C05GradientFlowAux
open Yau Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

theorem realCoord_realGradInChart (k : HermitianField M) (f : M.Carrier → ℝ)
    (c : M.Carrier) (z : ComplexVector n) (a : RIdx n) :
    realCoord (realGradInChart k f c z) a = realGradComponent k f c z a := by
  rcases a with ⟨i, j⟩
  fin_cases j <;> simp [realGradInChart, realCoord]

theorem realGradInChart_eq_sum (k : HermitianField M) (f : M.Carrier → ℝ)
    (c : M.Carrier) (z : ComplexVector n) :
    realGradInChart k f c z = ∑ a : RIdx n, realGradComponent k f c z a • realVec a := by
  apply realCoord_injective n
  funext a
  rw [realCoord_realGradInChart, realCoord_sum_realVec]

theorem realGradComponent_contDiffOn (g : SmoothMetric M) (f : M.Carrier → ℝ)
    (hf : SmoothFn f) (c : M.Carrier) (a : RIdx n) :
    ContDiffOn ℝ ∞ (fun z => realGradComponent g.form f c z a) (chartTarget c) := by
  apply ContDiffOn.sum
  intro b _
  exact (realMetricFn_inverse_contDiffOn g c a b).mul
    (rDeriv_contDiffOn (isOpen_extChartAt_target (I := ComplexModel n) c) (hf c) b)

theorem realGradInChart_contDiffOn (g : SmoothMetric M) (f : M.Carrier → ℝ)
    (hf : SmoothFn f) (c : M.Carrier) :
    ContDiffOn ℝ ∞ (realGradInChart g.form f c) (chartTarget c) := by
  have heq : realGradInChart g.form f c =
      fun z => ∑ a : RIdx n, realGradComponent g.form f c z a • realVec a :=
    funext (realGradInChart_eq_sum g.form f c)
  rw [heq]
  exact ContDiffOn.sum fun a _ => (realGradComponent_contDiffOn g f hf c a).smul contDiffOn_const

theorem fderiv_real_basis_expansion (u : ComplexVector n → ℝ) (z v : ComplexVector n) :
    fderiv ℝ u z v = ∑ a : RIdx n, realCoord v a * rDeriv u z a := by
  conv_lhs => rw [← sum_realCoord_realVec v]
  simp only [map_sum, map_smul, smul_eq_mul, rDeriv]

theorem realGradInChart_dual (k : HermitianField M) (f : M.Carrier → ℝ)
    (c : M.Carrier) (z : ComplexVector n) (hz : z ∈ chartTarget c) (v : ComplexVector n) :
    realMetricInChart k c z (realGradInChart k f c z) v = fderiv ℝ (inChart c f) z v := by
  let G := realMetricFn k c z
  let D : RIdx n → ℝ := fun a => rDeriv (inChart c f) z a
  let W : RIdx n → ℝ := realGradComponent k f c z
  have hGW : G *ᵥ W = D := by
    change G *ᵥ (G⁻¹ *ᵥ D) = D
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv G
      (isUnit_iff_ne_zero.mpr (realMetricFn_posDef k c z hz).det_pos.ne'), Matrix.one_mulVec]
  have hentry (a b : RIdx n) : realMetricInChart k c z (realVec a) (realVec b) = G a b :=
    underlyingRealRiemannianMetric_frame k c z hz a b
  rw [realBilin_eq_sum]
  simp_rw [realCoord_realGradInChart, hentry]
  calc
    _ = ∑ b : RIdx n, realCoord v b * (G *ᵥ W) b := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      have hs : G a b = G b a := realMetricFn_symm k c z a b
      change W a * realCoord v b * G a b = realCoord v b * (G b a * W a)
      rw [hs]
      ring
    _ = ∑ b : RIdx n, realCoord v b * D b := by rw [hGW]
    _ = _ := (fderiv_real_basis_expansion (inChart c f) z v).symm

theorem smoothFn_contMDiff (f : M.Carrier → ℝ) (hf : SmoothFn f) :
    letI := manifold_realSmooth M
    ContMDiff 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ℝ) ∞ f := by
  letI := manifold_realSmooth M
  intro x
  have hlocal : ContMDiffAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ℝ) ∞ (inChart x f) (chartPt x x) :=
    ((hf x).contDiffAt ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds
      (mem_extChartAt_target x))).contMDiffAt
  have hchart : ContMDiffAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) ∞ (chartPt x) x :=
    contMDiffAt_extChartAt' (mem_chart_source _ _)
  have H := hlocal.comp x hchart
  apply H.congr_of_eventuallyEq
  filter_upwards [(chartAt (ComplexVector n) x).open_source.mem_nhds (mem_chart_source _ _)] with y hy
  exact congrArg f ((extChartAt (ComplexModel n) x).left_inv (by
    simpa only [extChartAt_source, Set.mem_preimage] using hy)).symm

end Yau.Proofs.C05GradientFlowAux
