import Yau.Proofs.C05RicciInverseEnergyRegularity
import Yau.Proofs.C05InverseEnergySpatialError
import Yau.Proofs.G04ScalarNormalization
import Yau.LeafProofs.L23ScalarCalculus

/-! The spatial expansion is the Laplacian of the actual global inverse
Ricci energy. The factors one-half in Q and in the complex Laplacian remain. -/

noncomputable section
open Filter
open scoped Topology Manifold ContDiff Matrix ComplexOrder
namespace Yau.Proofs.C05Aux
open Yau Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux Yau.LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

theorem scalarJet_one_apply (k : HermitianField M) (f : M.Carrier → ℝ)
    (c : M.Carrier) (z : ComplexVector n) (v : Fin 1 → RIdx n) :
    scalarJet k f c 1 z v = rDeriv (inChart c f) z (v 0) := by
  have he : v = ![v 0] := by funext i; fin_cases i; rfl
  rw [he,scalarJet_one]
  rfl

theorem covectorSquare_eq_tensorProduct (p : CovTensor n 1) :
    covectorSquare p = tensorProduct (fun _ : Fin 2 => fun a => p ![a]) := by
  funext v
  simp only [covectorSquare,tensorConcatProduct,tensorProduct,Fin.prod_univ_two]
  congr 1 <;> congr 1 <;> funext j <;> fin_cases j <;> rfl

theorem ricciInverseEnergyInChart_eq_pair (k : HermitianField M)
    (f : M.Carrier → ℝ) (c : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget c) :
    ricciInverseEnergyInChart k f c z = (1 / 2 : ℝ) *
      covTensorPair (realMetricFn k c z) (ricciInverseTensor k c z)
        (covectorSquare (scalarJet k f c 1 z)) := by
  rw [covectorSquare_eq_tensorProduct]
  simp_rw [scalarJet_one]
  rw [ricciInverseTensor,loweredInverseMatrix_pair _ _ (realMetricFn_posDef k c z hz)]
  rfl

theorem chartRealLaplacian_congr_nhds (k : HermitianField M) (c : M.Carrier)
    {F H : ComplexVector n → ℝ} {z : ComplexVector n} (he : F =ᶠ[𝓝 z] H) :
    chartRealLaplacian k c F z = chartRealLaplacian k c H z := by
  have hd (j : RIdx n) : (fun w => rDeriv F w j) =ᶠ[𝓝 z]
      (fun w => rDeriv H w j) := (he.fderiv (𝕜 := ℝ)).mono (fun w hw =>
        congrArg (fun L : ComplexVector n →L[ℝ] ℝ => L (realVec j)) hw)
  simp only [chartRealLaplacian,chartCovHessian,rDeriv,he.fderiv_eq]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hj := (hd j).fderiv_eq (𝕜 := ℝ)
  dsimp only [rDeriv] at hj
  rw [hj]

theorem chartRealLaplacian_const_mul (k : HermitianField M) (c : M.Carrier)
    {F : ComplexVector n → ℝ} {z : ComplexVector n}
    (hF : ContDiffAt ℝ 2 F z) (a : ℝ) :
    chartRealLaplacian k c (fun w => a * F w) z = a * chartRealLaplacian k c F z := by
  have hm := chartRealLaplacian_mul k c (contDiffAt_const (c := a)) hF
  have hc : chartRealLaplacian k c (fun _ => a) z = 0 := by
    simp [chartRealLaplacian,chartCovHessian,rDeriv]
  have hg : Yau.LeafProofs.L18Aux.chartGradientPair k c (fun _ => a) F z = 0 := by
    simp [Yau.LeafProofs.L18Aux.chartGradientPair_eq_sum,rDeriv]
  simpa only [hc,hg,mul_zero,add_zero] using hm

def inverseEnergyHessianSquare (k : HermitianField M) (f : M.Carrier → ℝ)
    (c : M.Carrier) (z : ComplexVector n) : ℝ :=
  ∑ i, ∑ j, (realMetricFn k c z)⁻¹ i j *
    covTensorPair (realMetricFn k c z) (ricciInverseTensor k c z)
      (tensorConcatProduct
        (fun u => covariantD k c (scalarJet k f c 1) z (Fin.cons i u))
        (fun u => covariantD k c (scalarJet k f c 1) z (Fin.cons j u)))

theorem realRicciDifferentialEnergy_laplacian (k : HermitianField M) (hk : MetricSmooth k)
    (hK : KahlerClosed k) (hA : ∀ x, (ricci k x).PosDef)
    (f : M.Carrier → ℝ) (hf : SmoothFn f) (x : M.Carrier) :
    laplacian k (realRicciDifferentialEnergy k f) x =
      (1 / 4 : ℝ) * inverseEnergySpatialRemainder k x (ricciInverseTensor k x)
        (scalarJet k f x 1) (chartPt x x) +
      (1 / 2 : ℝ) * inverseEnergyHessianSquare k f x (chartPt x x) := by
  let C := ricciInverseTensor k x
  let p := scalarJet k f x 1
  let F : ComplexVector n → ℝ := fun w =>
    covTensorPair (realMetricFn k x w) (C w) (covectorSquare (p w))
  let z := chartPt x x
  have hz : z ∈ chartTarget x := mem_extChartAt_target x
  have hC := ricciInverseTensor_contDiffOn k hk hK hA x
  have hp := Yau.Proofs.C05HessianPropagationAux.scalarJet_contDiffOn k hk f hf x 1
  have hpp (v : Fin 2 → RIdx n) :
      ContDiffOn ℝ ∞ (fun w => covectorSquare (p w) v) (chartTarget x) :=
    (hp _).mul (hp _)
  have hF : ContDiffAt ℝ 2 F z :=
    ((chartTensorPair_contDiffOn k hk x C _ hC hpp).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).of_le (by simp)
  have he : inChart x (realRicciDifferentialEnergy k f) =ᶠ[𝓝 z]
      (fun w => (1 / 2 : ℝ) * F w) := by
    filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz] with w hw
    exact (ricciInverseEnergyInChart_eq_global k hk f hf x hw).symm.trans
      (ricciInverseEnergyInChart_eq_pair k f x hw)
  have hl := Yau.NodeProofs.G04Aux.scalarLaplacian k hk hK
    (realRicciDifferentialEnergy k f) (realRicciDifferentialEnergy_smoothFn k hk hK hA f hf)
    x z hz
  have hi : chartInv x z = x := (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  rw [hi] at hl
  change chartRealLaplacian k x (inChart x (realRicciDifferentialEnergy k f)) z = _ at hl
  rw [chartRealLaplacian_congr_nhds k x he,chartRealLaplacian_const_mul k x hF] at hl
  have hr : inverseEnergySpatialRemainder k x C p z =
      chartRealLaplacian k x F z - 2 * inverseEnergyHessianSquare k f x z := rfl
  dsimp only [C,p,z] at hl hr
  linarith

end Yau.Proofs.C05Aux
