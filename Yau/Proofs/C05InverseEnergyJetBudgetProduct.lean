import Yau.Proofs.C05TensorProductThird
import Yau.Proofs.C05RicciLeviJetBounds

/-! The first three computed jets of the actual differential square. -/
noncomputable section
open scoped Topology Manifold ContDiff Matrix
namespace Yau.Proofs.C05InverseEnergyJetBudgetAux
open Yau Yau.Proofs.C05Aux Yau.Proofs.C05RicciSquareJetsAux
open Yau.Proofs.C05HessianPropagationAux Yau.Proofs.C05QJetBudgetAux
open Yau.Proofs.C05TensorProductThirdAux Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

theorem differential_square_jets_le (k : HermitianField M) (hk : MetricSmooth k)
    (f : M.Carrier → ℝ) (hf : SmoothFn f) (x : M.Carrier) {CB : ℝ} (hCB : 0 ≤ CB)
    (hF : ∀ j ≤ 4, scalarJetNorm k f j x ≤ CB) :
    ∀ j ≤ 3, metricTensorNorm (realMetricFn k x (chartPt x x))
      (Generic.jet k x (fun w => tensorConcatProduct (scalarJet k f x 1 w)
        (scalarJet k f x 1 w)) j (chartPt x x)) ≤ 8 * CB ^ 2 := by
  let G := realMetricFn k x (chartPt x x)
  let z := chartPt x x
  let p := scalarJet k f x 1
  let P := fun w => tensorConcatProduct (p w) (p w)
  let N := fun j => metricTensorNorm G (Generic.jet k x p j z)
  have hz : z ∈ chartTarget x := mem_extChartAt_target x
  have hG := realMetricFn_posDef k x z hz
  have hp := scalarJet_contDiffOn k hk f hf x 1
  have hpd v := ((hp v).contDiffAt
    ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt (by simp)
  have hN (j : ℕ) (hj : j ≤ 3) : N j ≤ CB := by
    dsimp only [N,p]
    rw [computedJet_scalarJet]
    exact hF (1+j) (by omega)
  have hprod (i j : ℕ) (hi : i ≤ 3) (hj : j ≤ 3) : N i * N j ≤ CB^2 := by
    rw [pow_two]
    exact mul_le_mul (hN i hi) (hN j hj) (metricTensorNorm_nonneg _ _) hCB
  intro j hj
  change metricTensorNorm G (Generic.jet k x P j z) ≤ 8*CB^2
  interval_cases j
  · change metricTensorNorm G (tensorConcatProduct (p z) (p z)) ≤ _
    rw [metricTensorNorm_concatProduct G hG]
    change N 0 * N 0 ≤ _
    nlinarith [hprod 0 0 (by omega) (by omega),sq_nonneg CB]
  · have H := covariantD_concatProduct_norm_le k x p p z G hG hpd hpd
    change metricTensorNorm G (Generic.jet k x P 1 z) ≤ N 1*N 0+N 0*N 1 at H
    have H₁ := hprod 1 0 (by omega) (by omega)
    have H₂ := hprod 0 1 (by omega) (by omega)
    nlinarith [sq_nonneg CB]
  · have H := covariantD_twice_product_norm_le k hk x p p hp hp hz G hG
    change metricTensorNorm G (Generic.jet k x P 2 z) ≤ N 2*N 0+2*N 1*N 1+N 0*N 2 at H
    have H₁ := hprod 2 0 (by omega) (by omega)
    have H₂ := hprod 1 1 (by omega) (by omega)
    have H₃ := hprod 0 2 (by omega) (by omega)
    nlinarith [sq_nonneg CB]
  · have H := covariantD_thrice_product_norm_le k hk x p p hp hp hz G hG
    change metricTensorNorm G (Generic.jet k x P 3 z) ≤
      N 3*N 0+3*N 2*N 1+3*N 1*N 2+N 0*N 3 at H
    have H₁ := hprod 3 0 (by omega) (by omega)
    have H₂ := hprod 2 1 (by omega) (by omega)
    have H₃ := hprod 1 2 (by omega) (by omega)
    have H₄ := hprod 0 3 (by omega) (by omega)
    nlinarith

end Yau.Proofs.C05InverseEnergyJetBudgetAux
