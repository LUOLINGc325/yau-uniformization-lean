import Yau.Proofs.C05ScalarTimeSourceBoundsJets
import Yau.Proofs.C05RicciTimePolynomialBudgetActual

/-! The zeroth third-source estimate uses the actual half-Ricci/Hessian pairing. -/
noncomputable section
open scoped Topology Manifold ContDiff Matrix
namespace Yau.Proofs.C05ScalarTimeSourceBoundsAux
open Yau Yau.Proofs.C05Aux Yau.Proofs.C05NormalizedScalarTimeEvolutionAux
open Yau.Proofs.C05ThirdScalarTimeAux Yau.Proofs.C05RicciTimePolynomialBudgetAux
open Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux Yau.NodeProofs.G01Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

theorem ricciLeviPairing_abs_le (k : HermitianField M) (hk : MetricSmooth k)
    (hK : KahlerClosed k) (f : M.Carrier → ℝ) (hf : SmoothFn f) (x : M.Carrier) :
    |ricciLeviPairing k f x| ≤ (1/2:ℝ) * realRicciJetNorm k 0 x * scalarJetNorm k f 2 x := by
  rw [ricciLeviPairing_eq_half_hessian_pair k hk hK f hf x, abs_mul,
    abs_of_pos (by norm_num : (0:ℝ) < 1/2)]
  have H := covTensorPair_abs_le_norm (realMetricFn k x (chartPt x x))
    (realMetricFn_posDef k x _ (mem_extChartAt_target x))
    (realRicciJet k x 0 (chartPt x x)) (scalarJet k f x 2 (chartPt x x))
  simpa only [metricTensorNorm, realRicciJetNorm, scalarJetNorm, mul_assoc] using
    mul_le_mul_of_nonneg_left H (by norm_num : (0:ℝ) ≤ 1/2)

theorem trace_polynomial_bounds (k : HermitianField M) (hk : MetricSmooth k)
    (hK : KahlerClosed k) (x : M.Carrier) {B : ℝ} (hB : 0 ≤ B)
    (hScalar : scalarJetNorm k (scalarCurvature k) 2 x ≤ B)
    (hRicci : realRicciJetNorm k 0 x ≤ B) :
    |ricciSquareLevi k x| ≤ (realDimension n+1)^2 * B^3 ∧
    |leviScalarSquare k x| ≤ (realDimension n+1)^2 * B^2 ∧
    |ricciQuartic k x| ≤ (realDimension n+1)^2 * B^4 := by
  let G := realMetricFn k x (chartPt x x)
  let NA := metricTensorNorm G (matrixCovTensor (Matrix.of (realRicciCoeff k x (chartPt x x))))
  let NH := metricTensorNorm G (matrixCovTensor ((2:ℝ) • rawReal (levi (scalarCurvature k) x)))
  have hNA0 : 0 ≤ NA := metricTensorNorm_nonneg G _
  have hNH0 : 0 ≤ NH := metricTensorNorm_nonneg G _
  have hNA : NA ≤ B := hRicci
  have hNH : NH ≤ B :=
    (realLevi_norm_le_scalarHessian k hk hK _ (scalarCurvature_smoothFn k hk hK) x).trans hScalar
  have Hq : |ricciSquareLevi k x| ≤ (realDimension n+1)^2 * NA^2 * NH :=
    ricciSquareLevi_abs_le k hk hK x
  have Hs : |leviScalarSquare k x| ≤ (realDimension n+1)^2 * NH^2 :=
    leviScalarSquare_abs_le k x
  have Ht : |ricciQuartic k x| ≤ (realDimension n+1)^2 * NA^4 :=
    ricciQuartic_abs_le k hk hK x
  have hpowA2 := pow_le_pow_left₀ hNA0 hNA 2
  have hprod := mul_le_mul hpowA2 hNH hNH0 (sq_nonneg B)
  refine ⟨?_, ?_, ?_⟩
  · calc
      _ ≤ (realDimension n+1)^2 * NA^2 * NH := Hq
      _ = (realDimension n+1)^2 * (NA^2 * NH) := by ring
      _ ≤ (realDimension n+1)^2 * (B^2 * B) :=
        mul_le_mul_of_nonneg_left hprod (sq_nonneg _)
      _ = _ := by ring
  · exact Hs.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hNH0 hNH 2) (sq_nonneg _))
  · exact Ht.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hNA0 hNA 4) (sq_nonneg _))

theorem source3_abs_bound (k : HermitianField M) (hk : MetricSmooth k) (hK : KahlerClosed k)
    (x : M.Carrier) {B : ℝ} (hB : 0 ≤ B)
    (hScalar : ∀ j ≤ 6, scalarJetNorm k (scalarCurvature k) j x ≤ B)
    (hRicci : ∀ j ≤ 4, realRicciJetNorm k j x ≤ B) :
    |scalarTimeSource3 k x| ≤ b3 n B := by
  let L := laplacian k (scalarTimeSource2 k) x
  let P := ricciLeviPairing k (scalarTimeSource1 k) x
  let Q := ricciSquareLevi k x
  let S := leviScalarSquare k x
  let T := ricciQuartic k x
  have HL := scalarJetNorm_laplacian_le k hk hK _ (source2_smoothFn k hk hK) 0 x
  have hl : |L| ≤ Real.sqrt (realDimension n)/2 * b2 n B := by
    rw [← scalarJetNorm_zero k (laplacian k (scalarTimeSource2 k)) x]
    exact HL.trans (mul_le_mul_of_nonneg_left
      (source2_jet_bound k hk hK 2 (by norm_num) x hB hScalar hRicci)
      (div_nonneg (Real.sqrt_nonneg _) (by norm_num : (0:ℝ) ≤ 2)))
  have HP := ricciLeviPairing_abs_le k hk hK _ (source1_smoothFn k hk hK) x
  have hp : |P| ≤ (1/2:ℝ) * B * b1 n B := by
    have Hprod := mul_le_mul (hRicci 0 (by norm_num))
      (source1_jet_bound k hk hK 2 (by norm_num) x hB hScalar hRicci)
      (scalarJetNorm_nonneg k (scalarTimeSource1 k) 2 x) hB
    exact HP.trans (by nlinarith [mul_le_mul_of_nonneg_left Hprod (by norm_num : (0:ℝ) ≤ 1/2)])
  obtain ⟨hq, hs, ht⟩ := trace_polynomial_bounds k hk hK x hB
    (hScalar 2 (by norm_num)) (hRicci 0 (by norm_num))
  change |Q| ≤ _ at hq
  change |S| ≤ _ at hs
  change |T| ≤ _ at ht
  have H0 := abs_add_le L (4*P)
  have H1 := abs_add_le (L+4*P) (12*Q)
  have H2 := abs_add_le (L+4*P+12*Q) (3*S)
  have H3 := abs_add_le (L+4*P+12*Q+3*S) (6*T)
  simp only [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 4),
    abs_of_nonneg (by norm_num : (0:ℝ) ≤ 12), abs_of_nonneg (by norm_num : (0:ℝ) ≤ 3),
    abs_of_nonneg (by norm_num : (0:ℝ) ≤ 6)] at H0 H1 H2 H3
  change |L+4*P+12*Q+3*S+6*T| ≤ _
  unfold b3
  nlinarith

end Yau.Proofs.C05ScalarTimeSourceBoundsAux
