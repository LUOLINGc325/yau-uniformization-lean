import Yau.Proofs.C05ScalarHarnack
import Yau.Proofs.C05FlowRegularity
import Yau.Proofs.G04FlowNormalization

/-! The Harnack quadratic is one-half the actual real Ricci inverse energy
of the real scalar differential. The inverse transpose is preserved. -/

noncomputable section
open scoped Manifold Topology ContDiff ComplexOrder

namespace Yau.Proofs.C05Aux
open Yau Blueprint Yau.LeafProofs.L18Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem inverse_twice_realRepresentation (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosDef) :
    ((2 : ℝ) • realRepresentation A)⁻¹ =
      (1 / 2 : ℝ) • realRepresentation A⁻¹ := by
  apply Matrix.inv_eq_left_inv
  have hi : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A (hA.isUnit.map Matrix.detMonoidHom)
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    ← realRepresentation_mul, hi, realRepresentation_one]
  norm_num

def realRicciDifferentialEnergy (k : HermitianField M) (f : M.Carrier → ℝ)
    (x : M.Carrier) : ℝ :=
  (1 / 2 : ℝ) * ∑ a : RIdx n, ∑ b : RIdx n,
    ((Matrix.of (realRicciCoeff k x (chartPt x x)))⁻¹ a b) *
      rDeriv (inChart x f) (chartPt x x) a * rDeriv (inChart x f) (chartPt x x) b

theorem scalar_differential_ricci_dual_eq (k : HermitianField M) (hk : MetricSmooth k)
    (hK : KahlerClosed k) (f : M.Carrier → ℝ) (hf : SmoothFn f) (x : M.Carrier)
    (hA : (ricci k x).PosDef) :
    dualNormMat (ricci k x) (WithLp.toLp 2 (fun i =>
      wirt (fun z => Complex.ofReal (inChart x f z)) (chartPt x x) (stdVec i))) =
        realRicciDifferentialEnergy k f x := by
  have hz : chartPt x x ∈ chartTarget x := mem_extChartAt_target x
  have hdf := ((hf x).contDiffAt
    ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt (by simp)
  have hreal : Matrix.of (realRicciCoeff k x (chartPt x x)) =
      (2 : ℝ) • realRepresentation (ricci k x) := by
    ext a b
    rw [Matrix.of_apply, Yau.NodeProofs.G04Aux.realRicciCoeff_center_raw k hk hK]
    rw [Matrix.smul_apply, smul_eq_mul, realRepresentation_apply]
    rfl
  unfold realRicciDifferentialEnergy dualNormMat
  rw [hreal, inverse_twice_realRepresentation _ hA, complex_dual_quadratic_realification]
  simp only [WithLp.ofLp_toLp, Matrix.smul_apply, smul_eq_mul]
  simp_rw [wirt_ofReal_real_coordinates hdf]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

end Yau.Proofs.C05Aux
