import Yau.Proofs.E01QuadraticMixed
import Yau.Proofs.E01QuadraticReal
import Yau.Proofs.E01InverseTranspose
import Yau.Proofs.E01InverseLeviAlgebra
import Yau.Proofs.E01MatrixWirtAdjoint
import Yau.Proofs.E01WirtingerLift
import Yau.Proofs.V03MetricSmooth

/-! The genuine product-chart dual Levi calculator, with its exact inverse-transpose square completion. -/

noncomputable section
open scoped Matrix Topology ContDiff
open Filter Set

namespace Yau.NodeProofs.E01Aux
open Yau Yau.Blueprint
open Yau.Blueprint.V03Proof

variable {n : ℕ}

theorem dualNormMat_product_mixed {U : Set (ComplexVector n)} (hU : IsOpen U)
    (H : ComplexVector n → Herm n) (hHerm : ∀ z, (H z).IsHermitian)
    (hH : ∀ i j, ContDiffOn ℝ ∞ (fun z => H z i j) U)
    (hdet : ∀ z ∈ U, (H z).det ≠ 0) (z : ComplexVector n) (hz : z ∈ U)
    (ξ a u : ComplexVector n) :
    (wirt (fun p => wirtBar (fun q : CotangentCoord n => (dualNormMat (H q.1) q.2 : ℂ))
      p (a, u)) (z, ξ) (a, u)).re =
      ellipsoidQuadratic ((H z)⁻¹)ᵀ
        (u - matrixFiberMap ((complexMatrixWirt H z a)ᵀ * ((H z)⁻¹)ᵀ) ξ) +
      ellipsoidQuadratic
        (((H z)⁻¹)ᵀ * ((complexMatrixWirt H z a)ᵀ * ((H z)⁻¹)ᵀ *
          ((complexMatrixWirt H z a)ᴴ)ᵀ -
          (complexMatrixWirt (fun w => complexMatrixWirtBar H w a) z a)ᵀ) * ((H z)⁻¹)ᵀ) ξ := by
  let p : CotangentCoord n := (z, ξ)
  let v : CotangentCoord n := (a, u)
  let Hp : CotangentCoord n → Herm n := fun q => H q.1
  let Kp : CotangentCoord n → Herm n := fun q => ((H q.1)⁻¹)ᵀ
  let L : CotangentCoord n →L[ℂ] ComplexVector n := ContinuousLinearMap.snd ℂ _ _
  let K : Herm n := ((H z)⁻¹)ᵀ
  let A : Herm n := complexMatrixWirt H z a
  let B : Herm n := complexMatrixWirt (fun w => complexMatrixWirtBar H w a) z a
  have hH2 (i j : Fin n) : ContDiffAt ℝ 2 (fun w => H w i j) z :=
    ((hH i j).contDiffAt (hU.mem_nhds hz)).of_le (by simp)
  have hHd (i j : Fin n) := (hH2 i j).differentiableAt (by norm_num)
  have hHp2 (i j : Fin n) : ContDiffAt ℝ 2 (fun q : CotangentCoord n => Hp q i j) p :=
    (hH2 i j).comp p contDiffAt_fst
  have hHpd (i j : Fin n) := (hHp2 i j).differentiableAt (by norm_num)
  have hHplocal : ∀ᶠ q in 𝓝 p, ∀ i j, DifferentiableAt ℝ (fun r => Hp r i j) q := by
    have hnear : ∀ᶠ q : CotangentCoord n in 𝓝 p, q.1 ∈ U :=
      (continuous_fst.tendsto p).eventually (hU.mem_nhds hz)
    filter_upwards [hnear] with q hq
    intro i j
    exact (((hH i j).contDiffAt (hU.mem_nhds hq)).differentiableAt (by simp)).comp q differentiableAt_fst
  have hKp2 (i j : Fin n) : ContDiffAt ℝ 2 (fun q => Kp q i j) p :=
    (((entrywise_matrix_inv_contDiffOn hH hdet j i).contDiffAt (hU.mem_nhds hz)).of_le (by simp)).comp p contDiffAt_fst
  have hbar (i j : Fin n) : DifferentiableAt ℝ (fun q => complexMatrixWirtBar Hp q v i j) p :=
    wirtBar_differentiableAt (hHp2 i j) v
  have hreal : (fun q : CotangentCoord n => (dualNormMat (H q.1) q.2 : ℂ)) =
      (fun q => star (WithLp.ofLp (L q)) ⬝ᵥ (Kp q *ᵥ WithLp.ofLp (L q))) := by
    funext q
    exact dualNormMat_complex_eq (H q.1) (hHerm q.1) q.2
  have hm := mixedWirt_quadratic_fiber Kp L p v hKp2
  have hWA : complexMatrixWirt Hp p v = A :=
    complexMatrixWirt_prod_fst H p v hHd
  have hWB : complexMatrixWirtBar Hp p v = Aᴴ := by
    rw [complexMatrixWirtBar_prod_fst H p v hHd]
    exact complexMatrixWirtBar_of_hermitian H hHerm z a
  have hWM : complexMatrixWirt (fun q => complexMatrixWirtBar Hp q v) p v = B :=
    complexMatrixMixed_prod_fst H p v hH2
  have hKw : complexMatrixWirt Kp p v = -(K * Aᵀ * K) := by
    have hh := complexMatrixWirt_invTranspose hHpd (hdet z hz) v
    rw [hWA] at hh
    simpa only [Kp, Hp, p, K, neg_mul] using hh
  have hKb : complexMatrixWirtBar Kp p v = -(K * (Aᴴ)ᵀ * K) := by
    have hh := complexMatrixWirtBar_invTranspose hHpd (hdet z hz) v
    rw [hWB] at hh
    simpa only [Kp, Hp, p, K, neg_mul] using hh
  have hKm : complexMatrixWirt (fun q => complexMatrixWirtBar Kp q v) p v =
      K * (Aᴴ)ᵀ * K * Aᵀ * K + K * Aᵀ * K * (Aᴴ)ᵀ * K - K * Bᵀ * K := by
    have hh := complexMatrix_mixed_invTranspose hHpd hHplocal (hdet z hz) v v hbar
    rw [hWA, hWB, hWM] at hh
    exact hh
  rw [hKw, hKb, hKm] at hm
  rw [hreal]
  have hre := congrArg Complex.re hm
  simp only [Complex.add_re] at hre
  change _ = ellipsoidQuadratic K (u - matrixFiberMap (Aᵀ * K) ξ) +
    ellipsoidQuadratic (K * (Aᵀ * K * (Aᴴ)ᵀ - Bᵀ) * K) ξ
  rw [hre]
  exact inverse_levi_square_completion K A B (hHerm z).inv.transpose u ξ

end Yau.NodeProofs.E01Aux
