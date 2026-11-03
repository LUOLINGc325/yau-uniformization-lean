import Yau.Proofs.P06ScalarUniquenessRicciPositive
import Yau.Proofs.P07Matrix

noncomputable section
open scoped Matrix ComplexOrder MatrixOrder
namespace Yau.Proofs.C04BisectionalScalarAux
open Yau Yau.Blueprint Yau.NodeProofs Yau.LeafProofs
variable {n : ℕ}

/-- The full positive matrix lies below its relative trace times the metric. -/
theorem posSemidef_le_metric_trace (H A : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.PosDef) (hA : A.PosSemidef) :
    HermLE A (((traceWith H A : ℝ) : ℂ) • H) := by
  obtain ⟨S, hS, hu, hSS, hSHS⟩ := G04Aux.exists_hermitian_whitening H hH
  have hQ : (S * A * S).PosSemidef := by
    simpa only [hS.eq] using hA.conjTranspose_mul_mul_same S
  have hb := P07Aux.posSemidef_le_trace_identity (S * A * S) hQ
  rw [G04Aux.whitening_trace H A S hSS] at hb
  apply (Matrix.IsUnit.posSemidef_star_left_conjugate_iff hu
    (x := ((traceWith H A : ℝ) : ℂ) • H - A)).mp
  simpa only [hS.star_eq, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_smul, Matrix.smul_mul, hSHS] using hb

theorem metric_trace_nonneg (H A : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.PosDef) (hA : A.PosSemidef) : 0 ≤ traceWith H A :=
  P06Aux.matrix_trace_mul_nonneg H⁻¹ A hH.inv.posSemidef hA

variable {M : ComplexManifold n}

/-- The Ricci and scalar bounds use the actual Chern contraction. -/
theorem ricci_scalar_bounds (k : HermitianField M) (hs : MetricSmooth k)
    (hk : KahlerClosed k) (hBC : NonnegBisectional k) (x : M.Carrier) :
    (ricci k x).PosSemidef ∧ 0 ≤ scalarCurvature k x ∧
      HermLE (ricci k x) (((scalarCurvature k x : ℝ) : ℂ) • gMat k x) := by
  have hR := P06Aux.ricci_posSemidef_of_nonnegBisectional k hs hk hBC x
  have hH : (gMat k x).PosDef :=
    L12Aux.hMat_posDef k x (chartPt x x) (mem_extChartAt_target x)
  exact ⟨hR, metric_trace_nonneg _ _ hH hR, posSemidef_le_metric_trace _ _ hH hR⟩

end Yau.Proofs.C04BisectionalScalarAux
