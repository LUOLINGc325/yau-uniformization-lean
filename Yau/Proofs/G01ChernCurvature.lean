import Yau.Proofs.G01ChernCalculus

noncomputable section
open Filter
open scoped Manifold Topology ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.G01Aux
open Yau Yau.LeafProofs
variable {n : ℕ} {M : ComplexManifold n}

/-- Differentiating the actual metric-lowering identity identifies the local Chern calculator. -/
theorem chernF_lower (h : HermitianField M) (hs : MetricSmooth h) (x : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ chartTarget x) (i j k l : Fin n) :
    (hMat h x z * chernF h x z k l) j i = chernInChart h x z i j k l := by
  have hH (a b : Fin n) : DifferentiableAt ℝ (fun w => hMat h x w a b) z :=
    ((L17Aux.hMat_contDiffOn_of_metricSmooth h hs x a b).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt (by simp)
  have hA (a b : Fin n) : DifferentiableAt ℝ (fun w => chernA h x w k a b) z :=
    ((chernA_contDiffOn h hs x k a b).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt (by simp)
  have hd : matrixWirtBar (fun w => hMat h x w * chernA h x w k) z l =
      matrixWirtBar (fun w => matrixWirt (hMat h x) w k) z l := by
    ext a b
    have he : (fun w => (hMat h x w * chernA h x w k) a b) =ᶠ[𝓝 z]
        (fun w => matrixWirt (hMat h x) w k a b) := by
      filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz] with w hw
      exact congrArg (fun A => A a b) (chernA_lower h x w hw k)
    unfold matrixWirtBar wirtBar
    rw [he.fderiv_eq]
  rw [matrixWirtBar_mul _ _ z hH hA l] at hd
  have hl : hMat h x z * chernF h x z k l =
      -matrixWirtBar (fun w => matrixWirt (hMat h x) w k) z l +
        matrixWirtBar (hMat h x) z l * chernA h x z k := by
    unfold chernF
    rw [Matrix.mul_neg, eq_sub_of_add_eq' hd]
    noncomm_ring
  rw [hl]
  have hf : ContDiffAt ℝ 2 (fun w => hMat h x w j i) z :=
    ((L17Aux.hMat_contDiffOn_of_metricSmooth h hs x j i).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).of_le (by simp)
  simp only [Matrix.add_apply, Matrix.neg_apply, Matrix.mul_apply,
    chernA, BundleDbar.chernConnectionMatrix, Matrix.of_apply, matrixWirtBar, matrixWirt,
    chernInChart]
  rw [← L14Aux.wirt_wirtBar_comm _ z hf (stdVec l) (stdVec k)]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  ring

/-- The Kähler symmetry of the actual connection persists under its local anti-holomorphic derivative. -/
theorem chern_holomorphic_symm (h : HermitianField M) (hs : MetricSmooth h)
    (hk : KahlerClosed h) (x : M.Carrier) (z : ComplexVector n)
    (hz : z ∈ chartTarget x) (i j k l : Fin n) :
    chernInChart h x z i j k l = chernInChart h x z k j i l := by
  rw [← chernF_lower h hs x z hz i j k l, ← chernF_lower h hs x z hz k j i l]
  simp only [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro p _
  congr 1
  have he : (fun w => chernA h x w k p i) =ᶠ[𝓝 z]
      (fun w => chernA h x w i p k) := by
    filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz] with w hw
    exact chernA_torsion_symm h hs hk x w hw k i p
  change -wirtBar (fun w => chernA h x w k p i) z (stdVec l) =
    -wirtBar (fun w => chernA h x w i p k) z (stdVec l)
  unfold wirtBar
  rw [he.fderiv_eq]

end Yau.NodeProofs.G01Aux
