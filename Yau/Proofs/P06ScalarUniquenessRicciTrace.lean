import Yau.Proofs.G01

/-! Trace of the actual Chern connection and curvature, with the original
computed log determinant and Levi convention. -/

noncomputable section
open Filter
open scoped Manifold Topology ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.P06Aux
open Yau Yau.LeafProofs Yau.NodeProofs.G01Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem chernA_trace_eq_wirt_logDet
    (h : HermitianField M) (hs : MetricSmooth h) (hk : KahlerClosed h)
    (x : M.Carrier) (z : ComplexVector n) (hz : z ∈ chartTarget x) (k : Fin n) :
    Matrix.trace (chernA h x z k) =
      wirt (fun w => (logDet h x w : ℂ)) z (stdVec k) := by
  have hzero := connectionTrace_eq_logDet h hs x z hz (k, 0)
  have hone := connectionTrace_eq_logDet h hs x z hz (k, 1)
  rw [L12Aux.connectionTrace, connectionMatrix_eq_chernRealA h hs hk x z hz,
    rawReal_trace] at hzero hone
  simp only [chernRealA, Fin.reduceEq, ↓reduceIte, Matrix.trace_smul, smul_eq_mul,
    Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub] at hzero hone
  have hdf : DifferentiableAt ℝ (logDet h x) z :=
    ((L17Aux.logDet_contDiffOn_of_metricSmooth h hs x).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt (by simp)
  have hd : fderiv ℝ (fun w => (logDet h x w : ℂ)) z =
      Complex.ofRealCLM.comp (fderiv ℝ (logDet h x) z) :=
    (Complex.ofRealCLM.hasFDerivAt.comp z hdf.hasFDerivAt).fderiv
  apply Complex.ext <;>
    norm_num [wirt, hd, ContinuousLinearMap.comp_apply, Complex.mul_re, Complex.mul_im] <;>
    simp only [rDeriv, realVec, Fin.reduceEq, ↓reduceIte, stdVec, one_smul] at hzero hone ⊢ <;>
    linarith

theorem chernF_trace_eq_ricciInChart
    (h : HermitianField M) (hs : MetricSmooth h) (hk : KahlerClosed h)
    (x : M.Carrier) (z : ComplexVector n) (hz : z ∈ chartTarget x) (k l : Fin n) :
    Matrix.trace (chernF h x z k l) = (-leviC (logDet h x) z) l k := by
  have hA (a : Fin n) : DifferentiableAt ℝ (fun w => chernA h x w k a a) z :=
    ((chernA_contDiffOn h hs x k a a).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt (by simp)
  have he : (fun w => Matrix.trace (chernA h x w k)) =ᶠ[𝓝 z]
      (fun w => wirt (fun q => (logDet h x q : ℂ)) w (stdVec k)) := by
    filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz] with w hw
    exact chernA_trace_eq_wirt_logDet h hs hk x w hw k
  have hf : ContDiffAt ℝ 2 (fun w => (logDet h x w : ℂ)) z :=
    (((L17Aux.logDet_contDiffOn_of_metricSmooth h hs x).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).of_le (by simp)).continuousLinearMap_comp Complex.ofRealCLM
  simp only [Matrix.trace, Matrix.diag_apply, chernF, Matrix.neg_apply, matrixWirtBar]
  rw [Finset.sum_neg_distrib, ← L14Aux.wirtBar_sum_fun Finset.univ
    (fun a w => chernA h x w k a a) z (stdVec l) (fun a _ => hA a)]
  have hd := congrArg (fun L : ComplexVector n →L[ℝ] ℂ => L (stdVec l)) (he.fderiv_eq (𝕜 := ℝ))
  have hdI := congrArg (fun L : ComplexVector n →L[ℝ] ℂ => L (Complex.I • stdVec l))
    (he.fderiv_eq (𝕜 := ℝ))
  change -wirtBar (fun w => Matrix.trace (chernA h x w k)) z (stdVec l) = _
  unfold wirtBar
  rw [hd, hdI]
  change -wirtBar (fun w => wirt (fun q => (logDet h x q : ℂ)) w (stdVec k)) z (stdVec l) = _
  rw [← L14Aux.wirt_wirtBar_comm _ z hf (stdVec l) (stdVec k)]
  rfl

end Yau.NodeProofs.P06Aux
