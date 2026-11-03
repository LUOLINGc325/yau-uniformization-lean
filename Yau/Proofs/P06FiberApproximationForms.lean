import Yau.Proofs.P06FiberApproximationMatrix
import Yau.Proofs.P06FiberPolynomial
import Yau.Proofs.P06FiberClips

noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ComplexOrder MatrixOrder
namespace Yau.NodeProofs.P06Aux.FiberApprox
open Yau Yau.LeafProofs G04Aux Clip
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {M : ComplexManifold n}

/-- The intrinsic Hermitian matrix to which the scalar function is applied. -/
theorem whiteHermitian (g : HermitianField M) (A : RealForm M 2)
    (h11 : RealOneOne A) (x : M.Carrier) :
    (metricWhiten (gMat g x) (formHermitianMatrix A x)).IsHermitian :=
  metricWhiten_hermitian _ _ ((representsSelf A h11).2 x)

/-- The actual smooth compact input supplies one positive bound for every fibre spectrum. -/
theorem exists_global_spectral_bound (g : SmoothMetric M) (A : RealForm M 2)
    (hA : SmoothRealForm A) (hcA : CompactlySupportedRealForm A) (h11 : RealOneOne A) :
    ∃ R : ℝ, 0 < R ∧ ∀ x i, (whiteHermitian g.form A h11 x).eigenvalues i ∈ Icc (-R) R := by
  obtain ⟨B, hB⟩ := (L03.formNormSq_continuous g A hA).bddAbove_range_of_hasCompactSupport
    (L03.formNormSq_hasCompactSupport g.form A hcA)
  refine ⟨max B 0 + 1, by positivity, ?_⟩
  intro x i
  have hb : formNormSq g.form A x ≤ B := hB (mem_range_self x)
  rw [formNormSq_eq_pointFormHS g.form A h11 x] at hb
  have he := abs_eigenvalues_le_matrixToHS _ (whiteHermitian g.form A h11 x) i
  change |(whiteHermitian g.form A h11 x).eigenvalues i| ≤ ‖pointFormHS g.form A x‖ at he
  have hm : B ≤ max B 0 := le_max_left _ _
  have hp : 0 ≤ max B 0 := le_max_right _ _
  have hn := norm_nonneg (pointFormHS g.form A x)
  have he' : |(whiteHermitian g.form A h11 x).eigenvalues i| ≤ max B 0 + 1 := by
    have hh : ‖pointFormHS g.form A x‖ ≤ max B 0 + 1 := by nlinarith
    exact he.trans hh
  exact abs_le.mp he'

/-- The raw functional-calculus form, reconstructed on the original tangent fibres. -/
def functionalForm (g : HermitianField M) (A : RealForm M 2) (F : ℝ → ℝ) : RealForm M 2 :=
  iotaRealForm (fun x => metricUnwhiten (gMat g x)
    (cfc F (metricWhiten (gMat g x) (formHermitianMatrix A x))))
    (fun x => metricUnwhiten_hermitian _ _ IsSelfAdjoint.cfc)

theorem functionalForm_oneOne (g : HermitianField M) (A : RealForm M 2) (F : ℝ → ℝ) :
    RealOneOne (functionalForm g A F) := iotaRealForm_oneOne _ _

theorem functionalForm_matrix (g : HermitianField M) (A : RealForm M 2) (F : ℝ → ℝ)
    (x : M.Carrier) : formHermitianMatrix (functionalForm g A F) x =
      metricUnwhiten (gMat g x) (cfc F (metricWhiten (gMat g x) (formHermitianMatrix A x))) :=
  formHermitianMatrix_of_representsIota _ _ (iotaRealForm_represents _ _) x

theorem pointFormHS_functionalForm (g : HermitianField M) (A : RealForm M 2) (F : ℝ → ℝ)
    (x : M.Carrier) : pointFormHS g (functionalForm g A F) x =
      matrixToHS (cfc F (metricWhiten (gMat g x) (formHermitianMatrix A x))) := by
  rw [pointFormHS, functionalForm_matrix, relativeMatrixHS, metricWhiten_unwhiten (gMat g x) _
    (L12Aux.hMat_posDef g x (chartPt x x) (mem_extChartAt_target x))]

theorem pointFormHS_polynomialForm (g : HermitianField M) (A : RealForm M 2)
    (h11 : RealOneOne A) (p : Polynomial ℝ) (x : M.Carrier) :
    pointFormHS g (FiberPoly.polynomialForm g A h11 p) x =
      matrixToHS (Polynomial.aeval (metricWhiten (gMat g x) (formHermitianMatrix A x)) p) := by
  rw [pointFormHS, FiberPoly.polynomialForm_matrix, relativeMatrixHS,
    FiberPoly.fiberMatrix, metricWhiten_aeval (gMat g x) (formHermitianMatrix A x)
      (L12Aux.hMat_posDef g x (chartPt x x) (mem_extChartAt_target x))]

theorem functionalForm_pointNorm_le (g : HermitianField M) (A : RealForm M 2)
    (h11 : RealOneOne A) (F : ℝ → ℝ) (hF : LipschitzWith 1 F) (h0 : F 0 = 0)
    (x : M.Carrier) : ‖pointFormHS g (functionalForm g A F) x‖ ≤ ‖pointFormHS g A x‖ := by
  rw [pointFormHS_functionalForm]
  exact cfc_matrixToHS_norm_le _ (whiteHermitian g A h11 x) F hF h0

theorem polynomialForm_pointNorm_le (g : HermitianField M) (A : RealForm M 2)
    (h11 : RealOneOne A) (p : Polynomial ℝ) {R : ℝ} (hR : 0 ≤ R)
    (hs : ∀ x i, (whiteHermitian g A h11 x).eigenvalues i ∈ Icc (-R) R)
    (hp : p.eval 0 = 0) (hd : ∀ x ∈ Icc (-R) R, |p.derivative.eval x| ≤ 1)
    (x : M.Carrier) : ‖pointFormHS g (FiberPoly.polynomialForm g A h11 p) x‖ ≤
      ‖pointFormHS g A x‖ := by
  rw [pointFormHS_polynomialForm]
  exact aeval_matrixToHS_norm_le _ (whiteHermitian g A h11 x) p (hs x) hR hp hd

/-- Pointwise convergence is proved before any coefficient measurability is used. -/
theorem polynomialForm_matrix_tendsto (g : HermitianField M) (A : RealForm M 2)
    (h11 : RealOneOne A) (p : ℕ → Polynomial ℝ) (F : ℝ → ℝ) {R : ℝ}
    (hs : ∀ x i, (whiteHermitian g A h11 x).eigenvalues i ∈ Icc (-R) R)
    (ht : TendstoUniformlyOn (fun j x => (p j).eval x) F atTop (Icc (-R) R))
    (x : M.Carrier) : Tendsto (fun j => FiberPoly.fiberMatrix g A (p j) x) atTop
      (𝓝 (metricUnwhiten (gMat g x)
        (cfc F (metricWhiten (gMat g x) (formHermitianMatrix A x))))) := by
  have hm := aeval_tendsto_of_uniform _ (whiteHermitian g A h11 x) p F (hs x) ht
  have hc : Continuous (metricUnwhiten (gMat g x)) := by
    change Continuous (fun X : Matrix (Fin n) (Fin n) ℂ => metricRoot (gMat g x) * X * metricRoot (gMat g x))
    fun_prop
  have hH : (gMat g x).PosDef := L12Aux.hMat_posDef g x (chartPt x x) (mem_extChartAt_target x)
  have he (j : ℕ) : FiberPoly.fiberMatrix g A (p j) x =
      metricUnwhiten (gMat g x)
        (Polynomial.aeval (metricWhiten (gMat g x) (formHermitianMatrix A x)) (p j)) := by
    have hu := congrArg (metricUnwhiten (gMat g x))
      (metricWhiten_aeval (gMat g x) (formHermitianMatrix A x) hH (p j))
    rw [metricUnwhiten_whiten (gMat g x) _ hH] at hu
    exact hu
  simpa only [he, Function.comp_def] using (hc.tendsto _).comp hm

theorem polynomialForm_evaluation_tendsto (g : HermitianField M) (A : RealForm M 2)
    (h11 : RealOneOne A) (p : ℕ → Polynomial ℝ) (F : ℝ → ℝ) {R : ℝ}
    (hs : ∀ x i, (whiteHermitian g A h11 x).eigenvalues i ∈ Icc (-R) R)
    (ht : TendstoUniformlyOn (fun j x => (p j).eval x) F atTop (Icc (-R) R))
    (x : M.Carrier) (v : Fin 2 → TangentVector M x) :
    Tendsto (fun j => FiberPoly.polynomialForm g A h11 (p j) x v) atTop
      (𝓝 (functionalForm g A F x v)) := by
  have hc : Continuous (fun B : Matrix (Fin n) (Fin n) ℂ =>
      2 * (matrixPairing B (tangentCoords x x (v 0)) (tangentCoords x x (v 1))).im) := by
    dsimp only [matrixPairing]
    fun_prop
  exact (hc.tendsto _).comp (polynomialForm_matrix_tendsto g A h11 p F hs ht x)

end Yau.NodeProofs.P06Aux.FiberApprox
