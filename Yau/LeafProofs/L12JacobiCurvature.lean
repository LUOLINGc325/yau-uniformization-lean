import Yau.LeafProofs.L12JacobiMatrixODE
import Yau.LeafProofs.L12JacobiCalculus

/-! Genuine Levi--Civita curvature in the actual parallel frame, its Ricci
trace, and radial Jacobi determinant comparison on nonsingular intervals. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology Manifold ENNReal NNReal Matrix ContDiff Bundle ComplexOrder
namespace Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000

 theorem chartCurvatureVector_add_left (h : HermitianField M) (x : M.Carrier)
    (z u₁ u₂ v w : ComplexVector n) :
    chartCurvatureVector h x z (u₁ + u₂) v w =
      chartCurvatureVector h x z u₁ v w + chartCurvatureVector h x z u₂ v w := by
  simp only [chartCurvatureVector, map_add, ContinuousLinearMap.add_apply]
  abel

 theorem chartCurvatureVector_smul_left (h : HermitianField M) (x : M.Carrier)
    (z u v w : ComplexVector n) (c : ℝ) :
    chartCurvatureVector h x z (c • u) v w = c • chartCurvatureVector h x z u v w := by
  simp only [chartCurvatureVector, map_smul, ContinuousLinearMap.smul_apply,
    smul_sub, smul_add]

 theorem chartCurvatureVector_zero_left (h : HermitianField M) (x : M.Carrier)
    (z v w : ComplexVector n) : chartCurvatureVector h x z 0 v w = 0 := by
  simp only [chartCurvatureVector, map_zero, ContinuousLinearMap.zero_apply,
    sub_zero, zero_sub, add_zero, sub_self]

 theorem chartCurvatureVector_sum_left {ι : Type*} (h : HermitianField M) (x : M.Carrier)
    (z v w : ComplexVector n) (s : Finset ι) (u : ι → ComplexVector n) :
    chartCurvatureVector h x z (∑ a ∈ s, u a) v w =
      ∑ a ∈ s, chartCurvatureVector h x z (u a) v w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [chartCurvatureVector_zero_left]
  | @insert a s ha ih => simp only [Finset.sum_insert ha, chartCurvatureVector_add_left, ih]

/-- The actual curvature action with the two velocity slots fixed. -/
def chartJacobiCurvatureCLM (h : HermitianField M) (x : M.Carrier)
    (z T : ComplexVector n) : ComplexVector n →L[ℝ] ComplexVector n :=
  ∑ a, (realCoordCLM a).smulRight (chartCurvatureVector h x z (realVec a) T T)

theorem chartJacobiCurvatureCLM_apply (h : HermitianField M) (x : M.Carrier)
    (z T u : ComplexVector n) :
    chartJacobiCurvatureCLM h x z T u = chartCurvatureVector h x z u T T := by
  simp only [chartJacobiCurvatureCLM, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smulRight_apply, realCoordCLM_apply]
  conv_rhs => rw [← sum_realCoord_realVec u]
  rw [chartCurvatureVector_sum_left]
  simp only [chartCurvatureVector_smul_left]

/-- Curvature of the genuine Levi--Civita connection, with both velocity
slots fixed, as a linear map on the actual tangent fiber. -/
def realJacobiCurvatureOperator (g : SmoothMetric M) (x : M.Carrier)
    (T : TangentSpace 𝓘(ℝ, ComplexVector n) x) :
    TangentSpace 𝓘(ℝ, ComplexVector n) x →L[ℝ] TangentSpace 𝓘(ℝ, ComplexVector n) x :=
  (realFrameCLM x x).comp ((chartJacobiCurvatureCLM g.form x (chartPt x x)
    (realTangentCoords x x T)).comp (realTangentCoords x x))

theorem realJacobiCurvatureOperator_apply (g : SmoothMetric M) (x : M.Carrier)
    (T u : TangentSpace 𝓘(ℝ, ComplexVector n) x) :
    realJacobiCurvatureOperator g x T u = realFrameCLM x x
      (chartCurvatureVector g.form x (chartPt x x) (realTangentCoords x x u)
        (realTangentCoords x x T) (realTangentCoords x x T)) := by
  simp only [realJacobiCurvatureOperator, ContinuousLinearMap.comp_apply,
    chartJacobiCurvatureCLM_apply]

/-- The actual curvature matrix in the genuine global parallel orthonormal frame. -/
def realGeodesicCurvatureMatrix (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (t : ℝ) :
    Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ := fun i j =>
  let q := realGeodesicFlow g p t
  (underlyingRealRiemannianMetric g.form).inner q.proj
    (realGlobalParallelFrame g p t i)
    (realJacobiCurvatureOperator g q.proj q.2 (realGlobalParallelFrame g p t j))

theorem realJacobiCurvatureTermInChart_own (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (t : ℝ) (i j : Fin (2 * n)) :
    realJacobiCurvatureTermInChart g p (realGeodesicFlow g p t).proj t i j =
      (underlyingRealRiemannianMetric g.form).inner (realGeodesicFlow g p t).proj
        (realGlobalParallelFrame g p t i)
        (realJacobiCurvatureOperator g (realGeodesicFlow g p t).proj
          (realGeodesicFlow g p t).2
          (realGeodesicJacobiField g p (realInitialOrthonormalFrame g p.proj j) t)) := by
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  dsimp only [realJacobiCurvatureTermInChart]
  rw [realJacobiCurvatureOperator_apply]
  rw [← realMetricInChart_tangentCoords g.form (realGeodesicFlow g p t).proj
    (realGeodesicFlow g p t).proj (mem_chart_source _ _),
    realTangentCoords_realFrameCLM _ _ (mem_chart_source _ _)]

theorem realGeodesicJacobiField_parallel_expansion (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (t : ℝ) (j : Fin (2 * n)) :
    letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentNormedAddCommGroup g.form y
    letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentInnerProductSpace g.form y
    realGeodesicJacobiField g p (realInitialOrthonormalFrame g p.proj j) t =
      ∑ k, realGeodesicJacobiMatrix g p t k j • realGlobalParallelFrame g p t k := by
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  exact ((realGlobalParallelFrame g p t).sum_repr'
    (realGeodesicJacobiField g p (realInitialOrthonormalFrame g p.proj j) t)).symm

/-- The coordinate curvature term is the product of the actual curvature
matrix and actual differential-of-geodesic matrix. -/
theorem realJacobiCurvatureTermInChart_eq_matrix_mul (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (t : ℝ) (i j : Fin (2 * n)) :
    realJacobiCurvatureTermInChart g p (realGeodesicFlow g p t).proj t i j =
      (realGeodesicCurvatureMatrix g p t * realGeodesicJacobiMatrix g p t) i j := by
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  rw [realJacobiCurvatureTermInChart_own,
    realGeodesicJacobiField_parallel_expansion g p t j, map_sum, map_sum]
  simp only [map_smul, smul_eq_mul, Matrix.mul_apply, realGeodesicCurvatureMatrix]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The genuine Jacobi matrix solves A'' + R A = 0 in the actual
parallel orthonormal frame, without a supplied Jacobi equation. -/
theorem realGeodesicJacobiMatrixDeriv_hasDerivAt_matrix (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (t : ℝ) (i j : Fin (2 * n)) :
    HasDerivAt (fun s => realGeodesicJacobiMatrixDeriv g p s i j)
      (-(realGeodesicCurvatureMatrix g p t * realGeodesicJacobiMatrix g p t) i j) t := by
  simpa only [realJacobiCurvatureTermInChart_eq_matrix_mul] using
    realGeodesicJacobiMatrixDeriv_hasDerivAt g p t i j

theorem chartCurvatureVector_add_middle (h : HermitianField M) (x : M.Carrier)
    (z u v₁ v₂ w : ComplexVector n) :
    chartCurvatureVector h x z u (v₁ + v₂) w =
      chartCurvatureVector h x z u v₁ w + chartCurvatureVector h x z u v₂ w := by
  simp only [chartCurvatureVector, map_add, ContinuousLinearMap.add_apply]
  abel

theorem chartCurvatureVector_smul_middle (h : HermitianField M) (x : M.Carrier)
    (z u v w : ComplexVector n) (c : ℝ) :
    chartCurvatureVector h x z u (c • v) w = c • chartCurvatureVector h x z u v w := by
  simp only [chartCurvatureVector, map_smul, ContinuousLinearMap.smul_apply, smul_sub, smul_add]

theorem chartCurvatureVector_zero_middle (h : HermitianField M) (x : M.Carrier)
    (z u w : ComplexVector n) : chartCurvatureVector h x z u 0 w = 0 := by
  simp only [chartCurvatureVector, map_zero, ContinuousLinearMap.zero_apply,
    sub_zero, zero_sub, add_zero, sub_self]

theorem chartCurvatureVector_sum_middle {ι : Type*} (h : HermitianField M) (x : M.Carrier)
    (z u w : ComplexVector n) (s : Finset ι) (v : ι → ComplexVector n) :
    chartCurvatureVector h x z u (∑ a ∈ s, v a) w =
      ∑ a ∈ s, chartCurvatureVector h x z u (v a) w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [chartCurvatureVector_zero_middle]
  | @insert a s ha ih => simp only [Finset.sum_insert ha, chartCurvatureVector_add_middle, ih]

theorem chartCurvatureVector_add_right (h : HermitianField M) (x : M.Carrier)
    (z u v w₁ w₂ : ComplexVector n) :
    chartCurvatureVector h x z u v (w₁ + w₂) =
      chartCurvatureVector h x z u v w₁ + chartCurvatureVector h x z u v w₂ := by
  simp only [chartCurvatureVector, map_add, ContinuousLinearMap.add_apply]
  abel

theorem chartCurvatureVector_smul_right (h : HermitianField M) (x : M.Carrier)
    (z u v w : ComplexVector n) (c : ℝ) :
    chartCurvatureVector h x z u v (c • w) = c • chartCurvatureVector h x z u v w := by
  simp only [chartCurvatureVector, map_smul, ContinuousLinearMap.smul_apply, smul_sub, smul_add]

theorem chartCurvatureVector_zero_right (h : HermitianField M) (x : M.Carrier)
    (z u v : ComplexVector n) : chartCurvatureVector h x z u v 0 = 0 := by
  simp only [chartCurvatureVector, map_zero, ContinuousLinearMap.zero_apply,
    sub_zero, zero_sub, add_zero, sub_self]

theorem chartCurvatureVector_sum_right {ι : Type*} (h : HermitianField M) (x : M.Carrier)
    (z u v : ComplexVector n) (s : Finset ι) (w : ι → ComplexVector n) :
    chartCurvatureVector h x z u v (∑ a ∈ s, w a) =
      ∑ a ∈ s, chartCurvatureVector h x z u v (w a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [chartCurvatureVector_zero_right]
  | @insert a s ha ih => simp only [Finset.sum_insert ha, chartCurvatureVector_add_right, ih]

theorem chartCurvatureVector_eq_sum (h : HermitianField M) (x : M.Carrier)
    (z u v w : ComplexVector n) :
    chartCurvatureVector h x z u v w = ∑ a, ∑ b, ∑ c,
      (realCoord u a * realCoord v b * realCoord w c) •
        chartCurvatureVector h x z (realVec a) (realVec b) (realVec c) := by
  conv_lhs => rw [← sum_realCoord_realVec u, ← sum_realCoord_realVec v, ← sum_realCoord_realVec w]
  rw [chartCurvatureVector_sum_left]
  simp only [chartCurvatureVector_smul_left]
  simp only [chartCurvatureVector_sum_middle, chartCurvatureVector_smul_middle,
    Finset.smul_sum, smul_smul]
  simp only [chartCurvatureVector_sum_right, chartCurvatureVector_smul_right,
    Finset.smul_sum, smul_smul, mul_assoc]

theorem chartCurvatureVector_coord (g : SmoothMetric M) (x : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ chartTarget x) (u v w : ComplexVector n) (d : RIdx n) :
    realCoord (chartCurvatureVector g.form x z u v w) d = ∑ a, ∑ b, ∑ c,
      realCoord u a * realCoord v b * realCoord w c * riemannCoeff g.form x z a b c d := by
  rw [chartCurvatureVector_eq_sum]
  rw [← realCoordCLM_apply d]
  simp only [map_sum, map_smul, realCoordCLM_apply, chartCurvatureVector_basis g x z hz,
    realCoord_sum_realVec, smul_eq_mul]
  simp [realCoord_realVec]

theorem realFrameCLM_self (x : M.Carrier) (v : ComplexVector n) : realFrameCLM x x v = v := by
  have h := realTangentCoords_realFrameCLM x x (mem_chart_source _ _) v
  rwa [realTangentCoords_self] at h

theorem realTangentCoords_eq_complex_self (x : M.Carrier)
    (v : TangentSpace 𝓘(ℝ, ComplexVector n) x) :
    realTangentCoords x x v = tangentCoords x x (realTangentEquiv x v) := by
  have h := chartVec_tangentCoords x x (mem_extChartAt_source x) (realTangentEquiv x v)
  rw [chartVec_self] at h
  have h' := congrArg (tangentSpaceCastModel (ComplexModel n) x) h
  rw [realTangentCoords_self]
  have hcast : tangentSpaceCastModel (ComplexModel n) x (realTangentEquiv x v) = v := rfl
  simpa only [ContinuousLinearEquiv.apply_symm_apply, hcast] using h'.symm

theorem realGeodesicCurvatureMatrix_eq_toMatrix (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (t : ℝ) :
    letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentNormedAddCommGroup g.form y
    letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentInnerProductSpace g.form y
    realGeodesicCurvatureMatrix g p t = LinearMap.toMatrix
      (realGlobalParallelFrame g p t).toBasis (realGlobalParallelFrame g p t).toBasis
      (realJacobiCurvatureOperator g (realGeodesicFlow g p t).proj
        (realGeodesicFlow g p t).2).toLinearMap := by
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  ext i j
  simp only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.coe_toBasis, OrthonormalBasis.repr_apply_apply]
  rfl

theorem chartJacobiCurvatureCLM_toMatrix (g : SmoothMetric M) (x : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ chartTarget x) (T : ComplexVector n) (a b : RIdx n) :
    LinearMap.toMatrix (realVec_basis n) (realVec_basis n)
      (chartJacobiCurvatureCLM g.form x z T).toLinearMap a b =
      ∑ c, ∑ d, realCoord T c * realCoord T d * riemannCoeff g.form x z b c d a := by
  simp only [LinearMap.toMatrix_apply, realVec_basis_apply, realVec_basis_repr,
    ContinuousLinearMap.coe_coe, chartJacobiCurvatureCLM_apply,
    chartCurvatureVector_coord g x z hz, realCoord_realVec]
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single b]
  · simp
  · intro k _ hk
    simp [Ne.symm hk]
  · simp

/-- Basis-independent trace of the genuine Levi--Civita Jacobi operator. -/
theorem realJacobiCurvatureOperator_trace (g : SmoothMetric M) (x : M.Carrier)
    (T : TangentSpace 𝓘(ℝ, ComplexVector n) x) :
    LinearMap.trace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) x)
      (realJacobiCurvatureOperator g x T).toLinearMap = realRicciQuadratic g x T := by
  let e := (tangentSpaceCastModel 𝓘(ℝ, ComplexVector n) x).toLinearEquiv
  have hconj : e.conj (realJacobiCurvatureOperator g x T).toLinearMap =
      (chartJacobiCurvatureCLM g.form x (chartPt x x) (realTangentCoords x x T)).toLinearMap := by
    apply LinearMap.ext
    intro u
    change tangentSpaceCastModel 𝓘(ℝ, ComplexVector n) x
      (realJacobiCurvatureOperator g x T
        ((tangentSpaceCastModel 𝓘(ℝ, ComplexVector n) x).symm u)) = _
    rw [realJacobiCurvatureOperator_apply, realFrameCLM_self, realTangentCoords_self]
    exact (chartJacobiCurvatureCLM_apply g.form x (chartPt x x)
      (realTangentCoords x x T) u).symm
  have ht := LinearMap.trace_conj' (realJacobiCurvatureOperator g x T).toLinearMap e
  rw [hconj] at ht
  rw [← ht, LinearMap.trace_eq_matrix_trace ℝ (realVec_basis n)]
  simp only [Matrix.trace, Matrix.diag_apply,
    chartJacobiCurvatureCLM_toMatrix g x (chartPt x x) (mem_extChartAt_target x),
    realRicciQuadratic, ← realTangentCoords_eq_complex_self]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  simp only [realRicciMatrix, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem realMetricInChart_symm (h : HermitianField M) (x : M.Carrier)
    (z u v : ComplexVector n) : realMetricInChart h x z u v = realMetricInChart h x z v u := by
  rw [realMetricInChart_apply, realMetricInChart_apply]
  exact (underlyingRealRiemannianMetric h).symm (chartInv x z)
    (realChartVec x z u) (realChartVec x z v)

theorem chartCurvaturePairing_basis (g : SmoothMetric M) (x : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ chartTarget x) (a b c d : RIdx n) :
    realMetricInChart g.form x z
      (chartCurvatureVector g.form x z (realVec a) (realVec b) (realVec c)) (realVec d) =
      curvature4 g.form x z a b c d := by
  rw [chartCurvatureVector_basis g x z hz, map_sum, ContinuousLinearMap.sum_apply]
  simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul,
    realMetricInChart_basis g.form x z hz, curvature4, mul_comm]

theorem chartCurvaturePairing_eq_sum (g : SmoothMetric M) (x : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ chartTarget x) (u v w r : ComplexVector n) :
    realMetricInChart g.form x z (chartCurvatureVector g.form x z u v w) r =
      ∑ a, ∑ b, ∑ c, ∑ d,
        realCoord u a * realCoord v b * realCoord w c * realCoord r d *
          curvature4 g.form x z a b c d := by
  have hb (a b c : RIdx n) : realMetricInChart g.form x z
      (chartCurvatureVector g.form x z (realVec a) (realVec b) (realVec c)) r =
      ∑ d, realCoord r d * curvature4 g.form x z a b c d := by
    conv_lhs => rw [← sum_realCoord_realVec r]
    simp only [map_sum, map_smul, smul_eq_mul, chartCurvaturePairing_basis g x z hz]
  rw [chartCurvatureVector_eq_sum]
  simp only [map_sum, ContinuousLinearMap.sum_apply, map_smul,
    ContinuousLinearMap.smul_apply, smul_eq_mul, hb, Finset.mul_sum, mul_assoc]

theorem curvature4_reverse (g : SmoothMetric M) (x : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ chartTarget x) (a b c d : RIdx n) :
    curvature4 g.form x z a b c d = curvature4 g.form x z d c b a := by
  rw [curvature4_pair_swap g x z hz a b c d,
    curvature4_swap_first g.form x z c d a b,
    curvature4_swap_last g x z hz d c a b, neg_neg]

/-- Self-adjointness of the actual Jacobi curvature action follows from
the genuine Levi--Civita curvature symmetries. -/
theorem chartJacobiCurvature_pairing_symm (g : SmoothMetric M) (x : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ chartTarget x) (T u w : ComplexVector n) :
    realMetricInChart g.form x z (chartCurvatureVector g.form x z u T T) w =
      realMetricInChart g.form x z (chartCurvatureVector g.form x z w T T) u := by
  let κ := (RIdx n × RIdx n) × (RIdx n × RIdx n)
  let e : κ ≃ κ :=
    { toFun := fun q => ((q.2.2, q.2.1), (q.1.2, q.1.1))
      invFun := fun q => ((q.2.2, q.2.1), (q.1.2, q.1.1))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let f : κ → ℝ := fun q => realCoord w q.1.1 * realCoord T q.1.2 *
    realCoord T q.2.1 * realCoord u q.2.2 * curvature4 g.form x z q.1.1 q.1.2 q.2.1 q.2.2
  have hs := e.sum_comp f
  simp only [κ, Fintype.sum_prod_type] at hs
  rw [chartCurvaturePairing_eq_sum g x z hz, chartCurvaturePairing_eq_sum g x z hz]
  calc
    _ = ∑ a, ∑ b, ∑ c, ∑ d, f (e ((a, b), (c, d))) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro d _
      dsimp only [f, e, Equiv.coe_fn_mk]
      rw [curvature4_reverse g x z hz a b c d]
      ring
    _ = _ := by simpa only [κ, f, Fintype.sum_prod_type] using hs

theorem realGeodesicCurvatureMatrix_trace (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (t : ℝ) :
    (realGeodesicCurvatureMatrix g p t).trace =
      realRicciQuadratic g (realGeodesicFlow g p t).proj (realGeodesicFlow g p t).2 := by
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  rw [realGeodesicCurvatureMatrix_eq_toMatrix,
    ← LinearMap.trace_eq_matrix_trace ℝ (realGlobalParallelFrame g p t).toBasis,
    realJacobiCurvatureOperator_trace]

theorem realGeodesicCurvatureMatrix_trace_nonneg (g : SmoothMetric M)
    (hK : IsKahler g) (hR : ∀ x, (ricci g.form x).PosSemidef)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (t : ℝ) :
    0 ≤ (realGeodesicCurvatureMatrix g p t).trace := by
  rw [realGeodesicCurvatureMatrix_trace]
  exact realRicciQuadratic_nonneg g hK hR _ _

theorem realJacobiCurvatureOperator_pairing_symm (g : SmoothMetric M) (x : M.Carrier)
    (T u w : TangentSpace 𝓘(ℝ, ComplexVector n) x) :
    (underlyingRealRiemannianMetric g.form).inner x u (realJacobiCurvatureOperator g x T w) =
      (underlyingRealRiemannianMetric g.form).inner x w (realJacobiCurvatureOperator g x T u) := by
  rw [← realMetricInChart_tangentCoords g.form x x (mem_chart_source _ _),
    ← realMetricInChart_tangentCoords g.form x x (mem_chart_source _ _)]
  rw [realJacobiCurvatureOperator_apply, realJacobiCurvatureOperator_apply,
    realTangentCoords_realFrameCLM x x (mem_chart_source _ _),
    realTangentCoords_realFrameCLM x x (mem_chart_source _ _)]
  rw [realMetricInChart_symm g.form x (chartPt x x) (realTangentCoords x x u),
    realMetricInChart_symm g.form x (chartPt x x) (realTangentCoords x x w)]
  exact chartJacobiCurvature_pairing_symm g x (chartPt x x) (mem_extChartAt_target x) _ _ _

theorem realGeodesicCurvatureMatrix_isSymm (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (t : ℝ) :
    (realGeodesicCurvatureMatrix g p t).IsSymm := by
  ext i j
  exact realJacobiCurvatureOperator_pairing_symm g _ _ _ _

theorem realGeodesicJacobiMatrix_hasDerivAt_initial (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (i j : Fin (2 * n)) :
    HasDerivAt (fun t => realGeodesicJacobiMatrix g p t i j)
      ((1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) i j) 0 := by
  simpa only [realGeodesicJacobiMatrixDeriv_zero] using
    realGeodesicJacobiMatrix_hasDerivAt g p 0 i j

theorem realGeodesicJacobiMatrix_normalized_det_initial_limit (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) :
    Tendsto (fun t => (realGeodesicJacobiMatrix g p t).det / t ^ (2 * n))
      (𝓝[>] 0) (𝓝 1) := by
  simpa only [Fintype.card_fin] using matrixJacobi_normalized_det_initial_limit
    (realGeodesicJacobiMatrix_zero g p) (realGeodesicJacobiMatrix_hasDerivAt_initial g p)

theorem realGeodesicJacobiMatrix_det_pos_near_zero (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) :
    ∀ᶠ t in 𝓝[>] 0, 0 < (realGeodesicJacobiMatrix g p t).det :=
  matrixJacobi_det_pos_near_zero (realGeodesicJacobiMatrix_zero g p)
    (realGeodesicJacobiMatrix_hasDerivAt_initial g p)

/-- Actual Jacobi determinant comparison on every positive-determinant
radial interval, from genuine nonnegative project Ricci. -/
theorem realGeodesicJacobiMatrix_det_ratio_antitone (g : SmoothMetric M)
    (hK : IsKahler g) (hR : ∀ x, (ricci g.form x).PosSemidef)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (T : ℝ)
    (hdet : ∀ t ∈ Set.Ioo 0 T, 0 < (realGeodesicJacobiMatrix g p t).det) :
    AntitoneOn (fun t => (realGeodesicJacobiMatrix g p t).det / t ^ (2 * n)) (Set.Ioo 0 T) := by
  have hn := complexDimension_pos M
  have hd : 2 * n - 1 + 1 = 2 * n := by omega
  have hc : Fintype.card (Fin (2 * n)) = (2 * n - 1) + 1 := by simp only [Fintype.card_fin, hd]
  have h := matrixJacobi_det_ratio_antitone_of_initial
    (A := realGeodesicJacobiMatrix g p) (A₁ := realGeodesicJacobiMatrixDeriv g p)
    (A₂ := fun t => -(realGeodesicCurvatureMatrix g p t * realGeodesicJacobiMatrix g p t))
    (R := realGeodesicCurvatureMatrix g p) hc
    (realGeodesicJacobiMatrix_zero g p) (realGeodesicJacobiMatrix_hasDerivAt_initial g p)
    (realGeodesicJacobiMatrixDeriv_continuousAt_zero g p) (realGeodesicJacobiMatrixDeriv_zero g p)
    (fun t _ => realGeodesicJacobiMatrix_hasDerivAt g p t)
    (fun t _ => realGeodesicJacobiMatrixDeriv_hasDerivAt_matrix g p t)
    hdet (fun t _ => realGeodesicCurvatureMatrix_isSymm g p t)
    (fun _ _ => neg_add_cancel _) (fun t _ => realGeodesicCurvatureMatrix_trace_nonneg g hK hR p t)
  simpa only [hd] using h

end Yau.LeafProofs.L12Aux
