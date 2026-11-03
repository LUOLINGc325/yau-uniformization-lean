import Yau.Proofs.P06WeitzenbockTypeConnection

noncomputable section
open Filter
open scoped Matrix Manifold Topology ContDiff
namespace Yau.NodeProofs.P06Weitzenbock
open Yau Yau.LeafProofs G04Aux L23Aux L12Aux
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {M : ComplexManifold n}

def matrixMetricJTrace (H K : Matrix (RIdx n) (RIdx n) ℝ) : ℝ :=
  (1 / 2 : ℝ) * Matrix.trace (H * K * jMatrix n)

theorem matrixMetricJTrace_sub (H K L : Matrix (RIdx n) (RIdx n) ℝ) :
    matrixMetricJTrace H (K - L) = matrixMetricJTrace H K - matrixMetricJTrace H L := by
  simp only [matrixMetricJTrace, Matrix.mul_sub, Matrix.sub_mul, Matrix.trace_sub, mul_sub]

theorem matrixMetricJTrace_smul (H K : Matrix (RIdx n) (RIdx n) ℝ) (r : ℝ) :
    matrixMetricJTrace H (r • K) = r * matrixMetricJTrace H K := by
  simp only [matrixMetricJTrace, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  ring

theorem matrixMetricJTrace_sum {ι : Type*} [Fintype ι]
    (H : Matrix (RIdx n) (RIdx n) ℝ) (K : ι → Matrix (RIdx n) (RIdx n) ℝ) :
    matrixMetricJTrace H (∑ i, K i) = ∑ i, matrixMetricJTrace H (K i) := by
  simp only [matrixMetricJTrace, Matrix.mul_sum, Finset.sum_mul, Matrix.trace_sum, Finset.mul_sum]

theorem matrixMetricJTrace_form (h : HermitianField M) (A : RealForm M 2)
    (h11 : RealOneOne A) (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c) :
    inChart c (formTrace h A) z =
      matrixMetricJTrace (realMetricFn h c z)⁻¹ (chartFormMatrix A c z) := by
  rw [matrixMetricJTrace, symmetric_trace_KJ _ _ (realMetricFn_isSymm h c z).inv]
  exact trace_in_chart h A h11 c hz

/-- Parallelness of the actual inverse metric and complex structure,
including every connection term, for an arbitrary matrix field. -/
theorem matrixMetricJTrace_derivative (h : HermitianField M) (hs : MetricSmooth h)
    (hk : KahlerClosed h) (c : M.Carrier)
    (K : ComplexVector n → Matrix (RIdx n) (RIdx n) ℝ)
    {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (hK : ∀ i j, DifferentiableAt ℝ (fun w => K w i j) z) (a : RIdx n) :
    rDeriv (fun w => matrixMetricJTrace (realMetricFn h c w)⁻¹ (K w)) z a =
      matrixMetricJTrace (realMetricFn h c z)⁻¹ (matrixCovariantDerivative h c K z a) := by
  let H := fun w => (realMetricFn h c w)⁻¹
  let J := jMatrix n
  let Γ := connectionMatrix h c z a
  let T := fun w => H w * K w * J
  have hH (i j : RIdx n) : DifferentiableAt ℝ (fun w => H w i j) z :=
    ((realMetricFn_inverse_contDiffOn h hs c i j).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)).differentiableAt (by simp)
  have hJ (i j : RIdx n) : DifferentiableAt ℝ (fun _ : ComplexVector n => J i j) z :=
    differentiableAt_const _
  have hT := matrix_entries_differentiable_mul (matrix_entries_differentiable_mul hH hK) hJ
  have htr : DifferentiableAt ℝ (fun w => Matrix.trace (T w)) z :=
    DifferentiableAt.fun_sum (fun i _ => hT i i)
  have hzero : matrixDirectionalDerivative (fun _ : ComplexVector n => J) z (realVec a) = 0 := by
    ext i j
    simp [matrixDirectionalDerivative]
  have hcomm : J * Γ = Γ * J :=
    (G01Aux.connectionMatrix_commute_jMatrix h hs hk c z hz a).eq.symm
  have hd : matrixDirectionalDerivative T z (realVec a) + Γ * T z - T z * Γ =
      H z * matrixCovariantDerivative h c K z a * J := by
    dsimp only [T]
    rw [matrixDirectionalDerivative_mul (matrix_entries_differentiable_mul hH hK) hJ,
      matrixDirectionalDerivative_mul hH hK, hzero, Matrix.mul_zero, add_zero,
      inverseMetric_directional_derivative h hs c hz a]
    unfold matrixCovariantDerivative
    change _ + Γ * (H z * K z * J) - H z * K z * J * Γ =
      H z * (matrixDirectionalDerivative K z (realVec a) - Γᵀ * K z - K z * Γ) * J
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.neg_mul, Matrix.mul_neg,
      Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
    rw [hcomm]
    abel
  have ht := congrArg Matrix.trace hd
  simp only [Matrix.trace_add, Matrix.trace_sub] at ht
  rw [Matrix.trace_mul_comm Γ (T z)] at ht
  have htrace : rDeriv (fun w => Matrix.trace (T w)) z a =
      Matrix.trace (H z * matrixCovariantDerivative h c K z a * J) := by
    change fderiv ℝ (fun w => Matrix.trace (T w)) z (realVec a) = _
    rw [matrixDirectionalDerivative_trace hT]
    linarith
  change rDeriv (fun w => (1 / 2 : ℝ) * Matrix.trace (T w)) z a = _
  rw [rDeriv_const_mul htr, htrace]
  rfl

theorem trace_first_covariant (h : HermitianField M) (hs : MetricSmooth h)
    (hk : KahlerClosed h) (A : RealForm M 2) (hA : SmoothRealForm A) (h11 : RealOneOne A)
    (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c) (a : RIdx n) :
    rDeriv (inChart c (formTrace h A)) z a =
      matrixMetricJTrace (realMetricFn h c z)⁻¹ (covariantTwoMatrix h A c z a) := by
  rw [trace_covariant_derivative h hs hk A hA h11 c hz a, matrixMetricJTrace,
    symmetric_trace_KJ _ _ (realMetricFn_isSymm h c z).inv]
  rfl

theorem trace_second_covariant (h : HermitianField M) (hs : MetricSmooth h)
    (hk : KahlerClosed h) (A : RealForm M 2) (hA : SmoothRealForm A) (h11 : RealOneOne A)
    (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c) (a b : RIdx n) :
    matrixMetricJTrace (realMetricFn h c z)⁻¹ (secondTwoMatrix h A c z a b) =
      rDeriv (fun w => rDeriv (inChart c (formTrace h A)) w b) z a -
        ∑ p, christoffel h c z p a b * rDeriv (inChart c (formTrace h A)) z p := by
  have he : (fun w => rDeriv (inChart c (formTrace h A)) w b) =ᶠ[𝓝 z]
      (fun w => matrixMetricJTrace (realMetricFn h c w)⁻¹ (covariantTwoMatrix h A c w b)) := by
    filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz] with w hw
    exact trace_first_covariant h hs hk A hA h11 c hw b
  have hU (d e : RIdx n) : DifferentiableAt ℝ (fun w => covariantTwoMatrix h A c w b d e) z :=
    ((covariantComponents_smooth h hs c (formComponents A c) (hA c) b ![d,e]).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)).differentiableAt (by simp)
  have hder := congrArg (fun L : ComplexVector n →L[ℝ] ℝ => L (realVec a)) he.fderiv_eq
  change rDeriv _ z a = rDeriv _ z a at hder
  rw [matrixMetricJTrace_derivative h hs hk c _ hz hU a] at hder
  rw [secondTwoMatrix_formula, matrixMetricJTrace_sub, matrixMetricJTrace_sum]
  simp_rw [matrixMetricJTrace_smul, ← trace_first_covariant h hs hk A hA h11 c hz]
  rw [hder]

theorem trace_rough_eq_scalarHodge (h : HermitianField M) (hs : MetricSmooth h)
    (hk : KahlerClosed h) (A : RealForm M 2) (hA : SmoothRealForm A) (h11 : RealOneOne A)
    (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c) :
    matrixMetricJTrace (realMetricFn h c z)⁻¹ (roughTwoMatrix h A c z) =
      hodgeComponents h c 0 (formComponents (scalarForm (formTrace h A)) c) z Fin.elim0 := by
  have hd : exteriorComponents (formComponents (scalarForm (formTrace h A)) c) =
      fun z I => rDeriv (inChart c (formTrace h A)) z (I 0) := by
    funext w I
    simp [exteriorComponents, scalarForm_components, Fin.sum_univ_succ]
  rw [roughTwoMatrix_formula]
  have hn (H K : Matrix (RIdx n) (RIdx n) ℝ) : matrixMetricJTrace H (-K) = -matrixMetricJTrace H K := by
    simp [matrixMetricJTrace]
  rw [hn, matrixMetricJTrace_sum]
  simp_rw [matrixMetricJTrace_sum, matrixMetricJTrace_smul,
    trace_second_covariant h hs hk A hA h11 c hz]
  rw [hodgeComponents, hd]
  simp [codifferentialComponents, covariantComponents, Fin.sum_univ_succ]

end Yau.NodeProofs.P06Weitzenbock
