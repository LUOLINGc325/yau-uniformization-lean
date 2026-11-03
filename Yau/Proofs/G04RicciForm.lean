import Yau.Proofs.G04LocalLeviForm
import Yau.LeafProofs.L17RicciNaturality
import Yau.Blueprint.NormalizationTargets

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter
namespace Yau.NodeProofs.G04Aux
open Yau Yau.Blueprint Yau.LeafProofs
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {M : ComplexManifold n}

theorem matrixPairing_eq_dot (A : Matrix (Fin n) (Fin n) ℂ) (u v : ComplexVector n) :
    matrixPairing A u v = star (WithLp.ofLp u) ⬝ᵥ (A *ᵥ WithLp.ofLp v) := by
  simp [matrixPairing, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem matrixPairing_congruence (A : Matrix (Fin n) (Fin n) ℂ)
    (L : ComplexVector n →L[ℂ] ComplexVector n) (u v : ComplexVector n) :
    matrixPairing ((L17Aux.linearMatrix L)ᴴ * A * L17Aux.linearMatrix L) u v =
      matrixPairing A (L u) (L v) := by
  rw [matrixPairing_eq_dot, matrixPairing_eq_dot]
  conv_lhs => rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
  rw [← Matrix.star_mulVec, L17Aux.linearMatrix_mulVec, L17Aux.linearMatrix_mulVec]

def inverseChart (x : M.Carrier) : OpenPartialHomeomorph (ComplexVector n) M.Carrier :=
  (chartAt (ComplexVector n) x).symm

theorem inverseChart_apply (x : M.Carrier) (z : ComplexVector n) : inverseChart x z = chartInv x z := rfl

theorem inverseChart_source (x : M.Carrier) : (inverseChart x).source = chartTarget x := by
  simp [inverseChart, chartTarget, extChartAt_target, ModelWithCorners.range_eq_univ]

theorem inverseChart_differentiable (x : M.Carrier) :
    MDifferentiableOn (ComplexModel n) (ComplexModel n) (inverseChart x) (inverseChart x).source :=
  (mdifferentiable_chart (I := ComplexModel n) x).2

theorem inverseChart_inverse_differentiable (x : M.Carrier) :
    MDifferentiableOn (ComplexModel n) (ComplexModel n) (inverseChart x).symm (inverseChart x).target :=
  (mdifferentiable_chart (I := ComplexModel n) x).1

theorem chartVec_inverseChart (x : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget x)
    (u : ComplexVector n) :
    chartVec x (chartInv x z) u = mfderiv (ComplexModel n) (ComplexModel n) (inverseChart x) z u := by
  have hp : chartPt x (chartInv x z) = z := (extChartAt (ComplexModel n) x).right_inv hz
  unfold chartVec
  rw [hp]
  rfl

theorem pullbackMatrix_inverseChart (h : HermitianField M) (x : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget x) :
    L17Aux.pullbackMatrix h (inverseChart x) z = hMat h x z := by
  ext a b
  unfold L17Aux.pullbackMatrix LeafCandidates.pullbackCoefficient hMat
  rw [inverseChart_apply, chartVec_inverseChart x hz, chartVec_inverseChart x hz]
  rfl

theorem ricci_chart_congruence (h : HermitianField M) (hs : MetricSmooth h)
    (x : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget x) :
    ricciInChart h x z = (L17Aux.linearMatrix (L17Aux.coordinateDifferential (inverseChart x) (chartInv x z) z))ᴴ *
      ricci h (chartInv x z) * L17Aux.linearMatrix (L17Aux.coordinateDifferential (inverseChart x) (chartInv x z) z) := by
  have heq : (fun w => Real.log (L17Aux.pullbackMatrix h (inverseChart x) w).det.re) =ᶠ[𝓝 z] logDet h x := by
    filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz] with w hw
    rw [pullbackMatrix_inverseChart h x hw]
    rfl
  have hze : z ∈ (inverseChart x).source := by rw [inverseChart_source]; exact hz
  have he := L17Aux.pullbackRicci_eq_ricci h hs (inverseChart x)
    (inverseChart_differentiable x) (inverseChart_inverse_differentiable x) hze
  rw [L17Aux.pullbackRicci, L22Aux.leviC_congr_of_eventuallyEq heq, inverseChart_apply] at he
  exact he

theorem ricci_hermitian (h : HermitianField M) (hs : MetricSmooth h) (x : M.Carrier) :
    (ricci h x).IsHermitian := by
  apply Matrix.IsHermitian.neg
  exact L22Aux.leviC_isHermitian (((L17Aux.logDet_contDiffOn_of_metricSmooth h hs x).contDiffAt
    ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds (mem_extChartAt_target x))).of_le (by simp))

def rhoForm (h : HermitianField M) (hs : MetricSmooth h) : RealForm M 2 :=
  iotaRealForm (ricci h) (ricci_hermitian h hs)

theorem iotaRealForm_apply (A : M.Carrier → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ x, (A x).IsHermitian) (x : M.Carrier) (u v : TangentVector M x) :
    iotaRealForm A hA x ![u,v] =
      2 * (matrixPairing (A x) (tangentCoords x x u) (tangentCoords x x v)).im := rfl

theorem rhoForm_components (h : HermitianField M) (hs : MetricSmooth h)
    (x : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget x) (I : Fin 2 → RIdx n) :
    formComponents (rhoForm h hs) x z I =
      2 * (matrixPairing (ricciInChart h x z) (realVec (I 0)) (realVec (I 1))).im := by
  rw [ricci_chart_congruence h hs x hz, matrixPairing_congruence]
  have hv : (fun r => chartVec x (chartInv x z) (realVec (I r))) =
      ![chartVec x (chartInv x z) (realVec (I 0)), chartVec x (chartInv x z) (realVec (I 1))] := by
    funext r
    fin_cases r <;> rfl
  unfold formComponents rhoForm
  rw [hv, iotaRealForm_apply]
  simp only [L17Aux.coordinateDifferential_apply, inverseChart_apply, chartVec_inverseChart x hz]

theorem matrixPairing_neg (A : Matrix (Fin n) (Fin n) ℂ) (u v : ComplexVector n) :
    matrixPairing (-A) u v = -matrixPairing A u v := by
  simp [matrixPairing, Finset.sum_neg_distrib]

theorem rhoForm_smooth (h : HermitianField M) (hs : MetricSmooth h) : SmoothRealForm (rhoForm h hs) := by
  intro x I
  apply (localLevi_coeff_smooth (logDet h x) (isOpen_extChartAt_target (I := ComplexModel n) x)
    (L17Aux.logDet_contDiffOn_of_metricSmooth h hs x) I).neg.congr
  intro z hz
  rw [rhoForm_components h hs x hz, ricciInChart, matrixPairing_neg, Complex.neg_im]
  ring

theorem rhoForm_closed (h : HermitianField M) (hs : MetricSmooth h) : ClosedRealForm (rhoForm h hs) := by
  intro x z hz I
  let F : FormComponents n 2 := fun w J => 2 * (matrixPairing (leviC (logDet h x) w)
    (realVec (J 0)) (realVec (J 1))).im
  have hF (J : Fin 2 → RIdx n) : ContDiffOn ℝ ∞ (fun w => F w J) (chartTarget x) :=
    localLevi_coeff_smooth (logDet h x) (isOpen_extChartAt_target (I := ComplexModel n) x)
      (L17Aux.logDet_contDiffOn_of_metricSmooth h hs x) J
  have heq : formComponents (rhoForm h hs) x =ᶠ[𝓝 z] (-1 : ℝ) • F := by
    filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz] with w hw
    funext J
    rw [rhoForm_components h hs x hw, ricciInChart, matrixPairing_neg, Complex.neg_im]
    simp only [Pi.smul_apply, smul_eq_mul, F]
    ring
  rw [congrFun (L03.exteriorComponents_congr_nhds heq) I,
    L03.exteriorComponents_smul_at (-1) F z (fun J =>
      ((hF J).contDiffAt ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt (by simp))]
  rw [localLevi_coeff_closed (logDet h x) (isOpen_extChartAt_target (I := ComplexModel n) x)
    (L17Aux.logDet_contDiffOn_of_metricSmooth h hs x) hz, mul_zero]

end Yau.NodeProofs.G04Aux
