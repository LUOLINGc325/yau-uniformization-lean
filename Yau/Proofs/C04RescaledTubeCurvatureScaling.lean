import Yau.Proofs.C04RescaledTubeScaling
import Yau.Proofs.G04FlowNormalization

/-! The Levi-Civita connection and Ricci tensor under constant positive
rescaling, and the genuine zeroth curvature norm. -/
noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory Filter
namespace Yau.Proofs.C04RescaledTubeAux
open Yau Blueprint LeafProofs
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {M : ComplexManifold n}

theorem real_inverse_smul (c : ℝ) (hc : 0 < c)
    (H : Matrix (RIdx n) (RIdx n) ℝ) (hH : H.PosDef) :
    (c • H)⁻¹ = c⁻¹ • H⁻¹ := by
  apply Matrix.inv_eq_left_inv
  have hunit : IsUnit H.det := hH.isUnit.map Matrix.detMonoidHom
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    mul_inv_cancel₀ hc.ne', one_smul]
  exact Matrix.nonsing_inv_mul H hunit

theorem christoffel_scale (c : ℝ) (hc : 0 < c) (k : HermitianField M)
    (hk : MetricSmooth k) (x : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget x) (a b d : RIdx n) :
    christoffel (scaleField c hc k) x z a b d = christoffel k x z a b d := by
  have hd (i j : RIdx n) : DifferentiableAt ℝ
      (fun w => realMetricFn k x w i j) z :=
    ((hk x i j).contDiffAt ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt (by simp)
  unfold christoffel
  simp only [realMetricFn_scale]
  rw [real_inverse_smul c hc _ (L12Aux.realMetricFn_posDef k x z hz)]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [L12Aux.rDeriv_const_mul (hd d j), L12Aux.rDeriv_const_mul (hd b j),
    L12Aux.rDeriv_const_mul (hd b d)]
  field_simp [hc.ne']
  <;> ring

theorem riemannCoeff_scale (c : ℝ) (hc : 0 < c) (k : HermitianField M)
    (hk : MetricSmooth k) (x : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget x) (a b d e : RIdx n) :
    riemannCoeff (scaleField c hc k) x z a b d e = riemannCoeff k x z a b d e := by
  have heq (i j l : RIdx n) :
      (fun w => christoffel (scaleField c hc k) x w i j l) =ᶠ[𝓝 z]
        (fun w => christoffel k x w i j l) := by
    filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz] with w hw
    exact christoffel_scale c hc k hk x hw i j l
  unfold riemannCoeff rDeriv
  rw [(heq e b d).fderiv_eq, (heq e a d).fderiv_eq]
  simp_rw [christoffel_scale c hc k hk x hz]

theorem rmTensor_scale (c : ℝ) (hc : 0 < c) (k : HermitianField M)
    (hk : MetricSmooth k) (x : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget x) :
    rmTensor (scaleField c hc k) x z = c • rmTensor k x z := by
  ext v
  simp only [rmTensor, realMetricFn_scale, Matrix.smul_apply, smul_eq_mul,
    riemannCoeff_scale c hc k hk x hz, Pi.smul_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem realRicciCoeff_scale (c : ℝ) (hc : 0 < c) (k : HermitianField M)
    (hk : MetricSmooth k) (x : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget x) (a b : RIdx n) :
    realRicciCoeff (scaleField c hc k) x z a b = realRicciCoeff k x z a b := by
  unfold realRicciCoeff
  simp only [realMetricFn_scale]
  rw [real_inverse_smul c hc _ (L12Aux.realMetricFn_posDef k x z hz)]
  simp only [Matrix.smul_apply, smul_eq_mul, riemannCoeff_scale c hc k hk x hz]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [show (∑ l, c * realMetricFn k x z l j * riemannCoeff k x z i a b l) =
      c * ∑ l, realMetricFn k x z l j * riemannCoeff k x z i a b l by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring]
  field_simp [hc.ne']

theorem curvatureJetNorm_zero_scale (c : ℝ) (hc : 0 < c) (k : HermitianField M)
    (hk : MetricSmooth k) (x : M.Carrier) :
    curvatureJetNorm (scaleField c hc k) 0 x = c⁻¹ * curvatureJetNorm k 0 x := by
  let G := realMetricFn k x (chartPt x x)
  let A := rmTensor k x (chartPt x x)
  have hnorm : covTensorNormSq (c • G) (c • A) = c⁻¹ ^ 2 * covTensorNormSq G A := by
    unfold covTensorNormSq
    rw [real_inverse_smul c hc G
      (L12Aux.realMetricFn_posDef k x _ (mem_extChartAt_target x))]
    simp only [Matrix.smul_apply, Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v hv
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w hw
    field_simp [hc.ne']
    <;> ring
  change Real.sqrt (covTensorNormSq
    (realMetricFn (scaleField c hc k) x (chartPt x x))
    (rmTensor (scaleField c hc k) x (chartPt x x))) = _
  rw [realMetricFn_scale, rmTensor_scale c hc k hk x (z := chartPt x x) (mem_extChartAt_target x),
    hnorm, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (inv_nonneg.2 hc.le)]
  rfl

end Yau.Proofs.C04RescaledTubeAux
