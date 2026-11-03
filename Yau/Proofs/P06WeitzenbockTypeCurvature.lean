import Yau.Proofs.P06WeitzenbockTypeConnection

noncomputable section
open scoped Matrix Manifold Topology ContDiff
namespace Yau.NodeProofs.P06Weitzenbock
open Yau Yau.LeafProofs G04Aux L23Aux L12Aux
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {M : ComplexManifold n}

def curvatureCrossAction (h : HermitianField M) (c : M.Carrier) (z : ComplexVector n)
    (K : Matrix (RIdx n) (RIdx n) ℝ) : Matrix (RIdx n) (RIdx n) ℝ :=
  fun d e => Matrix.trace (curvatureMatrix h c z d e * (realMetricFn h c z)⁻¹ * K)

def curvatureTwoMatrix (h : HermitianField M) (A : RealForm M 2) (c : M.Carrier)
    (z : ComplexVector n) : Matrix (RIdx n) (RIdx n) ℝ :=
  fun d e => curvatureTwoComponents h A c z ![d,e]

theorem curvatureTwoMatrix_formula (h : HermitianField M) (hs : MetricSmooth h)
    (A : RealForm M 2) (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c) :
    curvatureTwoMatrix h A c z =
      realRicciMatrix h c z * (realMetricFn h c z)⁻¹ * chartFormMatrix A c z +
        chartFormMatrix A c z * (realMetricFn h c z)⁻¹ * realRicciMatrix h c z +
        curvatureCrossAction h c z (chartFormMatrix A c z) := by
  ext d e
  exact curvatureTwo_eq_ricci_matrix h hs A c hz d e

theorem curvatureCrossAction_jPullback_input (h : HermitianField M) (hs : MetricSmooth h)
    (hk : KahlerClosed h) (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (K : Matrix (RIdx n) (RIdx n) ℝ) :
    curvatureCrossAction h c z ((jMatrix n)ᵀ * K * jMatrix n) = curvatureCrossAction h c z K := by
  ext d e
  let J := jMatrix n
  let R := curvatureMatrix h c z d e
  let H := (realMetricFn h c z)⁻¹
  have hRJ : J * R = R * J := (G01Aux.curvatureMatrix_commute_jMatrix h hs hk c z hz d e).eq.symm
  have hHJ : J * H * Jᵀ = H := inverseMetric_J_orthogonal h c hz
  change Matrix.trace (R * H * (Jᵀ * K * J)) = Matrix.trace (R * H * K)
  calc
    _ = Matrix.trace ((R * H * Jᵀ * K) * J) := by congr 1; noncomm_ring
    _ = Matrix.trace (J * (R * H * Jᵀ * K)) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace (R * (J * H * Jᵀ) * K) := by
      congr 1
      calc
        _ = (J * R) * H * Jᵀ * K := by noncomm_ring
        _ = _ := by rw [hRJ]; noncomm_ring
    _ = _ := by rw [hHJ]

theorem curvatureCrossAction_jPullback_output (h : HermitianField M) (hs : MetricSmooth h)
    (hk : KahlerClosed h) (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (K : Matrix (RIdx n) (RIdx n) ℝ) :
    (jMatrix n)ᵀ * curvatureCrossAction h c z K * jMatrix n = curvatureCrossAction h c z K := by
  ext d e
  rw [jMatrix_conjugation_apply]
  have he := congrArg (fun T : Matrix (RIdx n) (RIdx n) ℝ =>
    Matrix.trace (T * (realMetricFn h c z)⁻¹ * K))
      (G01Aux.curvatureMatrix_jIndex_first h hs hk c z hz d e)
  simpa only [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, curvatureCrossAction] using he

theorem ricci_inverse_J_commute (h : HermitianField M) (hs : MetricSmooth h)
    (hk : KahlerClosed h) (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c) :
    jMatrix n * realRicciMatrix h c z = realRicciMatrix h c z * jMatrix n ∧
      jMatrix n * (realMetricFn h c z)⁻¹ = (realMetricFn h c z)⁻¹ * jMatrix n := by
  constructor
  · rw [G01Aux.realRicciMatrix_eq_realification h hs hk c z hz, G01Aux.hermitianRealification_eq]
    simp only [Matrix.mul_smul, Matrix.smul_mul, rawReal_commute_J]
  · rw [G01Aux.realMetricFn_inverse_eq h c z hz]
    simp only [Matrix.mul_smul, Matrix.smul_mul, rawReal_commute_J]

theorem ricciAction_jConjugate (T H K : Matrix (RIdx n) (RIdx n) ℝ)
    (hT : jMatrix n * T = T * jMatrix n) (hH : jMatrix n * H = H * jMatrix n) :
    T * H * ((jMatrix n)ᵀ * K * jMatrix n) + ((jMatrix n)ᵀ * K * jMatrix n) * H * T =
      (jMatrix n)ᵀ * (T * H * K + K * H * T) * jMatrix n := by
  let J := jMatrix n
  have hX : T * H * Jᵀ = Jᵀ * (T * H) := by
    rw [show Jᵀ = -J from jMatrix_transpose n]
    simp only [Matrix.mul_neg, Matrix.neg_mul]
    congr 1
    calc
      _ = T * (H * J) := by noncomm_ring
      _ = T * (J * H) := by rw [← hH]
      _ = (T * J) * H := by noncomm_ring
      _ = _ := by rw [← hT]; noncomm_ring
  have hY : J * (H * T) = (H * T) * J := by
    calc
      _ = (J * H) * T := by noncomm_ring
      _ = H * J * T := by rw [hH]
      _ = H * (J * T) := by noncomm_ring
      _ = _ := by rw [hT]; noncomm_ring
  change T * H * (Jᵀ * K * J) + (Jᵀ * K * J) * H * T = _
  calc
    _ = (T * H * Jᵀ) * K * J + Jᵀ * K * (J * (H * T)) := by noncomm_ring
    _ = _ := by rw [hX, hY]; noncomm_ring

theorem curvatureTwoMatrix_jPullback (h : HermitianField M) (hs : MetricSmooth h)
    (hk : KahlerClosed h) (A : RealForm M 2) (c : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget c) :
    curvatureTwoMatrix h (jPullbackRealForm A) c z =
      (jMatrix n)ᵀ * curvatureTwoMatrix h A c z * jMatrix n := by
  obtain ⟨hT, hH⟩ := ricci_inverse_J_commute h hs hk c hz
  rw [curvatureTwoMatrix_formula h hs _ c hz, curvatureTwoMatrix_formula h hs A c hz,
    chartFormMatrix_jPullback, ricciAction_jConjugate _ _ _ hT hH,
    curvatureCrossAction_jPullback_input h hs hk c hz]
  simp only [Matrix.mul_add, Matrix.add_mul]
  rw [curvatureCrossAction_jPullback_output h hs hk c hz]

end Yau.NodeProofs.P06Weitzenbock
