import Yau.Proofs.P06WeitzenbockType

noncomputable section
open scoped Matrix Manifold Topology ContDiff
namespace Yau.NodeProofs.P06Weitzenbock
open Yau Yau.LeafProofs G04Aux L23Aux L12Aux
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {M : ComplexManifold n}

theorem chartFormMatrix_jPullback (A : RealForm M 2) (c : M.Carrier) (z : ComplexVector n) :
    chartFormMatrix (jPullbackRealForm A) c z =
      (jMatrix n)ᵀ * chartFormMatrix A c z * jMatrix n := by
  ext a b
  rw [chartFormMatrix, jPullbackRealForm_components]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [formComponents_degree_two, jMatrix_conjugation_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]

theorem chartFormMatrix_center (A : RealForm M 2) (x : M.Carrier) :
    chartFormMatrix A x (chartPt x x) = realFormMatrix A x := by
  ext a b
  exact formComponents_center_pair A x ![a,b]

theorem realFormMatrix_jPullback (A : RealForm M 2) (x : M.Carrier) :
    realFormMatrix (jPullbackRealForm A) x =
      (jMatrix n)ᵀ * realFormMatrix A x * jMatrix n := by
  rw [← chartFormMatrix_center, chartFormMatrix_jPullback, chartFormMatrix_center]

theorem inverseMetric_J_orthogonal (h : HermitianField M) (x : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget x) :
    jMatrix n * (realMetricFn h x z)⁻¹ * (jMatrix n)ᵀ = (realMetricFn h x z)⁻¹ := by
  have he : (jMatrix n)ᵀ * (realMetricFn h x z)⁻¹ * jMatrix n = (realMetricFn h x z)⁻¹ := by
    ext a b
    rw [jMatrix_conjugation_apply]
    have hi : (realMetricFn h x z)⁻¹ (jIndex n a) (jIndex n b) =
        jSign a * jSign b * (realMetricFn h x z)⁻¹ a b := by
      simpa only [L18Aux.jIndex, L18Aux.jSign, jIndex, jSign] using
        (L18Aux.realMetricFn_inverse_jIndex h x hz a b)
    rw [hi]
    calc
      _ = (jSign a * jSign a) * (jSign b * jSign b) * (realMetricFn h x z)⁻¹ a b := by ring
      _ = _ := by rw [jSign_sq, jSign_sq]; ring
  calc
    _ = (jMatrix n)ᵀ * (realMetricFn h x z)⁻¹ * jMatrix n := by
      rw [jMatrix_transpose]
      noncomm_ring
    _ = _ := he

theorem formInner_jPullback (h : HermitianField M) (A B : RealForm M 2) (x : M.Carrier) :
    formInner h (jPullbackRealForm A) (jPullbackRealForm B) x = formInner h A B x := by
  rw [formInner_trace, formInner_trace, realFormMatrix_jPullback, realFormMatrix_jPullback]
  congr 1
  let H := (realMetricFn h x (chartPt x x))⁻¹
  let K := realFormMatrix A x
  let L := realFormMatrix B x
  have hJ : jMatrix n * H * (jMatrix n)ᵀ = H :=
    inverseMetric_J_orthogonal h x (mem_extChartAt_target x)
  change Matrix.trace (H * ((jMatrix n)ᵀ * K * jMatrix n) * H *
    ((jMatrix n)ᵀ * L * jMatrix n)) = Matrix.trace (H * K * H * L)
  calc
    _ = Matrix.trace ((H * (jMatrix n)ᵀ * K) *
        (jMatrix n * H * (jMatrix n)ᵀ) * L * jMatrix n) := by congr 1; noncomm_ring
    _ = Matrix.trace ((H * (jMatrix n)ᵀ * K) * H * L * jMatrix n) := by rw [hJ]
    _ = Matrix.trace (jMatrix n * ((H * (jMatrix n)ᵀ * K) * H * L)) :=
      Matrix.trace_mul_comm _ _
    _ = Matrix.trace ((jMatrix n * H * (jMatrix n)ᵀ) * K * H * L) := by congr 1; noncomm_ring
    _ = _ := by rw [hJ]

theorem formInner_jPullback_selfadjoint (h : HermitianField M) (A B : RealForm M 2)
    (x : M.Carrier) : formInner h (jPullbackRealForm A) B x =
      formInner h A (jPullbackRealForm B) x := by
  have he := formInner_jPullback h A (jPullbackRealForm B) x
  rw [jPullbackTwo_involution] at he
  exact he

theorem oneOneProjection_fixed (A : RealForm M 2) (hA : RealOneOne A) : oneOneProjection A = A := by
  have hj : jPullbackRealForm A = A := by
    funext x
    apply ContinuousAlternatingMap.ext
    intro V
    have hv : V = ![V 0,V 1] := by funext i; fin_cases i <;> rfl
    rw [hv, jPullbackRealForm_apply]
    have hI : (fun i : Fin 2 => Complex.I • (![V 0,V 1] i)) =
        ![Complex.I • V 0,Complex.I • V 1] := by funext i; fin_cases i <;> rfl
    rw [hI]
    exact hA x (V 0) (V 1)
  rw [oneOneProjection, hj]
  rw [← two_smul ℝ A, smul_smul]
  norm_num

theorem oneOneProjection_idempotent (A : RealForm M 2) :
    oneOneProjection (oneOneProjection A) = oneOneProjection A :=
  oneOneProjection_fixed _ (oneOneProjection_type A)

theorem formInner_oneOneProjection_selfadjoint (h : HermitianField M)
    (A B : RealForm M 2) (x : M.Carrier) :
    formInner h (oneOneProjection A) B x = formInner h A (oneOneProjection B) x := by
  simp only [oneOneProjection, L03.formInner_smul_left, L03.formInner_smul_right,
    L03.formInner_add_left, L03.formInner_add_right, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [formInner_jPullback_selfadjoint]

theorem formInner_projection_residual (h : HermitianField M) (A : RealForm M 2)
    (x : M.Carrier) : formInner h (oneOneProjection A) (A - oneOneProjection A) x = 0 := by
  rw [L03.formInner_sub_right]
  simp only [Pi.sub_apply]
  rw [formInner_oneOneProjection_selfadjoint h A A x,
    formInner_oneOneProjection_selfadjoint h A (oneOneProjection A) x,
    oneOneProjection_idempotent]
  ring

end Yau.NodeProofs.P06Weitzenbock
