import Yau.Proofs.G01KahlerClosure
import Yau.LeafProofs.L23CurvatureCalculus

noncomputable section
open Filter
open scoped Manifold Topology ContDiff Matrix
namespace Yau.NodeProofs.G01Aux
open Yau Yau.LeafProofs L12Aux
variable {n : ℕ} {M : ComplexManifold n}

/-- Actual coefficient smoothness gives pointwise differentiability on its chart target. -/
theorem realMetricFn_differentiableAt (h : HermitianField M) (hs : MetricSmooth h)
    (x : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget x) (a b : RIdx n) :
    DifferentiableAt ℝ (fun w => realMetricFn h x w a b) z :=
  ((hs x a b).contDiffAt
    ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt (by simp)

theorem kahler_metric_derivative_identity_on {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (hs : MetricSmooth h) (hk : KahlerClosed h) (x : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget x) (a b d : RIdx n) :
    -rDeriv (fun w => realMetricFn h x w b d) z a +
      jSign b * jSign d * rDeriv
        (fun w => realMetricFn h x w (jIndex n d) a) z (jIndex n b) +
      rDeriv (fun w => realMetricFn h x w a b) z d = 0 := by
  have hk := kahlerClosed_in_chart h hs hk x hz a (jIndex n b) d
  have h1 : (fun w => kahlerFormFn h x w (jIndex n b) d) =
      (fun w => (-jSign b) * realMetricFn h x w b d) := by
    funext w
    exact kahlerFormFn_jIndex_left h x w b d
  have h2 : (fun w => kahlerFormFn h x w d a) =
      (fun w => jSign d * realMetricFn h x w (jIndex n d) a) := by
    funext w
    exact kahlerFormFn_eq_jIndex_metric h x w d a
  have h3 : (fun w => kahlerFormFn h x w a (jIndex n b)) =
      (fun w => jSign b * realMetricFn h x w a b) := by
    funext w
    exact kahlerFormFn_jIndex_right h x w a b
  change rDeriv _ z a + rDeriv _ z (jIndex n b) +
    rDeriv _ z d = 0 at hk
  have hG (p q : RIdx n) :
      DifferentiableAt ℝ (fun w => realMetricFn h x w p q) z :=
    realMetricFn_differentiableAt h hs x hz p q
  rw [h1, h2, h3,
    rDeriv_const_mul (hG b d) (-jSign b) a,
    rDeriv_const_mul (hG (jIndex n d) a) (jSign d) (jIndex n b),
    rDeriv_const_mul (hG a b) (jSign b) d] at hk
  by_cases hb : b.2 = 0
  · simp only [jSign, hb, ↓reduceIte] at hk ⊢
    linarith
  · simp only [jSign, hb, ↓reduceIte] at hk ⊢
    linarith

theorem christoffel_metric_jIndex {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (hs : MetricSmooth h) (hk : KahlerClosed h) (x : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ chartTarget x) (a b c : RIdx n) :
    jSign b * (∑ d, christoffel h x z d a (jIndex n b) * realMetricFn h x z d c) +
      jSign c * (∑ d, christoffel h x z d a b * realMetricFn h x z d (jIndex n c)) = 0 := by
  rw [L23Aux.christoffel_metric_contraction h hs x z hz a (jIndex n b) c,
    L23Aux.christoffel_metric_contraction h hs x z hz a b (jIndex n c)]
  have h1 := kahler_metric_derivative_identity_on h hs hk x hz a (jIndex n b) c
  have h2 := kahler_metric_derivative_identity_on h hs hk x hz a b (jIndex n c)
  simp only [jIndex_involutive, jSign_jIndex] at h1 h2
  rw [rDeriv_realMetricFn_symm h x z b (jIndex n c) a] at h1
  rw [rDeriv_realMetricFn_symm h x z (jIndex n b) c a] at h2
  rcases b with ⟨bi, b⟩
  rcases c with ⟨ci, c⟩
  fin_cases b <;> fin_cases c <;> norm_num [jSign] at h1 h2 ⊢ <;> linarith

theorem christoffel_jIndex {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (hs : MetricSmooth h) (hk : KahlerClosed h) (x : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ chartTarget x) (a b c : RIdx n) :
    jSign b * christoffel h x z c a (jIndex n b) =
      jSign (jIndex n c) * christoffel h x z (jIndex n c) a b := by
  let G := realMetricFn h x z
  let W : RIdx n → ℝ := fun d => jSign b * christoffel h x z d a (jIndex n b) -
    jSign (jIndex n d) * christoffel h x z (jIndex n d) a b
  have hvec : G *ᵥ W = 0 := by
    funext k
    have hk := christoffel_metric_jIndex h hs hk x z hz a b k
    have hswap : jSign k * (∑ d, christoffel h x z d a b * G d (jIndex n k)) =
        -(∑ d, jSign (jIndex n d) * christoffel h x z (jIndex n d) a b * G d k) := by
      calc
        _ = jSign k * (∑ d, christoffel h x z (jIndex n d) a b *
            G (jIndex n d) (jIndex n k)) := by
          exact congrArg (fun t : ℝ => jSign k * t)
            ((jIndex n).sum_comp (fun d => christoffel h x z d a b * G d (jIndex n k))).symm
        _ = ∑ d, jSign d * christoffel h x z (jIndex n d) a b * G d k := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro d _
          rw [show G (jIndex n d) (jIndex n k) = jSign d * jSign k * G d k from
            realMetricFn_jIndex h x z d k]
          calc
            _ = (jSign k * jSign k) * (jSign d * christoffel h x z (jIndex n d) a b * G d k) := by ring
            _ = _ := by rw [jSign_sq]; ring
        _ = _ := by simp only [jSign_jIndex, neg_mul, Finset.sum_neg_distrib, neg_neg]
    change jSign b * (∑ d, christoffel h x z d a (jIndex n b) * G d k) +
      jSign k * (∑ d, christoffel h x z d a b * G d (jIndex n k)) = 0 at hk
    rw [hswap] at hk
    change (∑ d, G k d * W d) = 0
    calc
      _ = jSign b * (∑ d, christoffel h x z d a (jIndex n b) * G d k) -
          (∑ d, jSign (jIndex n d) * christoffel h x z (jIndex n d) a b * G d k) := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro d _
        rw [show G k d = G d k from realMetricFn_symm h x z k d]
        dsimp [W]
        ring
      _ = 0 := by linarith
  have hinv : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul G
    (isUnit_iff_ne_zero.mpr (realMetricFn_posDef h x z hz).det_pos.ne')
  have hW : W = 0 := by
    calc
      W = G⁻¹ *ᵥ (G *ᵥ W) := by rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
      _ = 0 := by rw [hvec, Matrix.mulVec_zero]
  have hc := congrFun hW c
  change jSign b * christoffel h x z c a (jIndex n b) -
    jSign (jIndex n c) * christoffel h x z (jIndex n c) a b = 0 at hc
  exact sub_eq_zero.mp hc

theorem connectionMatrix_commute_jMatrix (h : HermitianField M) (hs : MetricSmooth h) (hk : KahlerClosed h) (x : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ chartTarget x) (a : RIdx n) :
    Commute (connectionMatrix h x z a) (jMatrix n) := by
  ext c b
  rw [mul_jMatrix, jMatrix_mul]
  exact christoffel_jIndex h hs hk x z hz a b c

theorem rDeriv_christoffel_jIndex (h : HermitianField M) (hs : MetricSmooth h) (hk : KahlerClosed h) (x : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ chartTarget x) (d a b c : RIdx n) :
    jSign b * rDeriv (fun w => christoffel h x w c a (jIndex n b)) z d =
      jSign (jIndex n c) * rDeriv (fun w => christoffel h x w (jIndex n c) a b) z d := by
  have hdiff (l i j : RIdx n) : DifferentiableAt ℝ (fun w => christoffel h x w l i j) z :=
    ((L23Aux.christoffel_contDiffOn h hs x l i j).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt (by simp)
  rw [← rDeriv_const_mul (hdiff c a (jIndex n b)) (jSign b) d,
    ← rDeriv_const_mul (hdiff (jIndex n c) a b) (jSign (jIndex n c)) d]
  have heq : (fun w => jSign b * christoffel h x w c a (jIndex n b)) =ᶠ[𝓝 z]
      (fun w => jSign (jIndex n c) * christoffel h x w (jIndex n c) a b) := by
    filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz] with w hw
    exact christoffel_jIndex h hs hk x w hw a b c
  exact congrArg (fun L => L (realVec d)) (heq.fderiv_eq (𝕜 := ℝ))

theorem connectionDerivativeMatrix_commute_jMatrix (h : HermitianField M) (hs : MetricSmooth h) (hk : KahlerClosed h)
    (x : M.Carrier) (z : ComplexVector n) (hz : z ∈ chartTarget x) (d a : RIdx n) :
    Commute (connectionDerivativeMatrix h x z d a) (jMatrix n) := by
  ext c b
  rw [mul_jMatrix, jMatrix_mul]
  exact rDeriv_christoffel_jIndex h hs hk x z hz d a b c

theorem curvatureMatrix_commute_jMatrix (h : HermitianField M) (hs : MetricSmooth h) (hk : KahlerClosed h)
    (x : M.Carrier) (z : ComplexVector n) (hz : z ∈ chartTarget x) (a b : RIdx n) :
    Commute (curvatureMatrix h x z a b) (jMatrix n) := by
  rw [curvatureMatrix_eq]
  have hDa := (connectionDerivativeMatrix_commute_jMatrix h hs hk x z hz a b).symm
  have hDb := (connectionDerivativeMatrix_commute_jMatrix h hs hk x z hz b a).symm
  have hA := (connectionMatrix_commute_jMatrix h hs hk x z hz a).symm
  have hB := (connectionMatrix_commute_jMatrix h hs hk x z hz b).symm
  exact ((hDa.sub_right hDb).add_right (hA.mul_right hB) |>.sub_right (hB.mul_right hA)).symm

theorem connectionMatrix_jIndex_direction (h : HermitianField M) (hs : MetricSmooth h) (hk : KahlerClosed h)
    (x : M.Carrier) (z : ComplexVector n) (hz : z ∈ chartTarget x) (b : RIdx n) :
    jSign b • connectionMatrix h x z (jIndex n b) = jMatrix n * connectionMatrix h x z b := by
  ext c d
  rw [jMatrix_mul]
  change jSign b * christoffel h x z c (jIndex n b) d =
    jSign (jIndex n c) * christoffel h x z (jIndex n c) b d
  rw [christoffel_symm_lower h x z c (jIndex n b) d,
    christoffel_jIndex h hs hk x z hz d b c,
    christoffel_symm_lower h x z (jIndex n c) d b]

end Yau.NodeProofs.G01Aux
