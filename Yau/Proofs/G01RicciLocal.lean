import Yau.Proofs.G01ConnectionJ
import Yau.LeafProofs.L17ChartNaturality

noncomputable section
open Filter
open scoped Manifold Topology ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.G01Aux
open Yau Yau.LeafProofs L12Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem curvature4_jIndex_last (h : HermitianField M) (hs : MetricSmooth h) (hk : KahlerClosed h) (x : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ chartTarget x) (a b c d : RIdx n) :
    jSign c * jSign d * curvature4 h x z a b (jIndex n c) (jIndex n d) =
      curvature4 h x z a b c d := by
  let R := curvatureMatrix h x z a b
  let G := realMetricFn h x z
  have hR : Commute R (jMatrix n) := curvatureMatrix_commute_jMatrix h hs hk x z hz a b
  have hm : (jMatrix n)ᵀ * (Rᵀ * G) * jMatrix n = Rᵀ * G := by
    calc
      _ = (R * jMatrix n)ᵀ * G * jMatrix n := by simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = (jMatrix n * R)ᵀ * G * jMatrix n := by rw [hR.eq]
      _ = Rᵀ * ((jMatrix n)ᵀ * G * jMatrix n) := by simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = Rᵀ * G := by rw [jMatrix_metric_orthogonal h x z]
  have he := congrArg (fun A : Matrix (RIdx n) (RIdx n) ℝ => A c d) hm
  rw [jMatrix_conjugation_apply] at he
  simpa only [curvature4_eq_matrix] using he

theorem curvature4_jIndex_first (h : HermitianField M) (hs : MetricSmooth h) (hk : KahlerClosed h) (x : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ chartTarget x) (a b c d : RIdx n) :
    jSign a * jSign b * curvature4 h x z (jIndex n a) (jIndex n b) c d =
      curvature4 h x z a b c d := by
  rw [L23Aux.curvature4_pair_swap h hs x z hz (jIndex n a) (jIndex n b) c d,
    L23Aux.curvature4_pair_swap h hs x z hz a b c d]
  exact curvature4_jIndex_last h hs hk x z hz c d a b

theorem curvatureMatrix_jIndex_first (h : HermitianField M) (hs : MetricSmooth h) (hk : KahlerClosed h) (x : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ chartTarget x) (a b : RIdx n) :
    (jSign a * jSign b) • curvatureMatrix h x z (jIndex n a) (jIndex n b) =
      curvatureMatrix h x z a b := by
  let G := realMetricFn h x z
  have hlow : ((jSign a * jSign b) • (curvatureMatrix h x z (jIndex n a) (jIndex n b))ᵀ) * G =
      (curvatureMatrix h x z a b)ᵀ * G := by
    ext c d
    rw [Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
    simpa only [curvature4_eq_matrix, G] using curvature4_jIndex_first h hs hk x z hz a b c d
  have he := congrArg (fun A : Matrix (RIdx n) (RIdx n) ℝ => A * G⁻¹) hlow
  have hGG : G * G⁻¹ = 1 := Matrix.mul_nonsing_inv G
    (isUnit_iff_ne_zero.mpr (realMetricFn_posDef h x z hz).det_pos.ne')
  rw [Matrix.mul_assoc, Matrix.mul_assoc, hGG, Matrix.mul_one, Matrix.mul_one] at he
  have ht := congrArg Matrix.transpose he
  simpa only [Matrix.transpose_smul, Matrix.transpose_transpose] using ht

theorem riemannCoeff_jIndex_first (h : HermitianField M) (hs : MetricSmooth h) (hk : KahlerClosed h) (x : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ chartTarget x) (a b c l : RIdx n) :
    riemannCoeff h x z (jIndex n a) (jIndex n b) c l =
      jSign a * jSign b * riemannCoeff h x z a b c l := by
  have he := congrArg (fun A : Matrix (RIdx n) (RIdx n) ℝ => A l c)
    (curvatureMatrix_jIndex_first h hs hk x z hz a b)
  change (jSign a * jSign b) * riemannCoeff h x z (jIndex n a) (jIndex n b) c l =
    riemannCoeff h x z a b c l at he
  calc
    _ = (jSign a * jSign a) * (jSign b * jSign b) *
      riemannCoeff h x z (jIndex n a) (jIndex n b) c l := by rw [jSign_sq, jSign_sq]; ring
    _ = (jSign a * jSign b) * ((jSign a * jSign b) *
      riemannCoeff h x z (jIndex n a) (jIndex n b) c l) := by ring
    _ = _ := by rw [he]

theorem riemannCoeff_jIndex_last (h : HermitianField M) (hs : MetricSmooth h) (hk : KahlerClosed h) (x : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ chartTarget x) (a b c l : RIdx n) :
    riemannCoeff h x z a b (jIndex n c) (jIndex n l) =
      jSign l * jSign c * riemannCoeff h x z a b c l := by
  have he := congrArg (fun A : Matrix (RIdx n) (RIdx n) ℝ => A (jIndex n l) c)
    (curvatureMatrix_commute_jMatrix h hs hk x z hz a b).eq
  rw [mul_jMatrix, jMatrix_mul, jIndex_involutive] at he
  change jSign c * riemannCoeff h x z a b (jIndex n c) (jIndex n l) =
    jSign l * riemannCoeff h x z a b c l at he
  calc
    _ = (jSign c * jSign c) * riemannCoeff h x z a b (jIndex n c) (jIndex n l) := by rw [jSign_sq]; ring
    _ = jSign c * (jSign c * riemannCoeff h x z a b (jIndex n c) (jIndex n l)) := by ring
    _ = _ := by rw [he]; ring

theorem realRicciMatrix_eq_jTrace (h : HermitianField M) (hs : MetricSmooth h) (hk : KahlerClosed h) (x : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ chartTarget x) (b c : RIdx n) :
    jSign c * Matrix.trace (jMatrix n * curvatureMatrix h x z b (jIndex n c)) =
      2 * realRicciMatrix h x z b c := by
  let S1 := ∑ a, jSign c * jSign (jIndex n a) *
    riemannCoeff h x z (jIndex n c) a b (jIndex n a)
  let S2 := ∑ a, jSign c * jSign (jIndex n a) *
    riemannCoeff h x z a b (jIndex n c) (jIndex n a)
  have hsum : jSign c * Matrix.trace (jMatrix n * curvatureMatrix h x z b (jIndex n c)) +
      S1 + S2 = 0 := by
    simp only [Matrix.trace, Matrix.diag_apply, jMatrix_mul, curvatureMatrix, S1, S2,
      Finset.mul_sum]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro a _
    have hb := riemannCoeff_firstBianchi h x z b (jIndex n c) a (jIndex n a)
    calc
      _ = (jSign c * jSign (jIndex n a)) *
        (riemannCoeff h x z b (jIndex n c) a (jIndex n a) +
          riemannCoeff h x z (jIndex n c) a b (jIndex n a) +
          riemannCoeff h x z a b (jIndex n c) (jIndex n a)) := by ring
      _ = 0 := by rw [hb, mul_zero]
  have hS2 : S2 = -realRicciMatrix h x z b c := by
    dsimp [S2, realRicciMatrix]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro a _
    rw [riemannCoeff_jIndex_last h hs hk x z hz a b c a, jSign_jIndex]
    calc
      _ = -(jSign c * jSign c) * (jSign a * jSign a) * riemannCoeff h x z a b c a := by ring
      _ = _ := by rw [jSign_sq, jSign_sq]; ring
  have hS1 : S1 = -realRicciMatrix h x z c b := by
    calc
      S1 = ∑ a, jSign c * jSign (jIndex n (jIndex n a)) *
          riemannCoeff h x z (jIndex n c) (jIndex n a) b (jIndex n (jIndex n a)) :=
        ((jIndex n).sum_comp (fun a => jSign c * jSign (jIndex n a) *
          riemannCoeff h x z (jIndex n c) a b (jIndex n a))).symm
      _ = _ := by
        simp only [jIndex_involutive, realRicciMatrix]
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro a _
        rw [riemannCoeff_swap h x z (jIndex n c) (jIndex n a) b a,
          riemannCoeff_jIndex_first h hs hk x z hz a c b a]
        calc
          _ = -(jSign c * jSign c) * (jSign a * jSign a) * riemannCoeff h x z a c b a := by ring
          _ = _ := by rw [jSign_sq, jSign_sq]; ring
  rw [hS1, hS2, L23Aux.realRicciMatrix_symm h hs x z hz c b] at hsum
  linarith


open scoped ComplexOrder
/- The determinant/logarithm subgraph below is copied from immutable
/tmp/yau-l18-44.lean, SHA256
dddb59386cd1d770fd51350b396d5f1c212aeafe91ef78dfdd0d25f1168fc568.
Original/new names are stated individually.  realBasis_repr is replaced by
realVec_basis_repr, proved from this file's realVec_basis reconstruction;
the realification determinant proofs use this same genuine real basis.
No L09 or L18 import is introduced. -/

theorem connectionTrace_contDiffOn (h : HermitianField M) (hs : MetricSmooth h) (x : M.Carrier) (b : RIdx n) :
    ContDiffOn ℝ ∞ (fun z => connectionTrace h x z b) (chartTarget x) := by
  apply ContDiffOn.sum
  intro i _
  exact L23Aux.christoffel_contDiffOn h hs x i b i

theorem trace_jMatrix_connectionDerivative (h : HermitianField M) (hs : MetricSmooth h) (hk : KahlerClosed h)
    (x : M.Carrier) (z : ComplexVector n) (hz : z ∈ chartTarget x) (a b : RIdx n) :
    Matrix.trace (jMatrix n * connectionDerivativeMatrix h x z a b) =
      jSign b * rDeriv (fun w => connectionTrace h x w (jIndex n b)) z a := by
  have hC (i j : RIdx n) : DifferentiableAt ℝ (fun w => connectionMatrix h x w b i j) z :=
    ((L23Aux.christoffel_contDiffOn h hs x i b j).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt (by simp)
  have hprod := matrix_entries_differentiable_mul (A := fun _ : ComplexVector n => jMatrix n)
    (fun i j => differentiableAt_const (jMatrix n i j)) hC
  have ht := matrixDirectionalDerivative_trace hprod (realVec a)
  rw [matrixDirectionalDerivative_const_mul (jMatrix n) hC] at ht
  have heq : (fun w => Matrix.trace (jMatrix n * connectionMatrix h x w b)) =ᶠ[𝓝 z]
      (fun w => jSign b * connectionTrace h x w (jIndex n b)) := by
    filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz] with w hw
    have he := congrArg Matrix.trace (connectionMatrix_jIndex_direction h hs hk x w hw b)
    rw [Matrix.trace_smul, smul_eq_mul] at he
    exact he.symm
  have hd := congrArg (fun L => L (realVec a)) (heq.fderiv_eq (𝕜 := ℝ))
  have hT := ((connectionTrace_contDiffOn h hs x (jIndex n b)).contDiffAt
    ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt (by simp)
  calc
    _ = fderiv ℝ (fun w => Matrix.trace (jMatrix n * connectionMatrix h x w b)) z (realVec a) := ht.symm
    _ = _ := hd
    _ = _ := rDeriv_const_mul hT (jSign b) a

theorem curvatureMatrix_jTrace_eq (h : HermitianField M) (hs : MetricSmooth h) (hk : KahlerClosed h)
    (x : M.Carrier) (z : ComplexVector n) (hz : z ∈ chartTarget x) (a b : RIdx n) :
    Matrix.trace (jMatrix n * curvatureMatrix h x z a b) =
      jSign b * rDeriv (fun w => connectionTrace h x w (jIndex n b)) z a -
      jSign a * rDeriv (fun w => connectionTrace h x w (jIndex n a)) z b := by
  let A := connectionMatrix h x z a
  let B := connectionMatrix h x z b
  have hcomm : Matrix.trace (jMatrix n * (A * B)) = Matrix.trace (jMatrix n * (B * A)) := by
    calc
      _ = Matrix.trace (A * (jMatrix n * B)) := by
        rw [← Matrix.mul_assoc, ← (connectionMatrix_commute_jMatrix h hs hk x z hz a).eq,
          Matrix.mul_assoc]
      _ = _ := by rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
  rw [curvatureMatrix_eq, mul_sub, mul_add, mul_sub, Matrix.trace_sub, Matrix.trace_add,
    Matrix.trace_sub, trace_jMatrix_connectionDerivative h hs hk x z hz a b,
    trace_jMatrix_connectionDerivative h hs hk x z hz b a]
  change (_ - _ + Matrix.trace (jMatrix n * (A * B))) - Matrix.trace (jMatrix n * (B * A)) = _
  rw [hcomm]
  ring

theorem realRicciMatrix_eq_connectionTrace (h : HermitianField M) (hs : MetricSmooth h) (hk : KahlerClosed h)
    (x : M.Carrier) (z : ComplexVector n) (hz : z ∈ chartTarget x) (b c : RIdx n) :
    2 * realRicciMatrix h x z b c =
      -rDeriv (fun w => connectionTrace h x w c) z b -
        jSign b * jSign c * rDeriv (fun w => connectionTrace h x w (jIndex n b)) z (jIndex n c) := by
  have he := realRicciMatrix_eq_jTrace h hs hk x z hz b c
  rw [curvatureMatrix_jTrace_eq h hs hk x z hz b (jIndex n c),
    jIndex_involutive, jSign_jIndex] at he
  calc
    _ = jSign c * ((-jSign c) * rDeriv (fun w => connectionTrace h x w c) z b -
        jSign b * rDeriv (fun w => connectionTrace h x w (jIndex n b)) z (jIndex n c)) := he.symm
    _ = -(jSign c * jSign c) * rDeriv (fun w => connectionTrace h x w c) z b -
        jSign b * jSign c * rDeriv (fun w => connectionTrace h x w (jIndex n b)) z (jIndex n c) := by ring
    _ = _ := by rw [jSign_sq]; ring


/-- Local log-determinant calculus uses coefficient smoothness alone. -/

theorem rDeriv_log_realMetricFn_det (h : HermitianField M) (hs : MetricSmooth h) (x : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ chartTarget x) (a : RIdx n) :
    rDeriv (fun w => Real.log (realMetricFn h x w).det) z a =
      2 * rDeriv (logDet h x) z a := by
  have heq : (fun w => Real.log (realMetricFn h x w).det) =ᶠ[𝓝 z]
      (fun w => 2 * logDet h x w + 2 * (n : ℝ) * Real.log 2) := by
    filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz] with w hw
    exact log_realMetricFn_det h x w hw
  have hH : DifferentiableAt ℝ (logDet h x) z :=
    ((L17Aux.logDet_contDiffOn_of_metricSmooth h hs x).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt (by simp)
  have he := congrArg (fun L => L (realVec a)) (heq.fderiv_eq (𝕜 := ℝ))
  rw [fderiv_add_const, fderiv_const_mul hH 2] at he
  exact he

theorem rDeriv_log_realMetricFn_det_trace (h : HermitianField M) (hs : MetricSmooth h) (x : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ chartTarget x) (a : RIdx n) :
    rDeriv (fun w => Real.log (realMetricFn h x w).det) z a =
      Matrix.trace ((realMetricFn h x z)⁻¹ *
        matrixDirectionalDerivative (fun w => realMetricFn h x w) z (realVec a)) := by
  have hG (i j : RIdx n) := realMetricFn_differentiableAt h hs x hz i j
  have hdetd : DifferentiableAt ℝ (fun w => (realMetricFn h x w).det) z :=
    ((contDiffOn_matrix_det (hs x)).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt (by simp)
  have hdet : (realMetricFn h x z).det ≠ 0 := (realMetricFn_posDef h x z hz).det_pos.ne'
  have hj := fderiv_matrix_det_trace hG hdet (realVec a)
  simp_rw [fderiv_matrix_row_apply hG] at hj
  unfold rDeriv
  rw [fderiv.log hdetd hdet]
  simp only [smul_apply, smul_eq_mul]
  rw [hj]
  change (realMetricFn h x z).det⁻¹ *
    ((realMetricFn h x z).det * _) = _
  rw [← mul_assoc, inv_mul_cancel₀ hdet, one_mul]
  rfl

theorem connectionTrace_eq_logDet (h : HermitianField M) (hs : MetricSmooth h) (x : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ chartTarget x) (a : RIdx n) :
    connectionTrace h x z a = rDeriv (logDet h x) z a := by
  have ht := christoffel_trace h x z a
  change connectionTrace h x z a = (1 / 2 : ℝ) *
    Matrix.trace ((realMetricFn h x z)⁻¹ *
      matrixDirectionalDerivative (fun w => realMetricFn h x w) z (realVec a)) at ht
  have hlog := rDeriv_log_realMetricFn_det_trace h hs x z hz a
  rw [rDeriv_log_realMetricFn_det h hs x z hz a] at hlog
  linarith

theorem rDeriv_connectionTrace_eq_logDet (h : HermitianField M) (hs : MetricSmooth h) (x : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ chartTarget x) (a b : RIdx n) :
    rDeriv (fun w => connectionTrace h x w b) z a =
      rDeriv (fun w => rDeriv (logDet h x) w b) z a := by
  have heq : (fun w => connectionTrace h x w b) =ᶠ[𝓝 z]
      (fun w => rDeriv (logDet h x) w b) := by
    filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz] with w hw
    exact connectionTrace_eq_logDet h hs x w hw b
  exact congrArg (fun L => L (realVec a)) (heq.fderiv_eq (𝕜 := ℝ))

theorem realRicciMatrix_eq_logDet (h : HermitianField M) (hs : MetricSmooth h) (hk : KahlerClosed h) (x : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ chartTarget x) (b c : RIdx n) :
    2 * realRicciMatrix h x z b c =
      -rDeriv (fun w => rDeriv (logDet h x) w c) z b -
      jSign b * jSign c * rDeriv
        (fun w => rDeriv (logDet h x) w (jIndex n b)) z (jIndex n c) := by
  rw [realRicciMatrix_eq_connectionTrace h hs hk x z hz b c,
    rDeriv_connectionTrace_eq_logDet h hs x z hz b c,
    rDeriv_connectionTrace_eq_logDet h hs x z hz (jIndex n c) (jIndex n b)]

theorem realRicciMatrix_eq_realification (h : HermitianField M) (hs : MetricSmooth h) (hk : KahlerClosed h) (x : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ chartTarget x) :
    realRicciMatrix h x z = hermitianRealification (-leviC (logDet h x) z) := by
  have hf : ContDiffAt ℝ 2 (logDet h x) z :=
    ((L17Aux.logDet_contDiffOn_of_metricSmooth h hs x).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).of_le (by simp)
  have hsymm (u v : ComplexVector n) := hf.isSymmSndFDerivAt (by norm_num) u v
  ext a b
  have hR := realRicciMatrix_eq_logDet h hs hk x z hz a b
  rw [rDeriv_rDeriv_eq_hessian hf, rDeriv_rDeriv_eq_hessian hf] at hR
  have hre (i j : Fin n) := (leviMatrix_entry_re_im hf stdVec i j).1
  have him (i j : Fin n) := (leviMatrix_entry_re_im hf stdVec i j).2
  rcases a with ⟨i, a⟩
  rcases b with ⟨j, b⟩
  fin_cases a <;> fin_cases b <;>
    norm_num [hermitianRealification, leviC, jIndex, jSign, realVec, stdVec] at hR ⊢
  all_goals
    simp only [hre, him]
    dsimp only [stdVec]
    linarith [hsymm (EuclideanSpace.single i 1) (EuclideanSpace.single j 1),
      hsymm (Complex.I • EuclideanSpace.single i 1) (Complex.I • EuclideanSpace.single j 1),
      hsymm (EuclideanSpace.single i 1) (Complex.I • EuclideanSpace.single j 1),
      hsymm (Complex.I • EuclideanSpace.single i 1) (EuclideanSpace.single j 1)]

end Yau.NodeProofs.G01Aux
