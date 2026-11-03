import Yau.LeafProofs.L19BochnerEnergy

/-! The Bochner formula for the actual coordinate metric, connection and
curvature calculators. -/

noncomputable section

open MeasureTheory Filter
open scoped Topology ContDiff Manifold Matrix ComplexOrder

namespace Yau.LeafProofs.L19Aux

open L18Aux

section Algebra

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem sum_four_exchange_pairs (F : ι → ι → ι → ι → ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l, F i j k l) = ∑ k, ∑ l, ∑ i, ∑ j, F i j k l := by
  calc
    _ = ∑ i, ∑ k, ∑ l, ∑ j, F i j k l := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      exact Finset.sum_comm
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      exact Finset.sum_comm

omit [DecidableEq ι] in
theorem inverseMetric_tensor_trace_derivative_algebra
    (A C H dH : Matrix ι ι ℝ) :
    (∑ i, ∑ j, ((-(C * A + A * Cᵀ)) i j * H i j + A i j * dH i j)) =
      ∑ i, ∑ j, A i j * (dH i j - (∑ p, C p i * H p j) - ∑ p, C p j * H i p) := by
  have hleft : (∑ i, ∑ j, ∑ p, C i p * A p j * H i j) =
      ∑ i, ∑ j, ∑ p, A i j * (C p i * H p j) := by
    rw [Finset.sum_comm]
    calc
      _ = ∑ j, ∑ p, ∑ i, C i p * A p j * H i j := by
        apply Finset.sum_congr rfl
        intro j hj
        exact Finset.sum_comm
      _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr rfl
        intro p hp
        ring
  have hright : (∑ i, ∑ j, ∑ p, A i p * C j p * H i j) =
      ∑ i, ∑ j, ∑ p, A i j * (C p j * H i p) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro p hp
    ring
  simp only [Matrix.neg_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
    neg_mul, add_mul, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_mul, Finset.mul_sum, Finset.sum_neg_distrib]
  rw [hleft, hright]
  ring

theorem bochner_contraction_algebra (A H Ric : Matrix ι ι ℝ) (r d : ι → ℝ)
    (T : ι → ι → ι → ℝ) (hA : A.IsSymm) (hH : H.IsSymm)
    (hTs : ∀ l k i, T l k i = T l i k)
    (hTc : ∀ i, (∑ l, ∑ k, A l k * T l i k) =
      d i + ∑ p, (∑ b, A p b * Ric i b) * r p) :
    (∑ l, ∑ k, A l k * (A.toBilin' (T l k) r + A.toBilin' (H k) (H l))) -
        A.toBilin' r d =
      Matrix.trace (A * H * A * H) + Ric.toBilin' (A *ᵥ r) (A *ᵥ r) := by
  have hR (i : ι) : (∑ p, (∑ b, A p b * Ric i b) * r p) =
      (Ric *ᵥ (A *ᵥ r)) i := by
    simp only [Finset.sum_mul, Matrix.mulVec, dotProduct, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro p hp
    rw [hA.apply b p]
    ring
  have hT : (∑ l, ∑ k, A l k * A.toBilin' (T l k) r) =
      A.toBilin' (d + Ric *ᵥ (A *ᵥ r)) r := by
    calc
      _ = A.toBilin' (fun i => ∑ l, ∑ k, A l k * T l i k) r := by
        simp only [Matrix.toBilin'_apply, Finset.mul_sum, Finset.sum_mul]
        rw [sum_four_exchange_pairs]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr rfl
        intro l hl
        apply Finset.sum_congr rfl
        intro k hk
        rw [hTs l k i]
        ring
      _ = _ := by
        apply congrArg (fun u : ι → ℝ => A.toBilin' u r)
        funext i
        rw [hTc i, hR i]
        rfl
  have hS : (∑ l, ∑ k, A l k * A.toBilin' (H k) (H l)) =
      Matrix.trace (A * H * A * H) := by
    calc
      _ = Matrix.trace (A * (H * A * H)) := by
        simp only [Matrix.toBilin'_apply, Matrix.trace, Matrix.diag_apply,
          Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro l hl
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        rw [hH.apply i l]
      _ = _ := by simp only [Matrix.mul_assoc]
  have hAd : A.toBilin' d r = A.toBilin' r d :=
    (Matrix.isSymm_toBilin'_iff_isSymm.mpr hA).eq _ _
  have hRic : A.toBilin' (Ric *ᵥ (A *ᵥ r)) r =
      Ric.toBilin' (A *ᵥ r) (A *ᵥ r) := by
    simp only [Matrix.toBilin'_apply']
    exact dotProduct_comm _ _
  simp only [mul_add, Finset.sum_add_distrib]
  rw [hT, hS]
  simp only [map_add, LinearMap.add_apply]
  rw [hAd, hRic]
  ring

end Algebra

variable {n : ℕ} {M : ComplexManifold n}

theorem chartRealLaplacian_contDiffOn (g : SmoothMetric M) (a : M.Carrier)
    {f : ComplexVector n → ℝ} (hf : ContDiffOn ℝ ∞ f (chartTarget a)) :
    ContDiffOn ℝ ∞ (chartRealLaplacian g.form a f) (chartTarget a) := by
  apply ContDiffOn.sum
  intro i hi
  apply ContDiffOn.sum
  intro j hj
  exact (realMetricFn_inverse_contDiffOn g a i j).mul
    (chartCovHessian_contDiffOn g a hf i j)

/-- The derivative of the actual metric trace is the metric trace of the
actual covariant third derivative. -/
theorem chartRealLaplacian_derivative (g : SmoothMetric M) (a : M.Carrier)
    {f : ComplexVector n → ℝ} (hf : ContDiffOn ℝ ∞ f (chartTarget a))
    {z : ComplexVector n} (hz : z ∈ chartTarget a) (k : RIdx n) :
    rDeriv (chartRealLaplacian g.form a f) z k =
      ∑ i, ∑ j, (realMetricFn g.form a z)⁻¹ i j * chartCovThird g.form a f z k i j := by
  have hO := isOpen_extChartAt_target (I := ComplexModel n) a
  have hA (i j : RIdx n) : DifferentiableAt ℝ
      (fun w => (realMetricFn g.form a w)⁻¹ i j) z := ((realMetricFn_inverse_contDiffOn g a i j).contDiffAt
    (hO.mem_nhds hz)).differentiableAt (by simp)
  have hH (i j : RIdx n) : DifferentiableAt ℝ
      (fun w => chartCovHessian g.form a f w i j) z := ((chartCovHessian_contDiffOn g a hf i j).contDiffAt
    (hO.mem_nhds hz)).differentiableAt (by simp)
  have hprod (i j : RIdx n) : DifferentiableAt ℝ
      (fun w => (realMetricFn g.form a w)⁻¹ i j * chartCovHessian g.form a f w i j) z :=
    (hA i j).mul (hH i j)
  have hrow (i : RIdx n) : DifferentiableAt ℝ
      (fun w => ∑ j, (realMetricFn g.form a w)⁻¹ i j * chartCovHessian g.form a f w i j) z := by
    simpa only [Finset.sum_fn] using DifferentiableAt.sum (u := Finset.univ)
      (fun j _ => hprod i j)
  unfold chartRealLaplacian
  rw [rDeriv_sum _ hrow]
  conv_lhs => arg 2; ext i; rw [rDeriv_sum _ (fun j => hprod i j)]
  simp_rw [rDeriv_mul (hA _ _) (hH _ _)]
  have hd := inverseMetric_tensor_trace_derivative_algebra
    ((realMetricFn g.form a z)⁻¹) (L12Aux.connectionMatrix g.form a z k)
    (chartCovHessian g.form a f z)
    (fun i j => rDeriv (fun w => chartCovHessian g.form a f w i j) z k)
  have hentry (i j : RIdx n) :
      rDeriv (fun w => (realMetricFn g.form a w)⁻¹ i j) z k =
      (-(L12Aux.connectionMatrix g.form a z k * (realMetricFn g.form a z)⁻¹ +
        (realMetricFn g.form a z)⁻¹ * (L12Aux.connectionMatrix g.form a z k)ᵀ)) i j :=
    congrArg (fun B : Matrix (RIdx n) (RIdx n) ℝ => B i j)
      (inverseMetric_directional_derivative g a hz k)
  simp_rw [hentry]
  exact hd

/-- Contract one slot of the actual Hessian against the actual gradient. -/
def chartHessianGradientPair (h : HermitianField M) (a : M.Carrier)
    (f : ComplexVector n → ℝ) (k : RIdx n) (z : ComplexVector n) : ℝ :=
  ((realMetricFn h a z)⁻¹).toBilin'
    (fun i => chartCovHessian h a f z k i) (fun j => rDeriv f z j)

theorem chartHessianGradientPair_contDiffOn (g : SmoothMetric M) (a : M.Carrier)
    {f : ComplexVector n → ℝ} (hf : ContDiffOn ℝ ∞ f (chartTarget a)) (k : RIdx n) :
    ContDiffOn ℝ ∞ (chartHessianGradientPair g.form a f k) (chartTarget a) := by
  have hO := isOpen_extChartAt_target (I := ComplexModel n) a
  have hs : ContDiffOn ℝ ∞ (fun z => ∑ i, ∑ j,
      chartCovHessian g.form a f z k i * (realMetricFn g.form a z)⁻¹ i j * rDeriv f z j)
      (chartTarget a) := by
    apply ContDiffOn.sum
    intro i hi
    apply ContDiffOn.sum
    intro j hj
    exact ((chartCovHessian_contDiffOn g a hf k i).mul
      (realMetricFn_inverse_contDiffOn g a i j)).mul (rDeriv_contDiffOn hO hf j)
  exact hs.congr (fun z _ => Matrix.toBilin'_apply _ _ _)

theorem chartHessianGradientPair_covDerivative (g : SmoothMetric M) (a : M.Carrier)
    {f : ComplexVector n → ℝ} (hf : ContDiffOn ℝ ∞ f (chartTarget a))
    {z : ComplexVector n} (hz : z ∈ chartTarget a) (l k : RIdx n) :
    rDeriv (chartHessianGradientPair g.form a f k) z l -
        (∑ p, christoffel g.form a z p l k * chartHessianGradientPair g.form a f p z) =
      ((realMetricFn g.form a z)⁻¹).toBilin'
        (fun i => chartCovThird g.form a f z l k i) (fun j => rDeriv f z j) +
      ((realMetricFn g.form a z)⁻¹).toBilin'
        (fun i => chartCovHessian g.form a f z k i)
        (fun j => chartCovHessian g.form a f z l j) := by
  have hO := isOpen_extChartAt_target (I := ComplexModel n) a
  have hraw := rDeriv_matrix_pairing
    (fun w => (realMetricFn g.form a w)⁻¹)
    (fun w i => chartCovHessian g.form a f w k i) (fun w i => rDeriv f w i)
    (fun i j => ((realMetricFn_inverse_contDiffOn g a i j).contDiffAt
      (hO.mem_nhds hz)).differentiableAt (by simp))
    (fun i => ((chartCovHessian_contDiffOn g a hf k i).contDiffAt
      (hO.mem_nhds hz)).differentiableAt (by simp))
    (fun i => ((rDeriv_contDiffOn hO hf i).contDiffAt
      (hO.mem_nhds hz)).differentiableAt (by simp)) l
  rw [inverseMetric_directional_derivative g a hz l,
    inverseMetric_pairing_derivative_algebra] at hraw
  have hdf : ((fun i => rDeriv (fun w => rDeriv f w i) z l) -
      (L12Aux.connectionMatrix g.form a z l)ᵀ *ᵥ (fun i => rDeriv f z i)) =
      (fun i => chartCovHessian g.form a f z l i) := rfl
  have hH : ((fun i => rDeriv (fun w => chartCovHessian g.form a f w k i) z l) -
      (L12Aux.connectionMatrix g.form a z l)ᵀ *ᵥ
        (fun i => chartCovHessian g.form a f z k i)) =
      (fun i => chartCovThird g.form a f z l k i) +
        ∑ p, christoffel g.form a z p l k • (fun i => chartCovHessian g.form a f z p i) := by
    funext i
    simp only [Pi.sub_apply, Pi.add_apply, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, chartCovThird, Matrix.mulVec, dotProduct,
      Matrix.transpose_apply, L12Aux.connectionMatrix]
    ring
  rw [hdf, hH] at hraw
  simp only [map_add, map_sum, map_smul, LinearMap.add_apply,
    LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] at hraw
  change rDeriv (chartHessianGradientPair g.form a f k) z l = _ at hraw
  change _ - (∑ p, christoffel g.form a z p l k *
    ((realMetricFn g.form a z)⁻¹).toBilin'
      (fun i => chartCovHessian g.form a f z p i) (fun j => rDeriv f z j)) = _
  linarith

theorem chartGradientPair_self_covHessian (g : SmoothMetric M) (a : M.Carrier)
    {f : ComplexVector n → ℝ} (hf : ContDiffOn ℝ ∞ f (chartTarget a))
    {z : ComplexVector n} (hz : z ∈ chartTarget a) (l k : RIdx n) :
    chartCovHessian g.form a (chartGradientPair g.form a f f) z l k =
      2 * (((realMetricFn g.form a z)⁻¹).toBilin'
        (fun i => chartCovThird g.form a f z l k i) (fun j => rDeriv f z j) +
      ((realMetricFn g.form a z)⁻¹).toBilin'
        (fun i => chartCovHessian g.form a f z k i)
        (fun j => chartCovHessian g.form a f z l j)) := by
  have hO := isOpen_extChartAt_target (I := ComplexModel n) a
  have heq : (fun w => rDeriv (chartGradientPair g.form a f f) w k) =ᶠ[𝓝 z]
      (fun w => 2 * chartHessianGradientPair g.form a f k w) := by
    filter_upwards [hO.mem_nhds hz] with w hw
    exact chartGradientPair_self_derivative g a hf hw k
  have hdiff := ((chartHessianGradientPair_contDiffOn g a hf k).contDiffAt
    (hO.mem_nhds hz)).differentiableAt (by simp)
  have hd : rDeriv (fun w => rDeriv (chartGradientPair g.form a f f) w k) z l =
      2 * rDeriv (chartHessianGradientPair g.form a f k) z l := by
    unfold rDeriv at heq ⊢
    rw [heq.fderiv_eq, fderiv_const_mul hdiff]
    rfl
  change rDeriv (fun w => rDeriv (chartGradientPair g.form a f f) w k) z l -
      (∑ p, christoffel g.form a z p l k * rDeriv (chartGradientPair g.form a f f) z p) = _
  rw [hd]
  simp_rw [chartGradientPair_self_derivative g a hf hz]
  have hc := chartHessianGradientPair_covDerivative g a hf hz l k
  change rDeriv (chartHessianGradientPair g.form a f k) z l -
    (∑ p, christoffel g.form a z p l k * chartHessianGradientPair g.form a f p z) = _ at hc
  simp only [mul_left_comm (christoffel _ _ _ _ _ _) 2, ← Finset.mul_sum]
  change 2 * rDeriv (chartHessianGradientPair g.form a f k) z l -
      2 * (∑ p, christoffel g.form a z p l k * chartHessianGradientPair g.form a f p z) = _
  linarith

theorem chartCovThird_symm_last (g : SmoothMetric M) (a : M.Carrier)
    {f : ComplexVector n → ℝ} (hf : ContDiffOn ℝ ∞ f (chartTarget a))
    {z : ComplexVector n} (hz : z ∈ chartTarget a) (l k i : RIdx n) :
    chartCovThird g.form a f z l k i = chartCovThird g.form a f z l i k := by
  have hO := isOpen_extChartAt_target (I := ComplexModel n) a
  have hH : (chartCovHessian g.form a f z).IsSymm :=
    chartCovHessian_symm _ _ ((hf.contDiffAt (hO.mem_nhds hz)).of_le (by simp))
  have heq : (fun w => chartCovHessian g.form a f w k i) =ᶠ[𝓝 z]
      (fun w => chartCovHessian g.form a f w i k) := by
    filter_upwards [hO.mem_nhds hz] with w hw
    exact (chartCovHessian_symm g.form a
      ((hf.contDiffAt (hO.mem_nhds hw)).of_le (by simp))).apply i k
  have hd : rDeriv (fun w => chartCovHessian g.form a f w k i) z l =
      rDeriv (fun w => chartCovHessian g.form a f w i k) z l :=
    congrArg (fun D : ComplexVector n →L[ℝ] ℝ => D (realVec l)) heq.fderiv_eq
  have h₁ : (∑ p, christoffel g.form a z p l k * chartCovHessian g.form a f z p i) =
      ∑ p, christoffel g.form a z p l k * chartCovHessian g.form a f z i p := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [hH.apply i p]
  have h₂ : (∑ p, christoffel g.form a z p l i * chartCovHessian g.form a f z k p) =
      ∑ p, christoffel g.form a z p l i * chartCovHessian g.form a f z p k := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [hH.apply p k]
  unfold chartCovThird
  rw [hd, h₁, h₂]
  ring

/-- The contracted commutator is exactly the Ricci correction to the
gradient of the scalar Laplacian. -/
theorem chartCovThird_contract (g : SmoothMetric M) (a : M.Carrier)
    {f : ComplexVector n → ℝ} (hf : ContDiffOn ℝ ∞ f (chartTarget a))
    {z : ComplexVector n} (hz : z ∈ chartTarget a) (i : RIdx n) :
    (∑ l, ∑ k, (realMetricFn g.form a z)⁻¹ l k * chartCovThird g.form a f z l i k) =
      rDeriv (chartRealLaplacian g.form a f) z i +
      ∑ p, (∑ b, (realMetricFn g.form a z)⁻¹ p b *
        L12Aux.realRicciMatrix g.form a z i b) * rDeriv f z p := by
  have hc (l k : RIdx n) : chartCovThird g.form a f z l i k =
      chartCovThird g.form a f z i l k -
        ∑ p, riemannCoeff g.form a z l i k p * rDeriv f z p := by
    have h := chartCovHessian_commutator g a hf hz l i k
    linarith
  have hR : -(∑ l, ∑ k, (realMetricFn g.form a z)⁻¹ l k *
      (∑ p, riemannCoeff g.form a z l i k p * rDeriv f z p)) =
      ∑ p, (∑ b, (realMetricFn g.form a z)⁻¹ p b *
        L12Aux.realRicciMatrix g.form a z i b) * rDeriv f z p := by
    simp only [Finset.mul_sum]
    rw [sum_three_cycle]
    simp only [← mul_assoc, ← Finset.sum_mul]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    rw [← neg_mul, inverseMetric_curvature_contract_ricci g a hz]
  simp_rw [hc, mul_sub, Finset.sum_sub_distrib]
  rw [← chartRealLaplacian_derivative g a hf hz, ← hR]
  ring

/-- The full real Bochner identity for the actual smooth metric in an
arbitrary genuine coordinate chart. -/
theorem chart_bochner_identity (g : SmoothMetric M) (a : M.Carrier)
    {f : ComplexVector n → ℝ} (hf : ContDiffOn ℝ ∞ f (chartTarget a))
    {z : ComplexVector n} (hz : z ∈ chartTarget a) :
    (1 / 2 : ℝ) * chartRealLaplacian g.form a (chartGradientPair g.form a f f) z -
        chartGradientPair g.form a f (chartRealLaplacian g.form a f) z =
      Matrix.trace ((realMetricFn g.form a z)⁻¹ * chartCovHessian g.form a f z *
        (realMetricFn g.form a z)⁻¹ * chartCovHessian g.form a f z) +
      (L12Aux.realRicciMatrix g.form a z).toBilin'
        ((realMetricFn g.form a z)⁻¹ *ᵥ (fun i => rDeriv f z i))
        ((realMetricFn g.form a z)⁻¹ *ᵥ (fun i => rDeriv f z i)) := by
  have hO := isOpen_extChartAt_target (I := ComplexModel n) a
  have hE : (1 / 2 : ℝ) * chartRealLaplacian g.form a (chartGradientPair g.form a f f) z =
      ∑ l, ∑ k, (realMetricFn g.form a z)⁻¹ l k *
        (((realMetricFn g.form a z)⁻¹).toBilin'
          (fun i => chartCovThird g.form a f z l k i) (fun j => rDeriv f z j) +
        ((realMetricFn g.form a z)⁻¹).toBilin'
          (fun i => chartCovHessian g.form a f z k i)
          (fun j => chartCovHessian g.form a f z l j)) := by
    unfold chartRealLaplacian
    simp_rw [chartGradientPair_self_covHessian g a hf hz]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hE]
  exact bochner_contraction_algebra
    ((realMetricFn g.form a z)⁻¹) (chartCovHessian g.form a f z)
    (L12Aux.realRicciMatrix g.form a z) (fun i => rDeriv f z i)
    (fun i => rDeriv (chartRealLaplacian g.form a f) z i)
    (chartCovThird g.form a f z)
    (realMetricFn_isSymm g.form a z).inv
    (chartCovHessian_symm _ _ ((hf.contDiffAt (hO.mem_nhds hz)).of_le (by simp)))
    (chartCovThird_symm_last g a hf hz) (chartCovThird_contract g a hf hz)

end Yau.LeafProofs.L19Aux
