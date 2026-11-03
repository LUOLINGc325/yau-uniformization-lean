import Yau.LeafProofs.L19BochnerRicci

/-! Differentiating the actual inverse-metric pairing once. -/

noncomputable section

open MeasureTheory Filter
open scoped Topology ContDiff Manifold Matrix ComplexOrder

namespace Yau.LeafProofs.L19Aux

open L18Aux

/-- Inverse-metric compatibility turns ordinary covector derivatives into
their actual covariant derivatives in the bilinear product rule. -/
theorem inverseMetric_pairing_derivative_algebra {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A C : Matrix ι ι ℝ) (x y dx dy : ι → ℝ) :
    (-(C * A + A * Cᵀ)).toBilin' x y + A.toBilin' dx y + A.toBilin' x dy =
      A.toBilin' (dx - Cᵀ *ᵥ x) y + A.toBilin' x (dy - Cᵀ *ᵥ y) := by
  have hleft : x ⬝ᵥ (C *ᵥ (A *ᵥ y)) = (Cᵀ *ᵥ x) ⬝ᵥ (A *ᵥ y) := by
    calc
      _ = (A *ᵥ y) ⬝ᵥ (Cᵀ *ᵥ x) :=
        (Matrix.dotProduct_transpose_mulVec C (A *ᵥ y) x).symm
      _ = _ := dotProduct_comm _ _
  simp only [Matrix.toBilin'_apply', Matrix.neg_mulVec, Matrix.add_mulVec,
    dotProduct_neg, dotProduct_add, sub_dotProduct, Matrix.mulVec_sub,
    dotProduct_sub, ← Matrix.mulVec_mulVec]
  rw [hleft]
  ring

/-- A genuine finite matrix/vector pairing satisfies the ordinary
directional product rule, with no operator or geometric data supplied. -/
theorem rDeriv_matrix_pairing {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ComplexVector n → Matrix ι ι ℝ)
    (u v : ComplexVector n → ι → ℝ) {z : ComplexVector n}
    (hA : ∀ i j, DifferentiableAt ℝ (fun w => A w i j) z)
    (hu : ∀ i, DifferentiableAt ℝ (fun w => u w i) z)
    (hv : ∀ i, DifferentiableAt ℝ (fun w => v w i) z) (l : RIdx n) :
    rDeriv (fun w => (A w).toBilin' (u w) (v w)) z l =
      (L12Aux.matrixDirectionalDerivative A z (realVec l)).toBilin' (u z) (v z) +
      (A z).toBilin' (fun i => rDeriv (fun w => u w i) z l) (v z) +
      (A z).toBilin' (u z) (fun i => rDeriv (fun w => v w i) z l) := by
  have hterm (i j : ι) : DifferentiableAt ℝ
      (fun w => u w i * A w i j * v w j) z := ((hu i).mul (hA i j)).mul (hv j)
  have hrow (i : ι) : DifferentiableAt ℝ
      (fun w => ∑ j, u w i * A w i j * v w j) z := by
    simpa only [Finset.sum_fn] using DifferentiableAt.sum (u := Finset.univ)
      (fun j _ => hterm i j)
  have hfun : (fun w => (A w).toBilin' (u w) (v w)) =
      (fun w => ∑ i, ∑ j, u w i * A w i j * v w j) := by
    funext w
    exact Matrix.toBilin'_apply _ _ _
  rw [hfun, rDeriv_sum _ hrow]
  have hrowD (i : ι) :
      rDeriv (fun w => ∑ j, u w i * A w i j * v w j) z l =
        ∑ j, (u z i * rDeriv (fun w => A w i j) z l * v z j +
          rDeriv (fun w => u w i) z l * A z i j * v z j +
          u z i * A z i j * rDeriv (fun w => v w j) z l) := by
    rw [rDeriv_sum _ (fun j => hterm i j)]
    apply Finset.sum_congr rfl
    intro j hj
    have hprod : DifferentiableAt ℝ (fun w => u w i * A w i j) z := (hu i).mul (hA i j)
    rw [rDeriv_mul hprod (hv j), rDeriv_mul (hu i) (hA i j)]
    ring
  simp_rw [hrowD]
  simp only [Matrix.toBilin'_apply, Finset.sum_add_distrib,
    L12Aux.matrixDirectionalDerivative, rDeriv]

variable {n : ℕ} {M : ComplexManifold n}

/-- B2: differentiating a physical scalar pairing in a fixed coordinate
direction gives the two actual covariant Hessian terms. -/
theorem chartGradientPair_derivative (g : SmoothMetric M) (a : M.Carrier)
    {f k : ComplexVector n → ℝ}
    (hf : ContDiffOn ℝ ∞ f (chartTarget a))
    (hk : ContDiffOn ℝ ∞ k (chartTarget a))
    {z : ComplexVector n} (hz : z ∈ chartTarget a) (l : RIdx n) :
    rDeriv (chartGradientPair g.form a f k) z l =
      ((realMetricFn g.form a z)⁻¹).toBilin'
        (fun i => chartCovHessian g.form a f z l i) (fun j => rDeriv k z j) +
      ((realMetricFn g.form a z)⁻¹).toBilin'
        (fun i => rDeriv f z i) (fun j => chartCovHessian g.form a k z l j) := by
  have hO := isOpen_extChartAt_target (I := ComplexModel n) a
  have hdf (i : RIdx n) := rDeriv_contDiffOn hO hf i
  have hdk (i : RIdx n) := rDeriv_contDiffOn hO hk i
  have hraw := rDeriv_matrix_pairing
    (fun w => (realMetricFn g.form a w)⁻¹)
    (fun w i => rDeriv f w i) (fun w i => rDeriv k w i)
    (fun i j => ((realMetricFn_inverse_contDiffOn g a i j).contDiffAt
      (hO.mem_nhds hz)).differentiableAt (by simp))
    (fun i => ((hdf i).contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp))
    (fun i => ((hdk i).contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp)) l
  rw [inverseMetric_directional_derivative g a hz l] at hraw
  rw [inverseMetric_pairing_derivative_algebra] at hraw
  change rDeriv (chartGradientPair g.form a f k) z l = _ at hraw
  have hHf : ((fun i => rDeriv (fun w => rDeriv f w i) z l) -
      (L12Aux.connectionMatrix g.form a z l)ᵀ *ᵥ (fun i => rDeriv f z i)) =
      (fun i => chartCovHessian g.form a f z l i) := by
    funext i
    rfl
  have hHk : ((fun i => rDeriv (fun w => rDeriv k w i) z l) -
      (L12Aux.connectionMatrix g.form a z l)ᵀ *ᵥ (fun i => rDeriv k z i)) =
      (fun i => chartCovHessian g.form a k z l i) := by
    funext i
    rfl
  rw [hHf, hHk] at hraw
  exact hraw

theorem chartGradientPair_self_derivative (g : SmoothMetric M) (a : M.Carrier)
    {f : ComplexVector n → ℝ} (hf : ContDiffOn ℝ ∞ f (chartTarget a))
    {z : ComplexVector n} (hz : z ∈ chartTarget a) (l : RIdx n) :
    rDeriv (chartGradientPair g.form a f f) z l =
      2 * ((realMetricFn g.form a z)⁻¹).toBilin'
        (fun i => chartCovHessian g.form a f z l i) (fun j => rDeriv f z j) := by
  have hs := (Matrix.isSymm_toBilin'_iff_isSymm.mpr
    (realMetricFn_isSymm g.form a z).inv).eq
    (fun i => rDeriv f z i) (fun i => chartCovHessian g.form a f z l i)
  rw [chartGradientPair_derivative g a hf hf hz, hs]
  ring

end Yau.LeafProofs.L19Aux
