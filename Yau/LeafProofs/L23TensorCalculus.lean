import Yau.Geometry.ParabolicCalculus
import Yau.LeafProofs.L19OrthonormalTrace
import Mathlib.Analysis.Matrix.Order

/-! Actual tensor contractions used by the local curvature argument. -/

noncomputable section

open scoped Topology ContDiff Matrix MatrixOrder
open Filter

namespace Yau.LeafProofs.L23Aux

variable {n : ℕ} {M : ComplexManifold n}

def jetSq (h : HermitianField M) (k : ℕ) (x : M.Carrier) : ℝ :=
  covTensorNormSq (realMetricFn h x (chartPt x x))
    (rmJet h x k (chartPt x x))

def realLap (h : HermitianField M) (f : M.Carrier → ℝ) (x : M.Carrier) : ℝ :=
  L19Aux.chartRealLaplacian h x (inChart x f) (chartPt x x)

def realGradPair (h : HermitianField M) (f g : M.Carrier → ℝ)
    (x : M.Carrier) : ℝ :=
  L18Aux.chartGradientPair h x (inChart x f) (inChart x g) (chartPt x x)

def flowOp (h : ℝ → HermitianField M) (σ : ℝ)
    (u : M.Carrier → ℝ → ℝ) (x : M.Carrier) (t : ℝ) : ℝ :=
  deriv (u x) t - (σ/2) * realLap (h t) (fun y => u y t) x

def roughLap {r : ℕ} (h : HermitianField M) (c : M.Carrier)
    (A : ComplexVector n → CovTensor n r) (z : ComplexVector n) : CovTensor n r :=
  fun v => ∑ i, ∑ j, (realMetricFn h c z)⁻¹ i j *
    covariantD h c (covariantD h c A) z (Fin.cons i (Fin.cons j v))

/-- The coefficient action of curvature on every covariant slot. -/
def curvatureAction {r : ℕ} (h : HermitianField M) (c : M.Carrier)
    (z : ComplexVector n) (i j : RIdx n) (A : CovTensor n r) : CovTensor n r :=
  fun v => -∑ s : Fin r, ∑ b : RIdx n,
    riemannCoeff h c z i j (v s) b * A (Function.update v s b)

section FiniteContractions

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def tensorFrameTransform (D : Matrix ι κ ℝ) {r : ℕ}
    (A : (Fin r → ι) → ℝ) (v : Fin r → κ) : ℝ :=
  ∑ w : Fin r → ι, A w * ∏ j : Fin r, D (w j) (v j)

/-- A Gram factor in every slot gives an ordinary finite dot product. -/
theorem tensor_contraction_eq_frame_sum (H : Matrix ι ι ℝ) (D : Matrix ι κ ℝ)
    (hH : H = D * Dᵀ) {r : ℕ} (A B : (Fin r → ι) → ℝ) :
    (∑ v : Fin r → ι, ∑ w : Fin r → ι,
      A v * B w * ∏ j : Fin r, H (v j) (w j)) =
      ∑ a : Fin r → κ, tensorFrameTransform D A a * tensorFrameTransform D B a := by
  classical
  have hp (v w : Fin r → ι) :
      (∏ j : Fin r, H (v j) (w j)) =
        ∑ a : Fin r → κ, ∏ j : Fin r, D (v j) (a j) * D (w j) (a j) := by
    simp only [hH, Matrix.mul_apply, Matrix.transpose_apply]
    exact Fintype.prod_sum _
  simp_rw [hp, Finset.mul_sum, Finset.prod_mul_distrib]
  conv_lhs =>
    arg 2
    ext v
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  unfold tensorFrameTransform
  simp only [Finset.sum_mul, Finset.mul_sum]
  conv_rhs =>
    arg 2
    ext a
    rw [Finset.sum_comm]
  congr 1
  funext a
  congr 1
  funext v
  congr 1
  funext w
  ring

end FiniteContractions

/-- The square-root factor is used only in this finite matrix identity. -/
theorem inverseMetric_exists_gram_factor {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℝ) (hG : G.PosDef) :
    ∃ D : Matrix ι ι ℝ, G⁻¹ = D * Dᵀ := by
  let D := CFC.sqrt G⁻¹
  have hD : Dᵀ = D := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, sub_zero] using
      (CFC.sqrt_nonneg G⁻¹).isHermitian.eq
  refine ⟨D, ?_⟩
  rw [hD]
  simpa only [pow_two] using (CFC.sq_sqrt G⁻¹ hG.posSemidef.inv.nonneg).symm

theorem covTensorNormSq_nonneg {r : ℕ}
    (G : Matrix (RIdx n) (RIdx n) ℝ) (hG : G.PosDef) (A : CovTensor n r) :
    0 ≤ covTensorNormSq G A := by
  obtain ⟨D, hD⟩ := inverseMetric_exists_gram_factor G hG
  unfold covTensorNormSq
  rw [tensor_contraction_eq_frame_sum _ D hD]
  exact Finset.sum_nonneg (fun v _ => mul_self_nonneg _)

theorem jetSq_nonneg (h : HermitianField M) (k : ℕ) (x : M.Carrier) :
    0 ≤ jetSq h k x :=
  covTensorNormSq_nonneg _
    (L12Aux.realMetricFn_posDef h x _ (mem_extChartAt_target x)) _

theorem curvatureJetNorm_sq (h : HermitianField M) (k : ℕ) (x : M.Carrier) :
    curvatureJetNorm h k x ^ 2 = jetSq h k x :=
  Real.sq_sqrt (jetSq_nonneg h k x)

theorem metricFamilySmooth_slice (h : ℝ → HermitianField M)
    {I : Set ℝ} (hh : MetricFamilySmooth h I) {t : ℝ} (ht : t ∈ I) :
    MetricSmooth (h t) := by
  intro x i j
  exact (hh x i j).comp (contDiffOn_id.prodMk contDiffOn_const)
    (fun z hz => ⟨hz, ht⟩)

end Yau.LeafProofs.L23Aux
