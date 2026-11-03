import Yau.LeafProofs.L14CutoffCalculus
import Yau.LeafProofs.L14PositiveEnergy
import Yau.LeafProofs.L14CompactDbar

set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped Manifold Topology ContDiff ComplexOrder ENNReal Matrix Kronecker
open MeasureTheory Bundle Filter Module

namespace Yau.LeafProofs.L14Aux
open BundleDbar

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

def bknDifferentialEnergy (g : HermitianField M) (h : Metric E) (φ : M.Carrier → ℝ)
    (u : NQForm E 1) (f : NQForm E 2) (S : NQForm E 0) (x : M.Carrier) : ℝ :=
  BundleDbar.formNormSq (r := r) E g h f x * Real.exp (-φ x) +
    BundleDbar.formNormSq (r := r) E g h S x * Real.exp (-φ x) -
    positiveFormEnergy (r := r) E g h φ u x

theorem weighted_formNormSq_top_inChart (g : HermitianField M) (h : Metric E)
    (φ : M.Carrier → ℝ) (S : NQForm E 0) (a : M.Carrier) (z : ComplexVector n)
    (hz : z ∈ localDomain (r := r) E a) :
    BundleDbar.formNormSq (r := r) E g h S (chartInv a z) * Real.exp (-φ (chartInv a z)) =
      ((hMat g a z).det.re)⁻¹ *
        (star (fun α => coefficients (r := r) E S a z Fin.elim0 α) ⬝ᵥ
          weightedMetricMatrix (BundleDbar.metricMatrix (r := r) E h a) (inChart a φ) z *ᵥ
          (fun α => coefficients (r := r) E S a z Fin.elim0 α)).re := by
  rw [formNormSq_top_inChart E g h S a z hz]
  simp only [weightedMetricMatrix, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have he : (∑ α, ∑ β, star (coefficients (r := r) E S a z Fin.elim0 α) *
      BundleDbar.metricMatrix (r := r) E h a z α β * coefficients (r := r) E S a z Fin.elim0 β) =
      star (fun α => coefficients (r := r) E S a z Fin.elim0 α) ⬝ᵥ
        BundleDbar.metricMatrix (r := r) E h a z *ᵥ
        (fun α => coefficients (r := r) E S a z Fin.elim0 α) := by
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum, mul_assoc]
  rw [he]
  simp only [inChart]
  ring

theorem weighted_formNormSq_two_inChart (g : HermitianField M) (h : Metric E)
    (φ : M.Carrier → ℝ) (f : NQForm E 2) (a : M.Carrier) (z : ComplexVector n)
    (hz : z ∈ localDomain (r := r) E a) :
    BundleDbar.formNormSq (r := r) E g h f (chartInv a z) * Real.exp (-φ (chartInv a z)) =
      ((hMat g a z).det.re)⁻¹ * twoCoefficientNormSq (hMat g a z)
        (weightedMetricMatrix (BundleDbar.metricMatrix (r := r) E h a) (inChart a φ) z)
        (fun α i j => coefficients (r := r) E f a z ![i,j] α) := by
  rw [formNormSq_two_chart_factor E g h f a z hz]
  rw [weightedMetricMatrix, twoCoefficientNormSq_smul_metric]
  simp only [twoCoefficientNormSq, inChart]
  ring

theorem bknDifferentialEnergy_inChart (hE : Holomorphic (r := r) E)
    (g : Yau.SmoothMetric M) (h : Metric E) (φ : M.Carrier → ℝ)
    (u : NQForm E 1) (hu : SmoothForm (r := r) E u) (f : NQForm E 2) (S : NQForm E 0)
    (a : M.Carrier) (z : ComplexVector n) (hz : z ∈ localDomain (r := r) E a) :
    bknDifferentialEnergy (r := r) E g.form h φ u f S (chartInv a z) =
      ((hMat g.form a z).det.re)⁻¹ *
        (twoCoefficientNormSq (hMat g.form a z)
          (weightedMetricMatrix (BundleDbar.metricMatrix (r := r) E h a) (inChart a φ) z)
          (fun α i j => coefficients (r := r) E f a z ![i,j] α) +
        (star (fun α => coefficients (r := r) E S a z Fin.elim0 α) ⬝ᵥ
          weightedMetricMatrix (BundleDbar.metricMatrix (r := r) E h a) (inChart a φ) z *ᵥ
          (fun α => coefficients (r := r) E S a z Fin.elim0 α)).re -
        (positiveTensorContraction (hMat g.form a z)
          (weightedMetricMatrix (BundleDbar.metricMatrix (r := r) E h a) (inChart a φ) z)
          (raisedBarTensor (r := r) E g.form u a z)).re) := by
  rw [bknDifferentialEnergy, weighted_formNormSq_two_inChart E g.form h φ f a z hz,
    weighted_formNormSq_top_inChart E g.form h φ S a z hz,
    positiveFormEnergy_inChart E hE g h φ u hu a z hz]
  simp only [chartPositiveEnergy]
  ring

theorem finite_bknDifferentialEnergy_IMS_inChart {ι : Type*} [Fintype ι]
    (hE : Holomorphic (r := r) E) (g : Yau.SmoothMetric M) (h : Metric E) (φ : M.Carrier → ℝ)
    (u : NQForm E 1) (hu : SmoothForm (r := r) E u) (f : NQForm E 2)
    (hdu : SmoothDbarRepresents (r := r) E u f) (S : NQForm E 0)
    (χ : ι → M.Carrier → ℝ) (hχ : ∀ k, SmoothFn (χ k))
    (fχ : ι → NQForm E 2)
    (hdfχ : ∀ k, SmoothDbarRepresents (r := r) E (multiplyForm E (fun x => (χ k x : ℂ)) u) (fχ k))
    (Sχ : ι → NQForm E 0)
    (hSχ : ∀ k, Sχ k = multiplyForm E (fun x => (χ k x : ℂ)) S - scalarGradientContraction (r := r) E g.form (χ k) u)
    (a : M.Carrier) (z : ComplexVector n) (hz : z ∈ localDomain (r := r) E a)
    (hnear : ∀ᶠ x in 𝓝 (chartInv a z), ∑ k, χ k x ^ 2 = 1) :
    (∑ k, bknDifferentialEnergy (r := r) E g.form h φ
      (multiplyForm E (fun x => (χ k x : ℂ)) u) (fχ k) (Sχ k) (chartInv a z)) =
      bknDifferentialEnergy (r := r) E g.form h φ u f S (chartInv a z) := by
  classical
  let G := hMat g.form a z
  let K := weightedMetricMatrix (BundleDbar.metricMatrix (r := r) E h a) (inChart a φ) z
  let η := fun k => χ k (chartInv a z)
  let b := fun k i => wirtBar (fun w => Complex.ofReal (inChart a (χ k) w)) z (stdVec i)
  let W := fun α j => raisedOneCoefficientsMatrix (r := r) E g.form u a z j α
  let T := fun α i j => coefficients (r := r) E f a z ![i,j] α
  let A := fun α => coefficients (r := r) E S a z Fin.elim0 α
  let D := raisedBarTensor (r := r) E g.form u a z
  have hG : G.PosDef := hMat_posDef g.form a z hz.1
  have hK : K.PosDef := weightedMetricMatrix_posDef _ _ z (metricMatrix_posDef E h a z hz)
  have hGW (α : Fin r) : G *ᵥ W α = (fun i => coefficients (r := r) E u a z (fun _ => i) α) := by
    have hW : W α = G⁻¹ *ᵥ (fun i => coefficients (r := r) E u a z (fun _ => i) α) := by rfl
    rw [hW, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (hG.isUnit.map Matrix.detMonoidHom), Matrix.one_mulVec]
  have hcχ : ∑ k, η k ^ 2 = 1 := hnear.self_of_nhds
  have hb (i : Fin n) : ∑ k, (η k : ℂ) * b k i = 0 :=
    square_partition_chart_wirtBar_zero χ hχ a z hz.1 hnear i
  have he := finite_BKN_IMS G K hG hK η b W T A D hcχ hb
  have hfχ (k : ι) : (fun α i j => coefficients (r := r) E (fχ k) a z ![i,j] α) =
      (fun α i j => (η k : ℂ) * T α i j + (b k i * (G *ᵥ W α) j - b k j * (G *ᵥ W α) i)) := by
    funext α i j
    rw [hdfχ k a z hz ![i,j] α, dbarCoefficients_one_multiply_real E (χ k) (hχ k) u hu a z hz i j α,
      ← hdu a z hz ![i,j] α, hGW]
    dsimp only [η, T, b]
    ring
  have hSχc (k : ι) : (fun α => coefficients (r := r) E (Sχ k) a z Fin.elim0 α) =
      (fun α => (η k : ℂ) * A α - star (b k) ⬝ᵥ W α) := by
    funext α
    rw [hSχ k, coefficients_sub, coefficients_multiplyForm,
      coefficients_scalarGradientContraction_apply E g.form (χ k) (hχ k) u a z hz α]
    change (η k : ℂ) * A α - (∑ i, ∑ j, star (b k i) * G⁻¹ i j *
      coefficients (r := r) E u a z (fun _ => j) α) = _
    simp only [dotProduct, Pi.star_apply, W, raisedOneCoefficientsMatrix,
      oneCoefficientsMatrix, Matrix.mul_apply, Finset.mul_sum, mul_assoc]
    rfl
  have hDχ (k : ι) : raisedBarTensor (r := r) E g.form
      (multiplyForm E (fun x => (χ k x : ℂ)) u) a z =
      (fun α i j => (η k : ℂ) * D α i j + b k i * W α j) := by
    funext α i j
    exact raisedBarTensor_multiply E g (χ k) (hχ k) u hu a z hz α i j
  have hlocal (k : ι) : bknDifferentialEnergy (r := r) E g.form h φ
      (multiplyForm E (fun x => (χ k x : ℂ)) u) (fχ k) (Sχ k) (chartInv a z) =
      G.det.re⁻¹ * (twoCoefficientNormSq G K
        (fun α i j => (η k : ℂ) * T α i j + (b k i * (G *ᵥ W α) j - b k j * (G *ᵥ W α) i)) +
        (star (fun α => (η k : ℂ) * A α - star (b k) ⬝ᵥ W α) ⬝ᵥ K *ᵥ
          (fun α => (η k : ℂ) * A α - star (b k) ⬝ᵥ W α)).re -
        (positiveTensorContraction G K (fun α i j => (η k : ℂ) * D α i j + b k i * W α j)).re) := by
    rw [bknDifferentialEnergy_inChart E hE g h φ _ (smoothForm_multiply_real E (χ k) (hχ k) u hu) _ _ a z hz,
      hfχ, hSχc, hDχ]
  calc
    _ = G.det.re⁻¹ * (∑ k : ι, (twoCoefficientNormSq G K
        (fun α i j => (η k : ℂ) * T α i j + (b k i * (G *ᵥ W α) j - b k j * (G *ᵥ W α) i)) +
        (star (fun α => (η k : ℂ) * A α - star (b k) ⬝ᵥ W α) ⬝ᵥ K *ᵥ
          (fun α => (η k : ℂ) * A α - star (b k) ⬝ᵥ W α)).re -
        (positiveTensorContraction G K (fun α i j => (η k : ℂ) * D α i j + b k i * W α j)).re)) := by
      simp_rw [hlocal, Finset.mul_sum]
    _ = G.det.re⁻¹ * (twoCoefficientNormSq G K T + (star A ⬝ᵥ K *ᵥ A).re -
        (positiveTensorContraction G K D).re) := congrArg (G.det.re⁻¹ * ·) he
    _ = _ := (bknDifferentialEnergy_inChart E hE g h φ u hu f S a z hz).symm

theorem finite_bknDifferentialEnergy_IMS {ι : Type*} [Fintype ι]
    (hE : Holomorphic (r := r) E) (g : Yau.SmoothMetric M) (h : Metric E) (φ : M.Carrier → ℝ)
    (u : NQForm E 1) (hu : SmoothForm (r := r) E u) (f : NQForm E 2)
    (hdu : SmoothDbarRepresents (r := r) E u f) (S : NQForm E 0)
    (χ : ι → M.Carrier → ℝ) (hχ : ∀ k, SmoothFn (χ k))
    (fχ : ι → NQForm E 2)
    (hdfχ : ∀ k, SmoothDbarRepresents (r := r) E (multiplyForm E (fun x => (χ k x : ℂ)) u) (fχ k))
    (Sχ : ι → NQForm E 0)
    (hSχ : ∀ k, Sχ k = multiplyForm E (fun x => (χ k x : ℂ)) S - scalarGradientContraction (r := r) E g.form (χ k) u)
    (x : M.Carrier) (hnear : ∀ᶠ y in 𝓝 x, ∑ k, χ k y ^ 2 = 1) :
    (∑ k, bknDifferentialEnergy (r := r) E g.form h φ
      (multiplyForm E (fun x => (χ k x : ℂ)) u) (fχ k) (Sχ k) x) =
      bknDifferentialEnergy (r := r) E g.form h φ u f S x := by
  have hInv : chartInv x (chartPt x x) = x := chartInv_chartPt_of_mem x x (mem_chart_source _ _)
  have hz : chartPt x x ∈ localDomain (r := r) E x := by
    refine ⟨mem_extChartAt_target x, ?_⟩
    change chartInv x (chartPt x x) ∈ (localTriv (r := r) E x).baseSet
    rw [hInv]
    exact FiberBundle.mem_baseSet_trivializationAt' x
  have ht := finite_bknDifferentialEnergy_IMS_inChart E hE g h φ u hu f hdu S χ hχ fχ hdfχ Sχ hSχ
    x (chartPt x x) hz (by rw [hInv]; exact hnear)
  simpa only [hInv] using ht

end Yau.LeafProofs.L14Aux
