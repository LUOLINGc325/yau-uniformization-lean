import Yau.Proofs.B01Image
import Yau.Proofs.B01CurvatureAlgebra

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Set Filter Bundle

noncomputable section

namespace Yau.Proofs.B01Aux
open Yau Yau.Blueprint Yau.Blueprint.BundlePresentation BundleDbar
open LeafProofs.L14Aux

variable {M : ComplexManifold 1} {r q : ℕ}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

theorem imageGram_posDef (c : DiscCoordinate M) (hc : IsDiscCoordinate c)
    (k : BundleDbar.Metric E) (A : MapToTrivial E q) (hA : PointwiseInjective E A)
    (a : M.Carrier) (z : ℂ) (hz : z ∈ imageFrameDomain (r := r) E c a) :
    (embeddedGram (imageFibers E c A) (imageMetric E c k A hA)
      (imageFrame (r := r) E c A a) z).PosDef := by
  rw [(imageMetricTransport (r := r) (q := q) E c hc k A hA).2 a z hz]
  exact metricMatrix_posDef E k a _ (baseChange_mem_localDomain E c hc a hz)

theorem imageGram_smooth (c : DiscCoordinate M) (hc : IsDiscCoordinate c)
    (k : BundleDbar.Metric E) (hk : BundleDbar.SmoothMetric (r := r) E k)
    (A : MapToTrivial E q) (hA : PointwiseInjective E A) (a : M.Carrier) (α β : Fin r) :
    ContDiffOn ℝ ∞ (fun z => embeddedGram (imageFibers E c A) (imageMetric E c k A hA)
      (imageFrame (r := r) E c A a) z α β) (imageFrameDomain (r := r) E c a) := by
  have hT : ContDiffOn ℂ ∞ (baseChange c a) (imageFrameDomain (r := r) E c a) :=
    fun z hz => (baseChange_contDiffAt E c hc a hz).contDiffWithinAt
  have he := (hk a α β).comp (hT.restrict_scalars ℝ)
    (fun z hz => baseChange_mem_localDomain E c hc a hz)
  apply he.congr
  intro z hz
  exact congrArg (fun H : Matrix (Fin r) (Fin r) ℂ => H α β)
    ((imageMetricTransport (r := r) (q := q) E c hc k A hA).2 a z hz)

theorem baseChange_jacobian (c : DiscCoordinate M) (hc : IsDiscCoordinate c)
    (a : M.Carrier) (z : ℂ) (hz : z ∈ imageFrameDomain (r := r) E c a) :
    fderiv ℂ (fun w => baseChange c a (complexOneEquiv.symm w)) (complexOneEquiv z) (stdVec 0) 0 =
      deriv (fun w => baseChange c a w 0) z := by
  have hT := (baseChange_contDiffAt E c hc a hz).differentiableAt (by simp)
  have hd : fderiv ℂ (fun w => baseChange c a (complexOneEquiv.symm w)) (complexOneEquiv z) =
      (fderiv ℂ (baseChange c a) z).comp complexOneEquiv.symm.toContinuousLinearEquiv.toContinuousLinearMap := by
    have he := complexOneEquiv.symm.toContinuousLinearEquiv.comp_right_fderiv
      (f := baseChange c a) (x := complexOneEquiv z)
    change fderiv ℂ (fun w => baseChange c a (complexOneEquiv.symm w)) (complexOneEquiv z) =
      (fderiv ℂ (baseChange c a) (complexOneEquiv.symm (complexOneEquiv z))).comp
        complexOneEquiv.symm.toContinuousLinearEquiv.toContinuousLinearMap at he
    simpa only [complexOneEquiv.symm_apply_apply] using he
  have hcoord := ((PiLp.hasFDerivAt_apply 2 (baseChange c a z) (0 : Fin 1)).comp z hT.hasFDerivAt).hasDerivAt
  have hderiv : deriv (fun w => baseChange c a w 0) z = (fderiv ℂ (baseChange c a) z (1 : ℂ)) 0 :=
    hcoord.deriv
  rw [hd]
  change (fderiv ℂ (baseChange c a) z (complexOneEquiv.symm (stdVec 0))) 0 = _
  rw [complexOneEquiv_symm_stdVec, hderiv]

theorem imageCurvatureTransport : ImageCurvatureTransport (r := r) (q := q) E := by
  intro c hc k A hA _ hk _ a z hz
  let U := imageFrameDomain (r := r) E c a
  let K := embeddedGram (imageFibers E c A) (imageMetric E c k A hA) (imageFrame (r := r) E c A a)
  let H := BundleDbar.metricMatrix (r := r) E k a
  let O : Set (ComplexVector 1) := complexOneEquiv.symm ⁻¹' U
  let T : ComplexVector 1 → ComplexVector 1 := fun w => baseChange c a (complexOneEquiv.symm w)
  have hU : IsOpen U := imageFrameDomain_isOpen E c hc a
  have hO : IsOpen O := hU.preimage complexOneEquiv.symm.continuous
  have hzO : complexOneEquiv z ∈ O := by simpa only [O, mem_preimage, complexOneEquiv.symm_apply_apply] using hz
  have hK (α β : Fin r) : ContDiffOn ℝ ∞ (fun w => K w α β) U := imageGram_smooth E c hc k hk A hA a α β
  have hdetK : ∀ w ∈ U, (K w).det ≠ 0 := fun w hw =>
    ne_of_gt (imageGram_posDef E c hc k A hA a w hw).det_pos
  have hbridge := scalar_curvatureMatrix_eq K U hU hK hdetK z hz
  change curvatureMatrix (fun w => K (complexOneEquiv.symm w)) (complexOneEquiv z) 0 0 =
    embeddedChernCurvature (imageFibers E c A) (imageMetric E c k A hA) (imageFrame (r := r) E c A a) z at hbridge
  have hGram : EqOn (fun w => K (complexOneEquiv.symm w)) (fun w => H (T w)) O := by
    intro w hw
    exact (imageMetricTransport (r := r) (q := q) E c hc k A hA).2 a _ hw
  have hcong := curvatureMatrix_congr_of_eqOn _ _ hO hGram (complexOneEquiv z) hzO
  have hTbase : ContDiffOn ℂ ∞ (baseChange c a) U :=
    fun w hw => (baseChange_contDiffAt E c hc a hw).contDiffWithinAt
  have hT : ContDiffOn ℂ ∞ T O := hTbase.comp
    complexOneEquiv.symm.toContinuousLinearEquiv.contDiff.contDiffOn (fun _ hw => hw)
  have hTU : MapsTo T O (localDomain (r := r) E a) :=
    fun w hw => baseChange_mem_localDomain E c hc a hw
  have hdetH : ∀ w ∈ localDomain (r := r) E a, (H w).det ≠ 0 :=
    fun w hw => ne_of_gt (metricMatrix_posDef E k a w hw).det_pos
  have hcomp := curvatureMatrix_comp hO (localDomain_isOpen E a) H T (hk a) hdetH hT hTU
    (complexOneEquiv z) hzO (0 : Fin 1) (0 : Fin 1)
  simp only [Fin.sum_univ_one] at hcomp
  rw [baseChange_jacobian (r := r) E c hc a z hz] at hcomp
  rw [Complex.star_def, Complex.mul_conj] at hcomp
  calc
    embeddedChernCurvature (imageFibers E c A) (imageMetric E c k A hA) (imageFrame (r := r) E c A a) z =
        curvatureMatrix (fun w => K (complexOneEquiv.symm w)) (complexOneEquiv z) 0 0 := hbridge.symm
    _ = curvatureMatrix (fun w => H (T w)) (complexOneEquiv z) 0 0 := congrFun (congrFun hcong 0) 0
    _ = _ := by simpa only [T, complexOneEquiv.symm_apply_apply, BundleDbar.curvature] using hcomp

theorem bundleCurvature_posSemidef_one (k : BundleDbar.Metric E)
    (hk : BundleDbar.SmoothMetric (r := r) E k) (hG : GriffithsNonnegative (r := r) E k)
    (a : M.Carrier) (z : ComplexVector 1) (hz : z ∈ localDomain (r := r) E a) :
    (BundleDbar.curvature (r := r) E k a z 0 0).PosSemidef := by
  have hdet : ∀ w ∈ localDomain (r := r) E a,
      (BundleDbar.metricMatrix (r := r) E k a w).det ≠ 0 :=
    fun w hw => ne_of_gt (metricMatrix_posDef E k a w hw).det_pos
  have hHerm : ∀ w ∈ localDomain (r := r) E a,
      (BundleDbar.metricMatrix (r := r) E k a w).IsHermitian :=
    fun w hw => (metricMatrix_posDef E k a w hw).isHermitian
  apply matrix_posSemidef_of_real_nonnegative _
    (curvatureMatrix_diagonal_isHermitian (localDomain_isOpen E a) _ (hk a) hdet hHerm z hz 0)
  intro v
  have he := hG a z hz (stdVec 0) (WithLp.toLp 2 v)
  simp only [griffithsQuadratic, Fin.sum_univ_one, stdVec, PiLp.single_apply] at he
  simp only [ite_true, star_one, mul_one] at he
  convert he using 1
  congr 1
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro α _
  apply Finset.sum_congr rfl
  intro β _
  dsimp only [BundleDbar.curvature]
  ring

end Yau.Proofs.B01Aux
