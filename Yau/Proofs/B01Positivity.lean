import Yau.Proofs.B01FrameCurvature

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Set Filter Bundle

noncomputable section

namespace Yau.Proofs.B01Aux
open Yau Yau.Blueprint Yau.Blueprint.BundlePresentation

variable {M : ComplexManifold 1} {r q : ℕ}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

theorem imageCurvature_posSemidef (c : DiscCoordinate M) (hc : IsDiscCoordinate c)
    (k : BundleDbar.Metric E) (A : MapToTrivial E q) (hA : PointwiseInjective E A)
    (hE : BundleDbar.Holomorphic (r := r) E) (hk : BundleDbar.SmoothMetric (r := r) E k)
    (hG : BundleDbar.GriffithsNonnegative (r := r) E k) (hHA : HolomorphicMap (r := r) E A)
    (a : M.Carrier) (z : ℂ) (hz : z ∈ imageFrameDomain (r := r) E c a) :
    (embeddedChernCurvature (imageFibers E c A) (imageMetric E c k A hA)
      (imageFrame (r := r) E c A a) z).PosSemidef := by
  rw [imageCurvatureTransport E c hc k A hA hE hk hHA a z hz]
  apply (bundleCurvature_posSemidef_one E k hk hG a _ (baseChange_mem_localDomain E c hc a hz)).smul
  exact Complex.nonneg_iff.mpr ⟨Complex.normSq_nonneg _, by simp⟩

theorem imagePositivityTransport : ImagePositivityTransport (r := r) (q := q) E := by
  intro c hc k A hA hE hk hG hHA U F hF
  let EI := imageFibers E c A
  let kI := imageMetric E c k A hA
  have hlocal : ∀ z ∈ U,
      (∀ i j, ContDiffAt ℝ ∞ (fun w => embeddedGram EI kI F w i j) z) ∧
      (embeddedChernCurvature EI kI F z).PosSemidef := by
    intro z hz
    let a := c.symm z
    let B := imageFrame (r := r) E c A a
    let V := imageFrameDomain (r := r) E c a
    have hzV : z ∈ V := by
      simpa only [V, a, disc_right_inv c hc (hF.2.1 hz)] using imageFrameDomain_self E c (c.symm z)
    have hB : LocalEmbeddedFrame EI B V :=
      (imageLocalFrameTransport E c hc A hE hHA hA).1 a
    obtain ⟨O, hO, hzO, hOUV, C, hC, hCi, hCF, hdetC⟩ :=
      local_frame_gauge EI B F V U hB hF z hzV hz
    have hBR : ∀ w ∈ O, LinearMap.range (frameLinear (B w)) = EI w :=
      fun w hw => (hB.2.2.2 w (hOUV hw).2).1
    have hFR : ∀ w ∈ O, LinearMap.range (frameLinear (F w)) = EI w :=
      fun w hw => (hF.2.2.2 w (hOUV hw).1).1
    have hHs (i j) : ContDiffOn ℝ ∞ (fun w => embeddedGram EI kI B w i j) O :=
      (imageGram_smooth E c hc k hk A hA a i j).mono (fun _ hw => (hOUV hw).2)
    have hHp : ∀ w ∈ O, (embeddedGram EI kI B w).PosDef :=
      fun w hw => imageGram_posDef E c hc k A hA a w (hOUV hw).2
    refine ⟨fun i j => (embeddedGram_gauge_smooth EI kI B F hBR hFR C hC hCF hHs i j).contDiffAt
      (hO.mem_nhds hzO), ?_⟩
    rw [embedded_curvature_gauge EI kI B F hO hBR hFR C hC hCi hCF hdetC hHs hHp z hzO]
    exact (imageCurvature_posSemidef E c hc k A hA hE hk hG hHA a z hzV).conjTranspose_mul_mul_same (C z)
  exact ⟨fun i j z hz => ((hlocal z hz).1 i j).contDiffWithinAt, fun z hz => (hlocal z hz).2⟩

end Yau.Proofs.B01Aux
