import Yau.LeafProofs.L14

noncomputable section
open scoped Manifold Topology ContDiff ComplexOrder ENNReal Matrix
open MeasureTheory Bundle Filter Module

namespace Yau.LeafProofs.L14Aux
open BundleDbar

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

def bundleChartOverlap (a b : M.Carrier) : Set (ComplexVector n) :=
  localDomain (r := r) E b ∩ (chartInv b) ⁻¹' bundleChartSource (r := r) E a

theorem bundleChartOverlap_isOpen (a b : M.Carrier) :
    IsOpen (bundleChartOverlap (r := r) E a b) :=
  ((continuousOn_extChartAt_symm (I := ComplexModel n) b).mono Set.inter_subset_left).isOpen_inter_preimage
    (localDomain_isOpen E b) (bundleChartSource_isOpen (r := r) E a)

theorem chartTransition_maps_bundleChartOverlap (a b : M.Carrier) :
    Set.MapsTo (fun w => chartPt a (chartInv b w))
      (bundleChartOverlap (r := r) E a b) (localDomain (r := r) E a) := by
  intro w hw
  refine ⟨(extChartAt (ComplexModel n) a).map_source hw.2.1, ?_⟩
  change chartInv a (chartPt a (chartInv b w)) ∈ (localTriv (r := r) E a).baseSet
  rw [chartInv_chartPt_of_mem a _ (by simpa only [extChartAt_source] using hw.2.1)]
  exact hw.2.2

theorem chartTransition_bundleChartOverlap_contDiff (a b : M.Carrier) :
    ContDiffOn ℂ ∞ (fun w => chartPt a (chartInv b w)) (bundleChartOverlap (r := r) E a b) := by
  intro z hz
  exact (L18Aux.chartTransition_contDiffAt b a hz.1.1 hz.2.1).contDiffWithinAt

def bundleFrameTransitionMatrix (a b x : M.Carrier) : Matrix (Fin r) (Fin r) ℂ :=
  fun α β => (localTriv (r := r) E a).coordChangeL ℂ (localTriv (r := r) E b) x (stdVec β) α

theorem bundleFrameTransitionMatrix_eq_basis (a b x : M.Carrier)
    (ha : x ∈ (localTriv (r := r) E a).baseSet)
    (hb : x ∈ (localTriv (r := r) E b).baseSet) :
    bundleFrameTransitionMatrix (r := r) E a b x =
      (bundleFrameBasis (r := r) E b x hb).toMatrix (bundleFrameBasis (r := r) E a x ha) := by
  ext α β
  simp only [bundleFrameTransitionMatrix, Basis.toMatrix_apply, bundleFrameBasis_repr,
    bundleFrameBasis_apply, bundleCoordChange_apply E a b x ha hb]

theorem bundleFrameTransitionMatrix_mul_reverse (a b x : M.Carrier)
    (ha : x ∈ (localTriv (r := r) E a).baseSet)
    (hb : x ∈ (localTriv (r := r) E b).baseSet) :
    bundleFrameTransitionMatrix (r := r) E a b x * bundleFrameTransitionMatrix (r := r) E b a x = 1 := by
  classical
  rw [bundleFrameTransitionMatrix_eq_basis E a b x ha hb,
    bundleFrameTransitionMatrix_eq_basis E b a x hb ha, Basis.toMatrix_mul_toMatrix_flip]

theorem bundleFrameTransitionMatrix_contDiffAt (hE : Holomorphic (r := r) E)
    (a b c : M.Carrier) (z : ComplexVector n) (hz : z ∈ chartTarget c)
    (ha : chartInv c z ∈ (localTriv (r := r) E a).baseSet)
    (hb : chartInv c z ∈ (localTriv (r := r) E b).baseSet) (α β : Fin r) :
    ContDiffAt ℂ ∞ (fun w => bundleFrameTransitionMatrix (r := r) E a b (chartInv c w) α β) z := by
  letI : ContMDiffVectorBundle ⊤ (ComplexVector r) E (ComplexModel n) := hE
  have hi : ContMDiffAt 𝓘(ℂ, ComplexVector n) (ComplexModel n) ∞ (chartInv c) z :=
    (contMDiffOn_extChartAt_symm (I := ComplexModel n) c).contMDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)
  have hC : ContMDiffAt (ComplexModel n) 𝓘(ℂ, ComplexVector r →L[ℂ] ComplexVector r) ∞
      (fun x => ((localTriv (r := r) E a).coordChangeL ℂ (localTriv (r := r) E b) x :
        ComplexVector r →L[ℂ] ComplexVector r)) (chartInv c z) :=
    contMDiffAt_coordChangeL ha hb
  have hv := (hC.comp z hi).contDiffAt.clm_apply
    (show ContDiffAt ℂ ∞ (fun _ : ComplexVector n => stdVec β) z from contDiffAt_const)
  exact (contDiffAt_piLp 2).mp hv α

theorem metricMatrix_at_chartPt (h : Metric E) (a x : M.Carrier)
    (hx : x ∈ bundleChartSource (r := r) E a) :
    BundleDbar.metricMatrix (r := r) E h a (chartPt a x) =
      hermitianGram (h x) (bundleFrameBasis (r := r) E a x hx.2) := by
  unfold BundleDbar.metricMatrix
  rw [chartInv_chartPt_of_mem a x (by simpa only [extChartAt_source] using hx.1)]
  ext α β
  simp only [hermitianGram, bundleFrameBasis_apply]

theorem metricMatrix_overlap (h : Metric E) (a b : M.Carrier) (z : ComplexVector n)
    (hz : z ∈ bundleChartOverlap (r := r) E a b) :
    BundleDbar.metricMatrix (r := r) E h b z =
      (bundleFrameTransitionMatrix (r := r) E b a (chartInv b z))ᴴ *
        BundleDbar.metricMatrix (r := r) E h a (chartPt a (chartInv b z)) *
          bundleFrameTransitionMatrix (r := r) E b a (chartInv b z) := by
  let y := chartInv b z
  have hyb : y ∈ bundleChartSource (r := r) E b :=
    ⟨(extChartAt (ComplexModel n) b).map_target hz.1.1, hz.1.2⟩
  have hzb : chartPt b y = z := (extChartAt (ComplexModel n) b).right_inv hz.1.1
  have hmetricB : BundleDbar.metricMatrix (r := r) E h b z =
      hermitianGram (h y) (bundleFrameBasis (r := r) E b y hyb.2) := by
    calc
      _ = BundleDbar.metricMatrix (r := r) E h b (chartPt b y) := congrArg (fun w =>
        BundleDbar.metricMatrix (r := r) E h b w) hzb.symm
      _ = _ := metricMatrix_at_chartPt E h b y hyb
  rw [bundleFrameTransitionMatrix_eq_basis E b a y hyb.2 hz.2.2,
    metricMatrix_at_chartPt E h a y hz.2, hmetricB]
  exact hermitianGram_changeBasis (h y) (bundleFrameBasis (r := r) E a y hz.2.2)
    (bundleFrameBasis (r := r) E b y hyb.2)

theorem hMat_overlap (g : HermitianField M) (a b : M.Carrier) (z : ComplexVector n)
    (hz : z ∈ bundleChartOverlap (r := r) E a b) :
    hMat g b z =
      (Matrix.of fun p i => fderiv ℂ (fun w => chartPt a (chartInv b w)) z (stdVec i) p)ᴴ *
        hMat g a (chartPt a (chartInv b z)) *
          (Matrix.of fun p i => fderiv ℂ (fun w => chartPt a (chartInv b w)) z (stdVec i) p) := by
  let y := chartInv b z
  have hyb : y ∈ (extChartAt (ComplexModel n) b).source :=
    (extChartAt (ComplexModel n) b).map_target hz.1.1
  have hya := hz.2.1
  have hinv : chartInv a (chartPt a y) = y :=
    chartInv_chartPt_of_mem a y (by simpa only [extChartAt_source] using hya)
  have hgA : hMat g a (chartPt a y) = hermitianGram (g y) (chartFrameBasis a y hya) := by
    change frameGram g a (chartInv a (chartPt a y)) = _
    rw [hinv]
    exact frameGram_eq_hermitianGram g a y hya
  have hgB : hMat g b z = hermitianGram (g y) (chartFrameBasis b y hyb) :=
    frameGram_eq_hermitianGram g b y hyb
  rw [hgB, hgA, ← chartFrameBasis_toMatrix_fderiv a b z hz.1.1 hya]
  exact hermitianGram_changeBasis (g y) (chartFrameBasis a y hya) (chartFrameBasis b y hyb)

end Yau.LeafProofs.L14Aux
