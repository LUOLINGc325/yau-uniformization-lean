import Yau.Proofs.P04LocalCanonicalRepresentative

noncomputable section
open Set Filter
open scoped Topology Manifold ContDiff

namespace Yau.Proofs.P04Aux
open Yau Yau.LeafProofs
variable {n : ℕ} {M : ComplexManifold n}

def canonicalOverlap (a b : M.Carrier) : Set (ComplexVector n) :=
  chartTarget b ∩ (chartInv b) ⁻¹' (extChartAt (ComplexModel n) a).source

theorem canonicalOverlap_isOpen (a b : M.Carrier) : IsOpen (canonicalOverlap a b) :=
  (continuousOn_extChartAt_symm (I := ComplexModel n) b).isOpen_inter_preimage
    (isOpen_extChartAt_target b) (isOpen_extChartAt_source a)

/-- The local tensor's coefficient in another original chart is genuinely
holomorphic on the overlap, with its determinant transition retained. -/
theorem localCanonicalTop_differentiableOn_overlap (a b : M.Carrier)
    (f : ComplexVector n → ℂ) (hf : DifferentiableOn ℂ f (chartTarget a)) :
    DifferentiableOn ℂ
      (fun z => BundleDbar.coefficients (r := 1) (CanonicalCoefficients M)
        (localCanonicalTop a f) b z Fin.elim0 0) (canonicalOverlap a b) := by
  intro z hz
  have hz' : z ∈ BundleDbar.localDomain (r := 1) (CanonicalCoefficients M) b := by
    rw [coefficient_localDomain]
    exact hz.1
  have hya : chartInv b z ∈ L14Aux.bundleChartSource (r := 1) (CanonicalCoefficients M) a := by
    rw [coefficient_bundleChartSource]
    exact hz.2
  have hT := L18Aux.chartTransition_contDiffAt b a hz.1 hz.2
  have htarget : chartPt a (chartInv b z) ∈ chartTarget a :=
    (extChartAt (ComplexModel n) a).map_source hz.2
  have hfa := (hf _ htarget).differentiableAt
    ((isOpen_extChartAt_target a).mem_nhds htarget)
  have hcoeff : DifferentiableAt ℂ
      (fun w => scalarToCoefficient (f (chartPt a (chartInv b w)))) z :=
    scalarToCoefficient.differentiableAt.comp z (hfa.comp z (hT.differentiableAt (by simp)))
  have htrans := L14Aux.topBundleTransition_contDiffAt (CanonicalCoefficients M)
    coefficient_holomorphic a b z hz' hya
  have hmodel : DifferentiableAt ℂ
      (fun w => (L14Aux.topBundleTransition (CanonicalCoefficients M) a b w
        (scalarToCoefficient (f (chartPt a (chartInv b w))))) 0) z :=
    coefficientToScalar.differentiableAt.comp z
      ((htrans.differentiableAt (by simp)).clm_apply hcoeff)
  have heq : (fun w => BundleDbar.coefficients (r := 1) (CanonicalCoefficients M)
      (localCanonicalTop a f) b w Fin.elim0 0) =ᶠ[𝓝 z]
      (fun w => (L14Aux.topBundleTransition (CanonicalCoefficients M) a b w
        (scalarToCoefficient (f (chartPt a (chartInv b w))))) 0) := by
    filter_upwards [(canonicalOverlap_isOpen a b).mem_nhds hz] with w hw
    have hw' : w ∈ BundleDbar.localDomain (r := 1) (CanonicalCoefficients M) b := by
      rw [coefficient_localDomain]
      exact hw.1
    have hwa : chartInv b w ∈ L14Aux.bundleChartSource (r := 1) (CanonicalCoefficients M) a := by
      rw [coefficient_bundleChartSource]
      exact hw.2
    exact congrArg (fun v : ComplexVector 1 => v 0)
      (L14Aux.topFormPushforward_coefficients_inChart (CanonicalCoefficients M) a b
        (fun z => scalarToCoefficient (f z)) w hw' hwa)
  exact (hmodel.congr_of_eventuallyEq heq).differentiableWithinAt

end Yau.Proofs.P04Aux
