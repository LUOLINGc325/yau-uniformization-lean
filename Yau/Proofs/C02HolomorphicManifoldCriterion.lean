import Yau.Proofs.C02ComplexSmoothness
import spec.CHAIN.CONTRACTS

/-! The complex chart criterion is applied on genuine original target
charts and actual open preimages, rather than on a fixed model manifold. -/

noncomputable section
open Set
open scoped Manifold ContDiff
namespace Yau.Blueprint.C02Proof
variable {n : ℕ} {M : ComplexManifold n}

theorem contMDiffOn_of_complex_coordinate_smoothness
    {O : Set (ComplexVector n)} (hO : IsOpen O)
    {Φ : ComplexVector n → M.Carrier} (hContinuous : ContinuousOn Φ O)
    (hCoordinates : ∀ c : M.Carrier,
      ContDiffOn ℂ ∞ (fun z => chartPt c (Φ z))
        (O ∩ Φ ⁻¹' (chartAt (ComplexVector n) c).source)) :
    ContMDiffOn 𝓘(ℂ, ComplexVector n) (ComplexModel n) ∞ Φ O := by
  intro z hz
  let c := Φ z
  have hc : Φ z ∈ (chartAt (ComplexVector n) c).source := mem_chart_source _ _
  have hV : IsOpen (O ∩ Φ ⁻¹' (chartAt (ComplexVector n) c).source) :=
    hContinuous.isOpen_inter_preimage hO (chartAt (ComplexVector n) c).open_source
  have hAt : ContDiffAt ℂ ∞ (fun w => chartPt c (Φ w)) z :=
    (hCoordinates c).contDiffAt (hV.mem_nhds ⟨hz, hc⟩)
  apply (contMDiffWithinAt_iff_target_of_mem_source hc).mpr
  exact ⟨hContinuous z hz, hAt.contMDiffAt.contMDiffWithinAt⟩

theorem contMDiffOn_of_real_CauchyRiemann_charts
    {O : Set (ComplexVector n)} (hO : IsOpen O)
    {Φ : ComplexVector n → M.Carrier} (hContinuous : ContinuousOn Φ O)
    (hReal : ∀ c x, x ∈ O ∩ Φ ⁻¹' (chartAt (ComplexVector n) c).source →
      DifferentiableAt ℝ (fun w => chartPt c (Φ w)) x)
    (hI : ∀ c x, x ∈ O ∩ Φ ⁻¹' (chartAt (ComplexVector n) c).source →
      ∀ v, fderiv ℝ (fun w => chartPt c (Φ w)) x (Complex.I • v) =
        Complex.I • fderiv ℝ (fun w => chartPt c (Φ w)) x v) :
    ContMDiffOn 𝓘(ℂ, ComplexVector n) (ComplexModel n) ∞ Φ O := by
  apply contMDiffOn_of_complex_coordinate_smoothness hO hContinuous
  intro c
  exact complex_contDiffOn_of_real_CauchyRiemann
    (hContinuous.isOpen_inter_preimage hO (chartAt (ComplexVector n) c).open_source)
    (hReal c) (hI c)

end Yau.Blueprint.C02Proof
