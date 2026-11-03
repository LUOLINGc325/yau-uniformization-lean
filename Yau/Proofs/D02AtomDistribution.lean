import Yau.Proofs.D02AtomPairings
import Yau.Proofs.D02RieszGreen

/-! A locally smooth representative of the SAME original limiting
distribution has zero mass at its center. -/

open scoped Topology ContDiff ENNReal
open MeasureTheory Filter Metric Set

noncomputable section
namespace Yau.NodeProofs.D02Aux
open Yau Yau.LeafProofs

theorem riesz_atom_zero_of_smooth_local_representative {D U : Set ℂ}
    (hU : IsOpen U) (hUD : U ⊆ D) (hD : MeasurableSet D)
    (μ : Measure ℂ) (u v : ℂ → ℝ)
    (hμ : ∀ K : Set ℂ, IsCompact K → K ⊆ D → μ K < ⊤)
    (hdist : ∀ χ : ℂ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ → tsupport χ ⊆ D →
      (2 * Real.pi) * (∫ z, χ z ∂μ) = ∫ z, u z * LeafCandidates.realPlanarLaplacian χ z)
    (hv : ContDiffOn ℝ ∞ v U) (hae : u =ᵐ[volume.restrict U] v)
    {z₀ : ℂ} (hz : z₀ ∈ U) : μ {z₀} = 0 := by
  apply atom_zero_of_smooth_test_pairings hU μ (LeafCandidates.realPlanarLaplacian v)
    (L08_contDiffOn_realPlanarLaplacian hU hv).continuousOn (fun K hK hKU => hμ K hK (hKU.trans hUD))
    (fun χ hχ hχc hχU => ?_) hz
  calc
    _ = ∫ z, u z * LeafCandidates.realPlanarLaplacian χ z :=
      hdist χ hχ hχc (hχU.trans hUD)
    _ = ∫ z, v z * LeafCandidates.realPlanarLaplacian χ z := by
      have hglobal := (ae_restrict_iff' hU.measurableSet).mp hae
      apply integral_congr_ae
      filter_upwards [hglobal] with z hz
      by_cases hzD : z ∈ U
      · rw [hz hzD]
      · have hzero : LeafCandidates.realPlanarLaplacian χ z = 0 :=
          image_eq_zero_of_notMem_tsupport (fun h => hzD (hχU (L08_tsupport_realPlanarLaplacian_subset hχ h)))
        rw [hzero, mul_zero, mul_zero]
    _ = ∫ z, LeafCandidates.realPlanarLaplacian v z * χ z :=
      D02RieszAux.integral_laplacian_swap hU hv hχ hχc hχU

end Yau.NodeProofs.D02Aux
