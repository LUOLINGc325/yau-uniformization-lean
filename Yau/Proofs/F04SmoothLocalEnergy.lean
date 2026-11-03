import Yau.Proofs.F04ClassicalWeakGradient
import Yau.LeafProofs.L16WeakLocalization

open MeasureTheory Filter Set
open scoped Topology ContDiff
noncomputable section
namespace Yau.F04Proof
open Yau.Parabolic Yau.LeafProofs.L16Aux

/-- A genuine smooth function has literal local energy with its actual
 spatial differential. Every smaller-cylinder L2 bound is constructed by
 compactness; no energy membership is assumed for the classical function. -/
theorem smooth_localEnergy
    {n : ℕ} {O : Set (Space n)} (hO : IsOpen O) {I : Set ℝ} (hI : IsOpen I)
    {u : Point n → ℝ} (hu : ContDiffOn ℝ ∞ u (O ×ˢ I)) :
    LocalEnergy O I u (dgGradient u) := by
  have hQ := hO.prod hI
  refine ⟨classical_weakGradient hQ hu, ?_⟩
  intro V l r hV hVC hVO hlr
  have hVV : volume V < (⊤ : ENNReal) :=
    lt_of_le_of_lt (measure_mono subset_closure) hVC.measure_lt_top
  let : IsFiniteMeasure (volume.restrict V) := isFiniteMeasure_restrict.mpr hVV.ne
  let : IsFiniteMeasure (productVolume V (Ioo l r)) := by
    unfold productVolume
    infer_instance
  have hSub : closure V ×ˢ Icc l r ⊆ O ×ˢ I := prod_mono hVO hlr
  have hPSub : V ×ˢ Ioo l r ⊆ O ×ˢ I :=
    (Set.prod_mono subset_closure Ioo_subset_Icc_self).trans hSub
  have hLp (v : Point n → ℝ) (hv : ContinuousOn v (O ×ˢ I)) :
      MemLp v 2 (productVolume V (Ioo l r)) := by
    obtain ⟨C, hC⟩ := (hVC.prod isCompact_Icc).bddAbove_image (hv.norm.mono hSub)
    have hM : AEStronglyMeasurable v (productVolume V (Ioo l r)) := by
      rw [productVolume_eq_restrict]
      exact (hv.mono hPSub).aestronglyMeasurable (hV.prod isOpen_Ioo).measurableSet
    apply MemLp.of_bound hM C
    rw [productVolume_eq_restrict]
    filter_upwards [ae_restrict_mem (hV.prod isOpen_Ioo).measurableSet] with p hp
    exact hC ⟨p, ⟨subset_closure hp.1, Ioo_subset_Icc_self hp.2⟩, rfl⟩
  exact ⟨hLp u hu.continuousOn, fun i => hLp (fun p => dgGradient u p i)
    (dgGradient_contDiffOn hQ hu i).continuousOn⟩

end Yau.F04Proof
