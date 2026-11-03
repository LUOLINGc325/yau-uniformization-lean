import Yau.Proofs.F04ClosedParabolicGradient
import Yau.LeafProofs.L16WeakLocalization

open MeasureTheory Filter Set
open scoped Topology ContDiff
noncomputable section
namespace Yau.F04Proof
open Yau.Parabolic Yau.LeafProofs.L16Aux

/-- Actual compact closed-cylinder continuity supplies actual product L2
 on its open spatial/time interior; no norm or integrability is an inlet. -/
theorem continuousOn_compactCylinder_memLp
    {n : ℕ} {O : Set (Space n)} (hO : IsOpen O) (hOC : IsCompact (closure O)) {l r : ℝ}
    {v : Point n → ℝ} (hv : ContinuousOn v (closure O ×ˢ Icc l r)) :
    MemLp v 2 (productVolume O (Ioo l r)) := by
  have hOV : volume O < (⊤ : ENNReal) :=
    lt_of_le_of_lt (measure_mono subset_closure) hOC.measure_lt_top
  let : IsFiniteMeasure (volume.restrict O) := isFiniteMeasure_restrict.mpr hOV.ne
  let : IsFiniteMeasure (productVolume O (Ioo l r)) := by
    unfold productVolume
    infer_instance
  obtain ⟨C, hC⟩ := (hOC.prod isCompact_Icc).bddAbove_image hv.norm
  have hM : AEStronglyMeasurable v (productVolume O (Ioo l r)) := by
    rw [productVolume_eq_restrict]
    exact (hv.mono (prod_mono subset_closure Ioo_subset_Icc_self)).aestronglyMeasurable
      (hO.prod isOpen_Ioo).measurableSet
  apply MemLp.of_bound hM C
  rw [productVolume_eq_restrict]
  filter_upwards [ae_restrict_mem (hO.prod isOpen_Ioo).measurableSet] with p hp
  exact hC ⟨p, ⟨subset_closure hp.1, Ioo_subset_Icc_self hp.2⟩, rfl⟩

/-- A genuinely smooth full-space closed-slab particular solution and its
 ACTUAL spatial differential are product L2 on every precompact chart
 region, including all times approaching the initial face. -/
theorem fullSpace_smooth_compactCylinder_memLp_gradient
    {n : ℕ} {O : Set (Space n)} (hO : IsOpen O) (hOC : IsCompact (closure O)) {S : ℝ}
    {p : Point n → ℝ} (hp : ContDiffOn ℝ ∞ p (univ ×ˢ Icc 0 S)) :
    MemLp p 2 (productVolume O (Ioo 0 S)) ∧
      ∀ i, MemLp (fun q => spatialD p q (realVec i)) 2 (productVolume O (Ioo 0 S)) := by
  have hSub : closure O ×ˢ Icc (0 : ℝ) S ⊆ univ ×ˢ Icc 0 S :=
    prod_mono (subset_univ _) (Subset.refl _)
  refine ⟨continuousOn_compactCylinder_memLp hO hOC (hp.continuousOn.mono hSub), ?_⟩
  intro i
  exact continuousOn_compactCylinder_memLp hO hOC
    ((fullSpace_spatialComponent_smooth hp i).continuousOn.mono hSub)

end Yau.F04Proof
