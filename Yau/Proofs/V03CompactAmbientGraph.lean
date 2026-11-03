import Yau.Proofs.V03AtlasCompact

/-! Native compact metric parameter spaces for the image of an intrinsic
compact set under the original immersion, with both actual time slabs. -/

open scoped Topology

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {M : ComplexManifold n}

def compactImmersionPoint (G : CotangentPoint M → ComplexVector q)
    {K : Set (CotangentPoint M)} (p : G '' K) : CotangentPoint M :=
  Classical.choose p.2

theorem compactImmersionPoint_mem (G : CotangentPoint M → ComplexVector q)
    {K : Set (CotangentPoint M)} (p : G '' K) : compactImmersionPoint G p ∈ K :=
  (Classical.choose_spec p.2).1

theorem compactImmersionPoint_image (G : CotangentPoint M → ComplexVector q)
    {K : Set (CotangentPoint M)} (p : G '' K) : G (compactImmersionPoint G p) = p.1 :=
  (Classical.choose_spec p.2).2

theorem compactImmersionPoint_eq {G : CotangentPoint M → ComplexVector q}
    (hG : Function.Injective G) {K : Set (CotangentPoint M)}
    (y : CotangentPoint M) (hy : y ∈ K) :
    compactImmersionPoint G (⟨G y, ⟨y, hy, rfl⟩⟩ : G '' K) = y :=
  hG (compactImmersionPoint_image G _)

theorem cotangentCompact_ambient_isCompact {G : CotangentPoint M → ComplexVector q}
    (hG : CotangentHolomorphic G) {K : Set (CotangentPoint M)} (hK : CotangentCompact K) :
    IsCompact (G '' K) := by
  have hc := (cotangentCompact_native_isCompact hK).image (nativeCotangentMap_continuous hG)
  simpa only [Set.image_image, Function.comp_def] using hc

abbrev CompactImmersionTimes (G : CotangentPoint M → ComplexVector q)
    (K : Set (CotangentPoint M)) (T : ℝ) := ((G '' K) × Set.Icc (0 : ℝ) T) × Set.Icc (0 : ℝ) T

theorem compactImmersionTimes_dist {G : CotangentPoint M → ComplexVector q}
    {K : Set (CotangentPoint M)} {T : ℝ} (p p' : CompactImmersionTimes G K T) :
    dist p p' = max (max ‖p.1.1.1 - p'.1.1.1‖ |p.1.2.1 - p'.1.2.1|)
      |p.2.1 - p'.2.1| := by
  simp only [Prod.dist_eq, Subtype.dist_eq, dist_eq_norm, Real.norm_eq_abs]

theorem compactImmersionTimes_spatial_dist_le {G : CotangentPoint M → ComplexVector q}
    {K : Set (CotangentPoint M)} {T : ℝ} (p p' : CompactImmersionTimes G K T) :
    ‖p.1.1.1 - p'.1.1.1‖ ≤ dist p p' := by
  rw [compactImmersionTimes_dist]
  exact (le_max_left _ _).trans (le_max_left _ _)

theorem compactImmersionTimes_physical_dist_le {G : CotangentPoint M → ComplexVector q}
    {K : Set (CotangentPoint M)} {T : ℝ} (p p' : CompactImmersionTimes G K T) :
    |p.1.2.1 - p'.1.2.1| ≤ dist p p' := by
  rw [compactImmersionTimes_dist]
  exact (le_max_right _ _).trans (le_max_left _ _)

theorem compactImmersionTimes_center_dist_le {G : CotangentPoint M → ComplexVector q}
    {K : Set (CotangentPoint M)} {T : ℝ} (p p' : CompactImmersionTimes G K T) :
    |p.2.1 - p'.2.1| ≤ dist p p' := by
  rw [compactImmersionTimes_dist]
  exact le_max_right _ _

theorem compactImmersionTimes_dist_le_sum {G : CotangentPoint M → ComplexVector q}
    {K : Set (CotangentPoint M)} {T : ℝ} (p p' : CompactImmersionTimes G K T) :
    dist p p' ≤ ‖p.1.1.1 - p'.1.1.1‖ + |p.1.2.1 - p'.1.2.1| + |p.2.1 - p'.2.1| := by
  rw [compactImmersionTimes_dist]
  apply max_le
  · apply max_le
    · linarith [abs_nonneg (p.1.2.1 - p'.1.2.1), abs_nonneg (p.2.1 - p'.2.1)]
    · linarith [norm_nonneg (p.1.1.1 - p'.1.1.1), abs_nonneg (p.2.1 - p'.2.1)]
  · linarith [norm_nonneg (p.1.1.1 - p'.1.1.1), abs_nonneg (p.1.2.1 - p'.1.2.1)]

end Yau.Blueprint.V03Proof
