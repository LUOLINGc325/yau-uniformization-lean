import Yau.Proofs.F04ChartWeakTestEntries
import Yau.LeafProofs.L16WeakLocalization

open MeasureTheory Filter Set
open scoped Topology ContDiff
noncomputable section
namespace Yau.F04Proof
open Yau.Parabolic Yau.LeafProofs.L16Aux

/-- The actual spatial flux-plus-drift tests have product L2 integrability.
 This follows from genuine joint directional differentiation and compact
 spacetime support, without a global coefficient extension or global
 coefficient bounds. -/
theorem chartWeakTestEntry_spacetime_memLp
    {n : ℕ} {O : Set (Space n)} (hO : IsOpen O) {I : Set ℝ} (hI : IsOpen I)
    {a : Point n → Mat n}
    (ha : ∀ i j, ContDiffOn ℝ 1 (fun p => a p i j) (O ×ˢ I))
    {φ : Point n → ℝ} (hφ : Test (O ×ˢ I) φ) (i j : RIdx n) :
    MemLp (fun p => chartWeakTestEntry (fun z => a (z, p.2)) (fun z => φ (z, p.2)) i j p.1)
      2 (productVolume O I) := by
  let v : Point n := (realVec i, 0)
  let W := fun p => a p i j * fderiv ℝ φ p v + fderiv ℝ (fun q => a q i j) p v * φ p
  have hW : MemLp W 2 volume := compactCoefficient_direction_memLp volume (hO.prod hI)
    (hφ.1.of_le (by simp)) hφ.2.1 hφ.2.2 (ha i j) v
  have hWr : MemLp W 2 (productVolume O I) := by
    rw [productVolume_eq_restrict]
    exact hW.restrict _
  apply (memLp_congr_ae ?_).mp hWr
  rw [productVolume_eq_restrict]
  filter_upwards [ae_restrict_mem (hO.prod hI).measurableSet] with p hp
  have hφd : DifferentiableAt ℝ φ p := hφ.1.differentiable (by simp) p
  have had : DifferentiableAt ℝ (fun q => a q i j) p :=
    ((ha i j).contDiffAt ((hO.prod hI).mem_nhds hp)).differentiableAt one_ne_zero
  change a p i j * fderiv ℝ φ p (realVec i, 0) +
      fderiv ℝ (fun q => a q i j) p (realVec i, 0) * φ p =
    a p i j * d (fun z => φ (z, p.2)) p.1 i +
      d (fun z => a (z, p.2) i j) p.1 i * φ p
  rw [d_eq_joint_fderiv hφd i, d_eq_joint_fderiv had i]

end Yau.F04Proof
