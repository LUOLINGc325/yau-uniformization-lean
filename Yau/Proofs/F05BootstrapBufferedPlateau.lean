import Yau.Proofs.F05BootstrapRelativePlateau
import Yau.Proofs.F05BootstrapFlatGeometry
import Yau.Proofs.F05BootstrapLocalJets
import Yau.Proofs.F05BootstrapRelativeRestriction
import Yau.Proofs.F05BootstrapRelativeTimeTranslation
import Yau.LeafProofs.L16InteriorPlateauJets

/-! The actual spatial and terminal-time jets on an arbitrary base cap of a compact physical patch
recover the original relative jets at every point of its plateau. -/

open Set
open scoped ContDiff
noncomputable section
set_option maxHeartbeats 1400000
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_buffered_interiorPatch_high_on_plateau (ν : Option (RIdx n)) {Rbase s0 T0 δ h σ v : ℝ}
    (hRbase : 0 < Rbase)
    (hδ : 0 < δ) (hh : 0 < h) (c : Space n) {y : Space n} (u : Point n → ℝ)
    (hu : F05RelC2 (region ν Rbase) (Icc s0 T0) u)
    (hStart : s0 ≤ σ) (hEnd : localSchauderTime δ h+σ ≤ T0)
    (hv : v ∈ Icc 0 (localSchauderTime δ h)) (hvPlateau : localSchauderTime δ h/2 < v)
    (hy : ‖y-c‖ < h/8) (hyFlat : y ∈ closure (F05FlatOpen ν)) (hyBall : ‖y‖ < Rbase) :
    (F05RelDD (closure (F05FlatOpen ν)) (classicalInteriorPatch δ h σ hh c u) (y,v),
      F05RelT (Icc 0 (localSchauderTime δ h)) (classicalInteriorPatch δ h σ hh c u) (y,v)) =
      (F05RelDD (region ν Rbase) u (y,v+σ),F05RelT (Icc s0 T0) u (y,v+σ)) := by
  let T := localSchauderTime δ h
  have hT : 0 < T := by dsimp only [T,localSchauderTime]; positivity
  have hX := F05_region_uniqueDiffOn ν hRbase
  have hBase : (y,v+σ) ∈ region ν Rbase ×ˢ Icc s0 T0 := by
    refine ⟨?_,by linarith [hv.1],by linarith [hv.2]⟩
    rw [F05_region_eq_flat_inter_ball]
    exact ⟨hyFlat,by simpa only [Metric.mem_closedBall,dist_zero_right] using hyBall.le⟩
  have hPlateau := F05_relative_cutoff_plateau_jets
    (X := closure (F05FlatOpen ν)) (I := Icc 0 T) (timeTranslate σ u)
    (z := (y,v)) (innerPatchBump_eventually_one_of_inside (by positivity) c hy)
    (initialTimeCutoff_eventually_one_of_plateau hT hvPlateau)
  have hDomain := F05_relative_local_domain_jets (F05_flat_closure_uniqueDiffOn ν) hX
    Metric.isOpen_ball (V := Metric.ball 0 Rbase)
    (fun x hx => by rw [F05_region_eq_flat_inter_ball]; exact ⟨hx.1,Metric.ball_subset_closedBall hx.2⟩)
    hu (z := (y,v+σ))
    ⟨⟨hyFlat,by simpa only [Metric.mem_ball,dist_zero_right] using hyBall⟩,hBase.2⟩
  have hLocalI : Icc (0+σ) (T+σ) ⊆ Icc s0 T0 :=
    fun t ht => ⟨by linarith [ht.1],ht.2.trans hEnd⟩
  have hInterval := uniqueDiffOn_Icc (show 0+σ < T+σ by linarith)
  have huTime := F05_relative_c2_restrict hX hX hInterval Subset.rfl hLocalI hu
  have hShift := F05_relative_timeTranslate_time_jet hT huTime
    (z := (y,v)) ⟨hBase.1,hv⟩
  have hRestrict := F05_relative_restriction_jets hX hX hInterval Subset.rfl hLocalI hu
    (z := (y,v+σ)) ⟨hBase.1,add_le_add hv.1 le_rfl,add_le_add hv.2 le_rfl⟩
  apply Prod.ext
  · exact hPlateau.2.1.trans hDomain.2
  · exact hPlateau.2.2.trans (hShift.trans hRestrict.2.2)

end Yau.Proofs.F05Aux
