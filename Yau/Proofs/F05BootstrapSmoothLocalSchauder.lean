import Yau.Proofs.F05BootstrapSmoothRelative
import Yau.Proofs.F05BootstrapLocalVectorHolder
import Yau.Proofs.F05BootstrapRelativeRestriction
import Yau.Proofs.F05BootstrapSchauderLimit

/-! A fixed smooth physical datum has actual local relative Schauder
bounds, including its computed one-sided terminal-time derivative. -/

open Set
open scoped ContDiff
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_smooth_background_local_schauder {ν : Option (RIdx n)} {T α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) {f : Point n → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Metric.ball 0 3 ×ˢ Ioc 0 T)) : F05LocalSchauder α ν T f := by
  have hC2 := F05_smooth_background_relative_c2 (ν := ν) hf
  have hJets := F05_smooth_background_relative_jets (ν := ν) hf
  have hAmbient := F05_joint_spatial_jets_smooth Metric.isOpen_ball hf
  have hTime := F05_joint_vector_time_derivative_smooth (uniqueDiffOn_Ioc 0 T) hf
  have hVHolder := F05_positive_smooth_local_holder (ν := ν) hα hα1 hf
  have hDHolder := F05_local_vector_holder_congr
    (F05_positive_smooth_local_holder (ν := ν) hα hα1 hAmbient.1) (fun z hz => (hJets.1 hz).symm)
  have hHHolder := F05_local_vector_holder_congr
    (F05_positive_smooth_local_holder (ν := ν) hα hα1 hAmbient.2) (fun z hz => (hJets.2 hz).symm)
  have hTHolder := F05_positive_smooth_local_holder (ν := ν) hα hα1 hTime
  intro r hr hr2 s hs hsT
  obtain ⟨CV,hCV,hV⟩ := hVHolder r hr hr2 s hs hsT
  obtain ⟨CD,hCD,hD⟩ := hDHolder r hr hr2 s hs hsT
  obtain ⟨CH,hCH,hH⟩ := hHHolder r hr hr2 s hs hsT
  obtain ⟨CT,hCT,hT⟩ := hTHolder r hr hr2 s hs hsT
  let C := CV+CD+CH+CT
  have hC : 0 < C := by dsimp only [C]; positivity
  have hSpace : region ν r ⊆ F05PosSpace ν := F05_region_subset_posSpace ν hr2
  have hI : Icc s T ⊆ Ioc 0 T := fun t ht => ⟨hs.trans_le ht.1,ht.2⟩
  have hLocalC2 := F05_relative_c2_restrict (F05_posSpace_uniqueDiffOn ν)
    (F05_region_uniqueDiffOn ν hr) (uniqueDiffOn_Icc hsT) hSpace hI hC2
  have hRestriction (z : Point n) (hz : z ∈ region ν r ×ˢ Icc s T) :=
    F05_relative_restriction_jets (F05_posSpace_uniqueDiffOn ν) (F05_region_uniqueDiffOn ν hr)
      (uniqueDiffOn_Icc hsT) hSpace hI hC2 hz
  have hLocalD := holderBound_congr_on hD (fun z hz => (hRestriction z hz).1.symm)
  have hLocalH := holderBound_congr_on hH (fun z hz => (hRestriction z hz).2.1.symm)
  have hLocalT := holderBound_congr_on hT (fun z hz => (hRestriction z hz).2.2.symm)
  refine ⟨C,hC,hLocalC2,?_,?_,?_⟩
  · exact F05_holderBound_prod_same (holderBound_mono_const hV (by dsimp only [C]; linarith))
      (holderBound_mono_const hLocalD (by dsimp only [C]; linarith))
  · exact holderBound_mono_const hLocalH (by dsimp only [C]; linarith)
  · exact holderBound_mono_const hLocalT (by dsimp only [C]; linarith)

end Yau.Proofs.F05Aux
