import Yau.Proofs.F05BootstrapLocalJetHolder
import Yau.Proofs.F05BootstrapQuotientSource

/-! The finite commutator Holder budget uses actual coefficient value
words and the supplied shorter solution word's closed spatial jets. -/

open Set
open scoped Matrix Matrix.Norms.Frobenius
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_good_correction_local_holder {ν : Option (RIdx n)} {T α : ℝ}
    (s t : List (Option (RIdx n)))
    (a : Point n → Mat n) (b : Point n → RIdx n → ℝ) (u : Point n → ℝ)
    (ha : F05LocalHolder α ν T (F05GoodWord T s a))
    (hb : ∀ j, F05LocalHolder α ν T (F05GoodWord T s (fun z => b z j)))
    (hu : F05LocalSchauder α ν T (F05GoodWord T t u)) :
    F05LocalHolder α ν T (F05GoodCorrection T (F05PosSpace ν) a b u s t) := by
  have hJets := F05_local_schauder_spatial_jet_holder hu
  intro r hr hr2 S hS hST
  obtain ⟨CA,hCA,hA⟩ := ha r hr hr2 S hS hST
  obtain ⟨CB,hCB,hB⟩ := F05_holder_finite_common (fun j => hb j r hr hr2 S hS hST)
  obtain ⟨CG,hCG,hG⟩ := hJets.1 r hr hr2 S hS hST
  obtain ⟨CH,hCH,hH⟩ := hJets.2 r hr hr2 S hS hST
  let M := max CA CB
  let U := max CG CH
  let D := linearizedSourceBudget n 0 M U
  have hZero : HolderBound α (region ν r ×ˢ Icc S T) (fun _ : Point n => (0 : ℝ)) 0 := by
    simpa only [norm_zero] using holderBound_const α (region ν r ×ˢ Icc S T) (0 : ℝ)
  have hBound := F05_relative_contraction_source_holder hZero
    (holderBound_mono_const hA (le_max_left _ _))
    (fun j => holderBound_mono_const (hB j) (le_max_right _ _))
    (holderBound_mono_const hH (le_max_right _ _))
    (holderBound_mono_const hG (le_max_left _ _))
  refine ⟨|D|+1,by positivity,?_⟩
  have hMon := holderBound_mono_const hBound
    ((le_abs_self D).trans (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)))
  exact holderBound_congr_on hMon (fun z hz => by simp only [F05GoodCorrection,zero_add])

end Yau.Proofs.F05Aux
