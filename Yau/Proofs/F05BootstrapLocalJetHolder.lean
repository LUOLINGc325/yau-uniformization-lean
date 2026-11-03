import Yau.Proofs.F05BootstrapLocalBounds

/-! The actual original-patch spatial gradient and Hessian inherit local
Holder bounds from the supplied relative Schauder caps. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_local_schauder_spatial_jet_holder {ν : Option (RIdx n)} {T α : ℝ}
    {u : Point n → ℝ} (hu : F05LocalSchauder α ν T u) :
    F05LocalHolder α ν T (F05RelD (F05PosSpace ν) u) ∧
      F05LocalHolder α ν T (F05RelDD (F05PosSpace ν) u) := by
  have hCaps (r : ℝ) (hr : 0 < r) (hr2 : r < 2) (s : ℝ) (hs : 0 < s) (hsT : s < T) :
      ∃ C : ℝ, 0 < C ∧
        HolderBound α (region ν r ×ˢ Icc s T) (F05RelD (F05PosSpace ν) u) C ∧
        HolderBound α (region ν r ×ˢ Icc s T) (F05RelDD (F05PosSpace ν) u) C := by
    let R := (r+2)/2
    let S := s/2
    have hR : 0 < R := by dsimp only [R]; linarith
    have hR2 : R < 2 := by dsimp only [R]; linarith
    have hrR : r < R := by dsimp only [R]; linarith
    have hS : 0 < S := by dsimp only [S]; linarith
    have hST : S < T := by dsimp only [S]; linarith
    obtain ⟨C,hC,hSch⟩ := hu R hR hR2 S hS hST
    have hSub : region ν r ×ˢ Icc s T ⊆ region ν R ×ˢ Icc S T :=
      fun z hz => ⟨F05_region_mono hrR.le hz.1,by dsimp only [S]; linarith [hz.2.1],hz.2.2⟩
    have hJets (z : Point n) (hz : z ∈ region ν r ×ˢ Icc s T) :=
      F05_pos_cap_jets hR hSch.1 (F05_receiving_subset_posPatch ν hr2 hs hz)
        (hz.1.1.trans_lt hrR) (show S < z.2 by dsimp only [S]; linarith [hz.2.1])
    exact ⟨C,hC,holderBound_congr_on (holderBound_mono (holderBound_snd hSch.2.1) hSub)
      (fun z hz => (hJets z hz).1.symm),
      holderBound_congr_on (holderBound_mono hSch.2.2.1 hSub)
        (fun z hz => (hJets z hz).2.1.symm)⟩
  constructor
  · intro r hr hr2 s hs hsT
    obtain ⟨C,hC,hD,hDD⟩ := hCaps r hr hr2 s hs hsT
    exact ⟨C,hC,hD⟩
  · intro r hr hr2 s hs hsT
    obtain ⟨C,hC,hD,hDD⟩ := hCaps r hr hr2 s hs hsT
    exact ⟨C,hC,hDD⟩

end Yau.Proofs.F05Aux
