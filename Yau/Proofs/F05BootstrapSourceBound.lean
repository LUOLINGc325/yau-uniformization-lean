import Yau.Proofs.F05BootstrapCommutatorBound

/-! A numerical bound for the actual localized source, retaining both the
native commutator and theta' times the unknown value. -/

open Set
open scoped Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1600000
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_localized_relative_source_holder
    {H V X : Set (Space n)} {I : Set ℝ} {α M E0 E1 E2 H0 H1 F L : ℝ}
    {a : Point n → Mat n} {b : Point n → RIdx n → ℝ}
    {φ : Space n → ℝ} {θ : ℝ → ℝ} {u f : Point n → ℝ}
    (ha : HolderBound α (H ×ˢ I) a M)
    (hb : ∀ j, HolderBound α (H ×ˢ I) (fun z => b z j) M)
    (hφ : HolderBound α (H ×ˢ I) (fun z => φ z.1) E0)
    (hφD : HolderBound α (H ×ˢ I) (fun z => fderiv ℝ φ z.1) E1)
    (hφDD : HolderBound α (H ×ˢ I) (fun z => fderiv ℝ (fderiv ℝ φ) z.1) E2)
    (hSupport : tsupport φ ⊆ V)
    (hLow : HolderBound α ((H ∩ V) ×ˢ I) (fun z => (u z,F05RelD X u z)) L)
    (hf : HolderBound α ((H ∩ V) ×ˢ I) f F)
    (hθ : HolderBound α (H ×ˢ I) (fun z => θ z.2) H0)
    (hθD : HolderBound α (H ×ˢ I) (fun z => deriv θ z.2) H1) :
    HolderBound α (H ×ˢ I)
      (fun z => θ z.2*(φ z.1*f z-F05RelSpatialCommutator X a b φ u z)+deriv θ z.2*(φ z.1*u z))
      (4*H0*E0*F+(2*H0*spatialCutoffCommutatorBudget n M E1 E2+4*H1*E0)*L) := by
  let Q : Set (Point n) := H ×ˢ I
  let U : Set (Point n) := V ×ˢ Set.univ
  have hSub : U ∩ Q ⊆ (H ∩ V) ×ˢ I := fun p hp => ⟨⟨hp.2.1,hp.1.1⟩,hp.2.2⟩
  have hZero (p : Point n) (hp : p ∈ Q) (hpU : p ∉ U) : φ p.1 = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hpU ⟨hSupport h,Set.mem_univ _⟩)
  have hProductF : HolderBound α Q (fun p => φ p.1*f p) (2*E0*F) := by
    simpa only [smul_eq_mul] using
      holderBound_smul_cutoff_extension hφ (holderBound_mono hf hSub) hZero
  have hProductU : HolderBound α Q (fun p => φ p.1*u p) (2*E0*L) := by
    simpa only [smul_eq_mul] using holderBound_smul_cutoff_extension hφ
      (holderBound_fst (holderBound_mono hLow hSub)) hZero
  have hCommutator := F05_relative_spatial_commutator_holder_local ha hb hφD hφDD hSupport hLow
  have hMain := holderBound_mul hθ (holderBound_sub hProductF hCommutator)
  have hDerivative := holderBound_mul hθD hProductU
  have hAll := holderBound_add hMain hDerivative
  convert hAll using 1; ring

end Yau.Proofs.F05Aux
