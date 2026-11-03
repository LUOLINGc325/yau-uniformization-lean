import Yau.Proofs.F05BootstrapRelativeCommutator
import Yau.LeafProofs.L16LocalizedClassicalEquation

/-! The actual relative commutator has the native numerical Hölder budget
from the lower jet alone, on the original physical set. -/

open Set
open scoped Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1600000
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_relative_spatial_commutator_holder_local
    {H V X : Set (Space n)} {I : Set ℝ} {α M E1 E2 L : ℝ}
    {a : Point n → Mat n} {b : Point n → RIdx n → ℝ}
    {φ : Space n → ℝ} {u : Point n → ℝ}
    (ha : HolderBound α (H ×ˢ I) a M)
    (hb : ∀ j, HolderBound α (H ×ˢ I) (fun z => b z j) M)
    (hφD : HolderBound α (H ×ˢ I) (fun z => fderiv ℝ φ z.1) E1)
    (hφDD : HolderBound α (H ×ˢ I) (fun z => fderiv ℝ (fderiv ℝ φ) z.1) E2)
    (hSupport : tsupport φ ⊆ V)
    (hLow : HolderBound α ((H ∩ V) ×ˢ I) (fun z => (u z,F05RelD X u z)) L) :
    HolderBound α (H ×ˢ I) (F05RelSpatialCommutator X a b φ u)
      (spatialCutoffCommutatorBudget n M E1 E2*L) := by
  let Q : Set (Point n) := H ×ˢ I
  let U : Set (Point n) := V ×ˢ Set.univ
  have hLow' : HolderBound α (U ∩ Q) (fun p => (u p,F05RelD X u p)) L :=
    holderBound_mono hLow (fun p hp => ⟨⟨hp.2.1,hp.1.1⟩,hp.2.2⟩)
  have hValue := holderBound_fst hLow'
  have hGrad (i : Yau.RIdx n) := holderBound_gradient_component (holderBound_snd hLow') i
  have hZeroD (i : Yau.RIdx n) (p : Point n) (hp : p ∈ Q) (hpU : p ∉ U) :
      fderiv ℝ φ p.1 (Yau.realVec i) = 0 := by
    have hNot : p.1 ∉ tsupport φ := fun h => hpU ⟨hSupport h,Set.mem_univ _⟩
    rw [fderiv_of_notMem_tsupport (𝕜 := ℝ) hNot,zero_apply]
  have hZeroDD (i j : Yau.RIdx n) (p : Point n) (hp : p ∈ Q) (hpU : p ∉ U) :
      fderiv ℝ (fderiv ℝ φ) p.1 (Yau.realVec i) (Yau.realVec j) = 0 := by
    have hNot : p.1 ∉ tsupport (fderiv ℝ φ) := fun h =>
      hpU ⟨hSupport (tsupport_fderiv_subset ℝ h),Set.mem_univ _⟩
    rw [fderiv_of_notMem_tsupport (𝕜 := ℝ) hNot,zero_apply,zero_apply]
  have hDG (i j : Yau.RIdx n) : HolderBound α Q
      (fun p => fderiv ℝ φ p.1 (Yau.realVec i)*F05RelD X u p (Yau.realVec j)) (2*E1*L) := by
    simpa only [smul_eq_mul] using holderBound_smul_cutoff_extension
      (holderBound_gradient_component hφD i) (hGrad j) (hZeroD i)
  have hHV (i j : Yau.RIdx n) : HolderBound α Q
      (fun p => u p*fderiv ℝ (fderiv ℝ φ) p.1 (Yau.realVec i) (Yau.realVec j)) (2*E2*L) := by
    simpa only [smul_eq_mul,mul_comm] using holderBound_smul_cutoff_extension
      (holderBound_hessian_component hφDD i j) hValue (hZeroDD i j)
  have hDV (i : Yau.RIdx n) : HolderBound α Q
      (fun p => fderiv ℝ φ p.1 (Yau.realVec i)*u p) (2*E1*L) := by
    simpa only [smul_eq_mul] using holderBound_smul_cutoff_extension
      (holderBound_gradient_component hφD i) hValue (hZeroD i)
  have hMatrix (i j : Yau.RIdx n) : HolderBound α Q
      (fun p => a p i j*
        (fderiv ℝ φ p.1 (Yau.realVec i)*F05RelD X u p (Yau.realVec j)+
          fderiv ℝ φ p.1 (Yau.realVec j)*F05RelD X u p (Yau.realVec i)+
          u p*fderiv ℝ (fderiv ℝ φ) p.1 (Yau.realVec i) (Yau.realVec j)))
      ((8*M*E1+4*M*E2)*L) := by
    have h := holderBound_mul (holderBound_matrix_entry ha i j)
      (holderBound_add (holderBound_add (hDG i j) (hDG j i)) (hHV i j))
    convert h using 1; ring
  have hRow (i : Yau.RIdx n) := holderBound_finset_sum Finset.univ (fun j _ => hMatrix i j)
  have hMatrixSum := holderBound_finset_sum Finset.univ (fun i _ => hRow i)
  have hDrift (i : Yau.RIdx n) : HolderBound α Q
      (fun p => b p i*(fderiv ℝ φ p.1 (Yau.realVec i)*u p)) (4*M*E1*L) := by
    have h := holderBound_mul (hb i) (hDV i)
    convert h using 1; ring
  have hDriftSum := holderBound_finset_sum Finset.univ (fun i _ => hDrift i)
  have hSum := holderBound_add hMatrixSum hDriftSum
  have hAlgebra (p : Point n) :
      (∑ i : Yau.RIdx n, b p i*(fderiv ℝ φ p.1 (Yau.realVec i)*u p)) =
        u p*(∑ i : Yau.RIdx n, b p i*fderiv ℝ φ p.1 (Yau.realVec i)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  apply holderBound_congr_on _ (show Set.EqOn
    (fun p => (∑ i : Yau.RIdx n, ∑ j : Yau.RIdx n, a p i j*
      (fderiv ℝ φ p.1 (Yau.realVec i)*F05RelD X u p (Yau.realVec j)+
        fderiv ℝ φ p.1 (Yau.realVec j)*F05RelD X u p (Yau.realVec i)+
        u p*fderiv ℝ (fderiv ℝ φ) p.1 (Yau.realVec i) (Yau.realVec j)))+
      ∑ i : Yau.RIdx n, b p i*(fderiv ℝ φ p.1 (Yau.realVec i)*u p))
    (F05RelSpatialCommutator X a b φ u) Q from by
      intro p hp
      dsimp only
      rw [hAlgebra p]
      rfl)
  convert hSum using 1
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  dsimp only [spatialCutoffCommutatorBudget]
  ring

end Yau.Proofs.F05Aux
