import Yau.LeafProofs.L16FiniteDataHolderGluing
import Yau.LeafProofs.L16HolderExtension

/-! Native finite Holder gluing is made uniform in the moving endpoint by
actual time clamping to that endpoint, with the native cover fixed at S. -/

open Set
noncomputable section
set_option maxHeartbeats 1600000
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux

theorem F05_uniform_compact_holder_glue {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    {K : Set (Space n)} (hK : IsCompact K) {α : ℝ} (hα : 0 ≤ α) (S : ℝ)
    (r A : K → ℝ) (hr : ∀ i, 0 < r i) (hA : ∀ i, 0 ≤ A i) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : ℝ) (hT : 0 ≤ T), T ≤ S →
      ∀ (f : Point n → E) (P : ℝ), 0 ≤ P →
      (∀ p ∈ cylinder K 0 T, ‖f p‖ ≤ P) →
      (∀ i : K, HolderBound α (cylinder (K∩Metric.closedBall (i : Space n) (r i)) 0 T) f (A i*P)) →
      HolderBound α (cylinder K 0 T) f (C*P) := by
  obtain ⟨C,hC,hGlue⟩ := compact_spatial_local_holder_glue (E := E) (T := S) hK hα r A hr hA
  refine ⟨C,hC,?_⟩
  intro T hT hTS f P hP hSup hLocal
  let fT : Point n → E := fun p => f (clampPointTime 0 T hT p)
  have hSupT : ∀ p ∈ cylinder K 0 S, ‖fT p‖ ≤ P := by
    intro p hp
    exact hSup (clampPointTime 0 T hT p) ⟨hp.1,(projIcc 0 T hT p.2).property⟩
  have hLocalT (i : K) :
      HolderBound α (cylinder (K∩Metric.closedBall (i : Space n) (r i)) 0 S) fT (A i*P) := by
    have h := holderBound_clampPointTime hα hT (K∩Metric.closedBall (i : Space n) (r i)) (hLocal i)
    exact holderBound_mono h (fun p hp => ⟨hp.1,mem_univ _⟩)
  have hGlued := hGlue fT P hP hSupT hLocalT
  have hRestricted := holderBound_mono hGlued
    (show cylinder K 0 T ⊆ cylinder K 0 S from fun p hp => ⟨hp.1,hp.2.1,hp.2.2.trans hTS⟩)
  apply holderBound_congr_on hRestricted
  intro p hp
  change f (clampPointTime 0 T hT p) = f p
  apply congrArg f
  change (p.1, ((projIcc 0 T hT p.2) : ℝ)) = p
  exact Prod.ext rfl (congrArg Subtype.val (projIcc_of_mem hT hp.2))

end Yau.Proofs.F05Aux
