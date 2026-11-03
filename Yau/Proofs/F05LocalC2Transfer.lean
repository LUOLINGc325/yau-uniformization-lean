import Yau.LeafProofs.L16

/-! Actual equality on a spatial neighborhood transfers the ambient spatial
jets and the closed-interval temporal jet, including the initial endpoints. -/

open Set Filter
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux

theorem F05_local_c2_transfer {n : ℕ} {D : Set (Space n)} {T : ℝ}
    {u v : Point n → ℝ} (hu : C2 (cylinder univ 0 T) u)
    (hNear : ∀ x ∈ D, ∀ᶠ y in 𝓝 x, ∀ t ∈ Icc 0 T, u (y,t) = v (y,t)) :
    C2 (cylinder D 0 T) v ∧ EqOn u v (cylinder D 0 T) ∧
      EqOn (spatialD u) (spatialD v) (cylinder D 0 T) ∧
      EqOn (spatialDD u) (spatialDD v) (cylinder D 0 T) ∧
      EqOn (timeD (cylinder univ 0 T) u) (timeD (cylinder D 0 T) v) (cylinder D 0 T) := by
  have hSub : cylinder D 0 T ⊆ cylinder univ 0 T := fun p hp => ⟨mem_univ _,hp.2⟩
  have hVal : EqOn u v (cylinder D 0 T) := by
    intro p hp
    exact (hNear p.1 hp.1).self_of_nhds p.2 hp.2
  have hSlice (p : Point n) (hp : p ∈ cylinder D 0 T) :
      (fun x => u (x,p.2)) =ᶠ[𝓝 p.1] (fun x => v (x,p.2)) := by
    filter_upwards [hNear p.1 hp.1] with x hx
    exact hx p.2 hp.2
  have hD : EqOn (spatialD u) (spatialD v) (cylinder D 0 T) := by
    intro p hp
    exact (hSlice p hp).fderiv_eq (𝕜 := ℝ)
  have hDD : EqOn (spatialDD u) (spatialDD v) (cylinder D 0 T) := by
    intro p hp
    exact ((hSlice p hp).fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)
  have hTime : EqOn (timeD (cylinder univ 0 T) u) (timeD (cylinder D 0 T) v)
      (cylinder D 0 T) := by
    intro p hp
    rw [← timeD_cylinder_restrict_space u hp]
    exact timeD_congr_on hVal hp
  refine ⟨⟨(hu.1.mono hSub).congr (fun p hp => (hVal hp).symm),
    (hu.2.1.mono hSub).congr (fun p hp => (hD hp).symm),
    (hu.2.2.1.mono hSub).congr (fun p hp => (hDD hp).symm),
    (hu.2.2.2.1.mono hSub).congr (fun p hp => (hTime hp).symm),?_,?_⟩,
    hVal,hD,hDD,hTime⟩
  · intro p hp
    exact (hu.2.2.2.2.1 p (hSub hp)).congr_of_eventuallyEq (hSlice p hp).symm
  · intro p hp
    have hAmbient : {t : ℝ | (p.1,t) ∈ cylinder (univ : Set (Space n)) 0 T} = Icc 0 T := by
      ext t
      simp only [cylinder,mem_prod,mem_univ,true_and,mem_setOf_eq]
    have hLocal : {t : ℝ | (p.1,t) ∈ cylinder D 0 T} = Icc 0 T := by
      ext t
      simp only [cylinder,mem_prod,hp.1,true_and,mem_setOf_eq]
    have hDiff := hu.2.2.2.2.2 p (hSub hp)
    rw [hAmbient] at hDiff
    rw [hLocal]
    exact hDiff.congr (fun t ht => ((hNear p.1 hp.1).self_of_nhds t ht).symm) (hVal hp).symm

theorem F05_local_schauder_transfer {n : ℕ} {D : Set (Space n)} {α T C L : ℝ}
    {u v : Point n → ℝ} (hu : SchauderBound α (cylinder univ 0 T) u C)
    (hLow : HolderBound α (cylinder univ 0 T) (fun p => (u p,spatialD u p)) L)
    (hNear : ∀ x ∈ D, ∀ᶠ y in 𝓝 x, ∀ t ∈ Icc 0 T, u (y,t) = v (y,t)) :
    SchauderBound α (cylinder D 0 T) v C ∧
      HolderBound α (cylinder D 0 T) (fun p => (v p,spatialD v p)) L := by
  have hSub : cylinder D 0 T ⊆ cylinder univ 0 T := fun p hp => ⟨mem_univ _,hp.2⟩
  obtain ⟨hC2,hVal,hD,hDD,hTime⟩ := F05_local_c2_transfer hu.1 hNear
  refine ⟨⟨hC2,hu.2.1,?_,
    holderBound_congr_on (holderBound_mono hu.2.2.2.1 hSub) hDD,
    holderBound_congr_on (holderBound_mono hu.2.2.2.2 hSub) hTime⟩,?_⟩
  · intro p hp
    rw [← hVal hp,← hD hp]
    exact hu.2.2.1 p (hSub hp)
  · apply holderBound_congr_on (holderBound_mono hLow hSub)
    intro p hp
    exact Prod.ext (hVal hp) (hD hp)

end Yau.Proofs.F05Aux
