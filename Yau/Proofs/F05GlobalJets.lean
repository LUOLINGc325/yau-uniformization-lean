import Yau.Blueprint.ParabolicSpaces

/-! Actual spatial derivative jets and the one-sided time derivative give
the literal parabolic C2 predicate on the full slab. -/

open Set Filter
open scoped Topology ContDiff
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic

theorem F05_c2_of_global_jets {n : ℕ} {T : ℝ} (hT : 0 < T)
    (v : Point n → ℝ) (G : Point n → Space n →L[ℝ] ℝ)
    (H : Point n → Space n →L[ℝ] Space n →L[ℝ] ℝ) (K : Point n → ℝ)
    (hv : ContinuousOn v (cylinder univ 0 T))
    (hG : ContinuousOn G (cylinder univ 0 T))
    (hH : ContinuousOn H (cylinder univ 0 T))
    (hK : ContinuousOn K (cylinder univ 0 T))
    (hD : ∀ p ∈ cylinder univ 0 T, HasFDerivAt (fun x => v (x,p.2)) (G p) p.1)
    (hDD : ∀ p ∈ cylinder univ 0 T, HasFDerivAt (fun x => G (x,p.2)) (H p) p.1)
    (ht : ∀ p ∈ cylinder univ 0 T,
      HasDerivWithinAt (fun t => v (p.1,t)) (K p) (Icc 0 T) p.2) :
    C2 (cylinder univ 0 T) v ∧ EqOn (spatialD v) G (cylinder univ 0 T) ∧
      EqOn (spatialDD v) H (cylinder univ 0 T) ∧
      EqOn (timeD (cylinder univ 0 T) v) K (cylinder univ 0 T) := by
  have hSD (p : Point n) (hp : p ∈ cylinder univ 0 T) : spatialD v p = G p := (hD p hp).fderiv
  have hSDD (p : Point n) (hp : p ∈ cylinder univ 0 T) : spatialDD v p = H p := by
    have hEq : fderiv ℝ (fun x => v (x,p.2)) = fun x => G (x,p.2) :=
      funext fun x => hSD (x,p.2) ⟨mem_univ _,hp.2⟩
    unfold spatialDD
    rw [hEq]
    exact (hDD p hp).fderiv
  have hFiber (x : Space n) : {t | (x,t) ∈ cylinder (univ : Set (Space n)) 0 T} = Icc 0 T := by
    ext t
    simp only [cylinder,mem_prod,mem_univ,true_and,mem_setOf_eq]
  have hTD (p : Point n) (hp : p ∈ cylinder univ 0 T) :
      timeD (cylinder univ 0 T) v p = K p := by
    unfold timeD
    rw [hFiber]
    exact (ht p hp).derivWithin (uniqueDiffOn_Icc hT p.2 hp.2)
  refine ⟨⟨hv,hG.congr hSD,hH.congr hSDD,hK.congr hTD,?_,?_⟩,hSD,hSDD,hTD⟩
  · intro p hp
    apply contDiffAt_succ_iff_hasFDerivAt.mpr
    refine ⟨fun x => G (x,p.2),⟨univ,univ_mem,fun x _ => hD (x,p.2) ⟨mem_univ _,hp.2⟩⟩,?_⟩
    apply contDiffAt_succ_iff_hasFDerivAt.mpr
    refine ⟨fun x => H (x,p.2),⟨univ,univ_mem,fun x _ => hDD (x,p.2) ⟨mem_univ _,hp.2⟩⟩,?_⟩
    apply contDiffAt_zero.mpr
    exact ⟨univ,univ_mem,hH.comp (by fun_prop) (fun x _ => ⟨mem_univ _,hp.2⟩)⟩
  · intro p hp
    rw [hFiber]
    exact (ht p hp).differentiableWithinAt

end Yau.Proofs.F05Aux
