import Yau.Proofs.F05CanonicalValue

/-! The concrete manifold realization has the original zero lateral trace
and the actual zero one-sided initial time derivative. -/

open Set
noncomputable section
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport
variable {n : ℕ} {M : ComplexManifold n}

theorem F05CanonicalJetFunction_lateral {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {χ : Fin A.count → M.Carrier → ℝ} (hχ : F05Partition O A χ)
    (α : ℝ) {T : ℝ} (hT : 0 ≤ T) (u : F05CompatibleJetGraph A α hT)
    {x : M.Carrier} (hx : x ∈ frontier O) {t : ℝ} (ht : t ∈ Icc 0 T) :
    F05CanonicalJetFunction A χ α hT u x t = 0 := by
  obtain ⟨j,z,hz,hzx⟩ := F05_cover hA (frontier_subset_closure hx)
  have hValue := F05CanonicalJetFunction_value hA hχ α hT u j hz ht
  rw [hzx] at hValue
  apply hValue.trans
  rw [F05BCFFun_apply (u.val j).val.1 ⟨(z,t),hz,ht⟩]
  obtain ⟨_,_,_,_,_,_,_,hPhysical⟩ := hA.1 j
  have hFrontier := (hPhysical z (F05D_mem_ball hz)).2.2
  rw [hzx] at hFrontier
  have hFace := hFrontier.mp hx
  cases hν : A.normal j with
  | none => simp only [hν] at hFace
  | some ν =>
    have hzν : realCoord z ν = 0 := by simpa only [hν] using hFace
    exact F05LocalZeroFTCGraph_lateral A j α hT (u.val j) ⟨z,hz⟩ ⟨t,ht⟩ ν hν hzν

theorem F05CanonicalJetFunction_initial_hasDerivWithinAt {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {χ : Fin A.count → M.Carrier → ℝ} (hχ : F05Partition O A χ)
    (α : ℝ) {T : ℝ} (hT : 0 ≤ T) (u : F05CompatibleJetGraph A α hT)
    {x : M.Carrier} (hx : x ∈ closure O) :
    HasDerivWithinAt (fun t => F05CanonicalJetFunction A χ α hT u x t) 0 (Icc 0 T) 0 := by
  obtain ⟨j,z,hz,hzx⟩ := F05_cover hA hx
  let uj : F05LocalFTCGraph A j α hT := ⟨(u.val j).val,(u.val j).property.1.1.1⟩
  have hGiven := F05LocalFTCGraph_hasDerivWithinAt_raw_time A j α hT uj hz ⟨le_rfl,hT⟩
  have hInitial : F05BCFFun (u.val j).val.2.2.2.val.1 (z,0) = 0 :=
    (F05LocalZeroFTCGraph_initial_total A j α hT (u.val j) z).2.2.2
  change HasDerivWithinAt (fun r => F05BCFFun (u.val j).val.1 (z,r))
    (F05BCFFun (u.val j).val.2.2.2.val.1 (z,0)) (Icc 0 T) 0 at hGiven
  rw [hInitial] at hGiven
  apply hGiven.congr_of_mem _ ⟨le_rfl,hT⟩
  intro r hr
  have hh := F05CanonicalJetFunction_value hA hχ α hT u j hz hr
  rwa [hzx] at hh

end Yau.Proofs.F05Aux
