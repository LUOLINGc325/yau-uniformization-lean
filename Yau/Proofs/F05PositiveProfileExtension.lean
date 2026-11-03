import Yau.Proofs.F05NormalSeeley
import Yau.Proofs.F05ProfileLocalTransfer
import Yau.Proofs.F05SmoothProfileGluing

/-! Every actual positive-time physical profile has a genuine global
smooth extension. The normal extensions are constructed by the certified
Seeley operator and glued without changing the original profile. -/

open Set
open scoped Topology ContDiff Manifold
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_positive_profile_global_extension {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (w : M.Carrier → ℝ → ℝ) {τ T t : ℝ} (ht : t ∈ Icc τ T)
    (hInner : ∀ k, ContDiffOn ℝ ∞ (pull A k w)
      (region (A.normal k) (3/2) ×ˢ Icc τ T)) :
    ∃ g : M.Carrier → ℝ, SmoothFn g ∧ EqOn g (fun x => w x t) (closure O) := by
  apply F05_smooth_profile_extension_of_local isClosed_closure (fun x => w x t)
  intro x hx
  obtain ⟨i,z,hz,hzx⟩ := F05_cover hA hx
  rw [← hzx]
  have hz3 := F05D_mem_ball hz
  have hPatch := F05_inner_smooth_to_physical_patch hA w hInner i
  by_cases hzOpen : z ∈ F05ModelOpen A i
  · let V := Metric.ball (0 : Space n) 3 ∩ F05ModelOpen A i
    have hV : IsOpen V := by
      change IsOpen (Metric.ball (0 : Space n) 3 ∩ F05ModelOpen A i)
      rw [F05ModelOpen_eq]
      exact Metric.isOpen_ball.inter (F05FlatOpen_isOpen _)
    have hProfile : ContDiffOn ℝ ∞ (fun y => pull A i w (y,t)) V := by
      apply hPatch.comp (contDiffOn_id.prodMk contDiffOn_const)
      intro y hy
      have hIn : lift A i y ∈ O := by
        apply (((hA.1 i).2.2.2.2.2.2.2 y hy.1).1).mpr
        cases hν : A.normal i <;> simpa only [F05ModelOpen,hν,mem_univ,mem_ofPred_eq] using hy.2
      exact ⟨⟨hy.1,subset_closure hIn⟩,ht⟩
    exact F05_local_profile_model_to_manifold hA i hz3 hV ⟨hz3,hzOpen⟩ hProfile
      (fun x => w x t) (fun _ _ _ _ => rfl)
  · cases hν : A.normal i with
    | none =>
      exact (hzOpen (by simp only [F05ModelOpen,hν,mem_univ])).elim
    | some j =>
      have hLe : realCoord z j ≤ 0 := by
        have h := (((hA.1 i).2.2.2.2.2.2.2 z hz3).2.1).mp (by rwa [hzx])
        simpa only [hν] using h
      have hNotLt : ¬realCoord z j < 0 := by
        simpa only [F05ModelOpen,hν,mem_ofPred_eq] using hzOpen
      have hFace : realCoord z j = 0 := le_antisymm hLe (not_lt.mp hNotLt)
      obtain ⟨V,F,hV,hzV,hF,hEq⟩ := F05_positive_boundary_profile_local_extension
        hA i j hν w ht hInner hz3 hFace
      apply F05_local_profile_model_to_manifold hA i hz3 hV hzV hF (fun x => w x t)
      intro y hy hy3 hyPhys
      apply hEq y hy
      have h := (((hA.1 i).2.2.2.2.2.2.2 y hy3).2.1).mp hyPhys
      simpa only [hν] using h

end Yau.Proofs.F05Aux
