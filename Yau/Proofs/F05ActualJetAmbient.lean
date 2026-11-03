import Yau.Proofs.F05ActualLocalZeroFTC
import Yau.Proofs.F05JetAmbient

/-! Actual chart jets with genuine homogeneous traces give an element of
the complete finite jet product, with its literal inherited norm bound. -/

open Set
open scoped Topology
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

def F05ActualJetAmbient {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {α C T : ℝ} (hα : 0 < α) (hT : 0 ≤ T)
    (w : M.Carrier → ℝ → ℝ)
    (hw : ∀ i : Fin A.count, SchauderBound α (F05Q A i T) (pull A i w) C)
    (h0 : ∀ x ∈ closure O, w x 0 = 0)
    (hTime0 : ∀ i : Fin A.count, ∀ z ∈ F05D A i, timeD (F05Q A i T) (pull A i w) (z,0) = 0)
    (hBoundary : ∀ x ∈ frontier O, ∀ t ∈ Icc 0 T, w x t = 0) : F05JetAmbient A α hT :=
  fun i => F05ActualLocalZeroFTC A i hα hT (hw i)
    (fun z hz => h0 _ (F05D_lift_mem_closure hA hz)) (hTime0 i) (by
      intro z hz t ht j hν hzj
      obtain ⟨_,_,_,_,_,_,_,hPhysical⟩ := hA.1 i
      apply hBoundary _ ((hPhysical z (F05D_mem_ball hz)).2.2.mpr ?_) t ht
      simpa only [hν] using hzj)

theorem F05ActualJetAmbient_norm_le {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {α C T : ℝ} (hα : 0 < α) (hT : 0 ≤ T)
    (w : M.Carrier → ℝ → ℝ)
    (hw : ∀ i : Fin A.count, SchauderBound α (F05Q A i T) (pull A i w) C)
    (h0 : ∀ x ∈ closure O, w x 0 = 0)
    (hTime0 : ∀ i : Fin A.count, ∀ z ∈ F05D A i, timeD (F05Q A i T) (pull A i w) (z,0) = 0)
    (hBoundary : ∀ x ∈ frontier O, ∀ t ∈ Icc 0 T, w x t = 0) (hC : 0 ≤ C) :
    ‖F05ActualJetAmbient hA hα hT w hw h0 hTime0 hBoundary‖ ≤ C := by
  apply (pi_norm_le_iff_of_nonneg hC).mpr
  intro i
  exact F05ActualJetComponent_norm_le hα (hw i)

theorem F05ActualJetAmbient_eval {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {α C T : ℝ} (hα : 0 < α) (hT : 0 ≤ T)
    (w : M.Carrier → ℝ → ℝ)
    (hw : ∀ i : Fin A.count, SchauderBound α (F05Q A i T) (pull A i w) C)
    (h0 : ∀ x ∈ closure O, w x 0 = 0)
    (hTime0 : ∀ i : Fin A.count, ∀ z ∈ F05D A i, timeD (F05Q A i T) (pull A i w) (z,0) = 0)
    (hBoundary : ∀ x ∈ frontier O, ∀ t ∈ Icc 0 T, w x t = 0)
    (i : Fin A.count) (p : F05Q A i T) :
    (F05ActualJetAmbient hA hα hT w hw h0 hTime0 hBoundary i).val.1 p = pull A i w p.val ∧
    (F05ActualJetAmbient hA hα hT w hw h0 hTime0 hBoundary i).val.2.1 p = spatialD (pull A i w) p.val ∧
    (F05ActualJetAmbient hA hα hT w hw h0 hTime0 hBoundary i).val.2.2.1.val.1 p = spatialDD (pull A i w) p.val ∧
    (F05ActualJetAmbient hA hα hT w hw h0 hTime0 hBoundary i).val.2.2.2.val.1 p = timeD (F05Q A i T) (pull A i w) p.val :=
  ⟨rfl,rfl,rfl,rfl⟩

end Yau.Proofs.F05Aux
