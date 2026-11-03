import Yau.Proofs.F05CanonicalRegularity
import Yau.Proofs.F05JetRealization
import Yau.Proofs.F05JetNorms

/-! The concrete finite manifold sum realizes every compatible physical jet,
with its actual original product norm controlling the literal Schauder bound. -/

open Set
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

def F05CanonicalPull (A : AtlasData M) (χ : Fin A.count → M.Carrier → ℝ)
    (α : ℝ) {T : ℝ} (hT : 0 ≤ T) (u : F05CompatibleJetGraph A α hT) (j : Fin A.count) : Point n → ℝ :=
  fun p => F05CanonicalJetFunction A χ α hT u (lift A j p.1) p.2

theorem F05CanonicalJetFunction_realizes {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {χ : Fin A.count → M.Carrier → ℝ} (hχ : F05Partition O A χ)
    (α : ℝ) {T : ℝ} (hT : 0 < T) (u : F05CompatibleJetGraph A α hT.le) (j : Fin A.count) :
    C2 (F05Q A j T) (F05CanonicalPull A χ α hT.le u j) ∧
      EqOn (spatialD (F05CanonicalPull A χ α hT.le u j)) (F05BCFFun (u.val j).val.2.1) (F05Q A j T) ∧
      EqOn (spatialDD (F05CanonicalPull A χ α hT.le u j)) (F05BCFFun (u.val j).val.2.2.1.val.1) (F05Q A j T) ∧
      EqOn (timeD (F05Q A j T) (F05CanonicalPull A χ α hT.le u j))
        (F05BCFFun (u.val j).val.2.2.2.val.1) (F05Q A j T) := by
  let uj : F05LocalFTCGraph A j α hT.le := ⟨(u.val j).val,(u.val j).property.1.1.1⟩
  have hValue : EqOn (F05CanonicalPull A χ α hT.le u j) (F05BCFFun (u.val j).val.1) (F05Q A j T) := by
    intro p hp
    exact F05CanonicalJetFunction_value hA hχ α hT.le u j hp.1 hp.2
  exact F05LocalFTCGraph_realization A j α hT uj (F05CanonicalPull A χ α hT.le u j) hValue
    (fun p hp => F05CanonicalJetFunction_spatial_C2 hA hχ α hT u j hp.1 hp.2)

theorem F05CanonicalJetFunction_schauder {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {χ : Fin A.count → M.Carrier → ℝ} (hχ : F05Partition O A χ)
    (α : ℝ) {T : ℝ} (hT : 0 < T) (u : F05CompatibleJetGraph A α hT.le) (j : Fin A.count) :
    SchauderBound α (F05Q A j T) (F05CanonicalPull A χ α hT.le u j) ‖(u.val j).val‖ := by
  have hReal := F05CanonicalJetFunction_realizes hA hχ α hT u j
  refine ⟨hReal.1,norm_nonneg _,?_,?_,?_⟩
  · intro p hp
    have hValue := F05CanonicalJetFunction_value hA hχ α hT.le u j hp.1 hp.2
    change F05CanonicalPull A χ α hT.le u j p = _ at hValue
    rw [hValue,hReal.2.1 hp]
    exact ⟨F05JetComponent_value_bound (u.val j).val p,F05JetComponent_gradient_bound (u.val j).val p⟩
  · exact holderBound_congr_on (F05JetComponent_hessian_holderBound (u.val j).val)
      (fun p hp => (hReal.2.2.1 hp).symm)
  · exact holderBound_congr_on (F05JetComponent_time_holderBound (u.val j).val)
      (fun p hp => (hReal.2.2.2 hp).symm)

end Yau.Proofs.F05Aux
