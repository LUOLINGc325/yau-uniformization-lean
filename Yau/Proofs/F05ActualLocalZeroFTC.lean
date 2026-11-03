import Yau.Proofs.F05ActualLocalFTC
import Yau.Proofs.F05JetZeroData

/-! Genuine homogeneous traces of a function give membership in the actual
zero-data FTC graph; no artificial rim condition is imposed. -/

open Set
open scoped Topology
noncomputable section
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05ActualJetComponent_mem_zeroFTC (A : AtlasData M) (i : Fin A.count)
    {α C T : ℝ} (hα : 0 < α) (hT : 0 ≤ T) {v : Point n → ℝ}
    (hv : SchauderBound α (F05Q A i T) v C)
    (h0 : ∀ z ∈ F05D A i, v (z,0) = 0)
    (hTime0 : ∀ z ∈ F05D A i, timeD (F05Q A i T) v (z,0) = 0)
    (hBoundary : ∀ z ∈ F05D A i, ∀ t ∈ Icc 0 T, ∀ j : RIdx n,
      A.normal i = some j → realCoord z j = 0 → v (z,t) = 0) :
    F05ActualJetComponent hα hv ∈ F05LocalZeroFTCGraph A i α hT := by
  change ((F05ActualJetComponent hα hv ∈ F05LocalFTCGraph A i α hT ∧
    F05ActualJetComponent hα hv ∈ F05LocalInitialValueGraph A i α hT) ∧
    F05ActualJetComponent hα hv ∈ F05LocalInitialTimeGraph A i α hT) ∧
    F05ActualJetComponent hα hv ∈ F05LocalLateralGraph A i α T
  refine ⟨⟨⟨F05ActualJetComponent_mem_FTC A i hα hT hv,?_⟩,?_⟩,?_⟩
  · apply (Submodule.mem_iInf _).mpr
    intro z
    change v (z.val,0) = 0
    exact h0 z.val z.property
  · apply (Submodule.mem_iInf _).mpr
    intro z
    change timeD (F05Q A i T) v (z.val,0) = 0
    exact hTime0 z.val z.property
  · simp only [F05LocalLateralGraph,Submodule.mem_iInf,LinearMap.mem_ker]
    intro z t j hν hz
    change v (z.val,t.val) = 0
    exact hBoundary z.val z.property t.val t.property j hν hz

def F05ActualLocalZeroFTC (A : AtlasData M) (i : Fin A.count)
    {α C T : ℝ} (hα : 0 < α) (hT : 0 ≤ T) {v : Point n → ℝ}
    (hv : SchauderBound α (F05Q A i T) v C)
    (h0 : ∀ z ∈ F05D A i, v (z,0) = 0)
    (hTime0 : ∀ z ∈ F05D A i, timeD (F05Q A i T) v (z,0) = 0)
    (hBoundary : ∀ z ∈ F05D A i, ∀ t ∈ Icc 0 T, ∀ j : RIdx n,
      A.normal i = some j → realCoord z j = 0 → v (z,t) = 0) :
    F05LocalZeroFTCGraph A i α hT :=
  ⟨F05ActualJetComponent hα hv,F05ActualJetComponent_mem_zeroFTC A i hα hT hv h0 hTime0 hBoundary⟩

theorem F05ActualLocalZeroFTC_norm_le (A : AtlasData M) (i : Fin A.count)
    {α C T : ℝ} (hα : 0 < α) (hT : 0 ≤ T) {v : Point n → ℝ}
    (hv : SchauderBound α (F05Q A i T) v C)
    (h0 : ∀ z ∈ F05D A i, v (z,0) = 0)
    (hTime0 : ∀ z ∈ F05D A i, timeD (F05Q A i T) v (z,0) = 0)
    (hBoundary : ∀ z ∈ F05D A i, ∀ t ∈ Icc 0 T, ∀ j : RIdx n,
      A.normal i = some j → realCoord z j = 0 → v (z,t) = 0) :
    ‖F05ActualLocalZeroFTC A i hα hT hv h0 hTime0 hBoundary‖ ≤ C :=
  F05ActualJetComponent_norm_le hα hv

end Yau.Proofs.F05Aux
