import Yau.Proofs.F05LinearRightInverse
import Yau.Proofs.F05LinearUniqueness

/-! The actual original manifold operator has a two-sided bounded inverse.
All time and norm constants precede the endpoint and all sources. -/

open Set
noncomputable section
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_linear_inverse {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {χ : Fin A.count → M.Carrier → ℝ} (hχ : F05Partition O A χ)
    (h : ℝ → HermitianField M) (c : M.Carrier → ℝ → ℝ)
    {S : ℝ} (hS : 0 < S) (hh : MetricFamilySmooth h (Icc 0 S))
    (hc : SmoothSpaceTime c (Icc 0 S)) (hPos : ∀ x t, t ∈ Icc 0 S → 0 < c x t)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ δ CL CB : ℝ, 0 < δ ∧ δ ≤ S ∧ δ ≤ 1 ∧ 0 < CL ∧ 0 < CB ∧
      ∀ (T : ℝ) (hT : 0 < T), T ≤ δ →
        ∃ (L : F05CompatibleJetGraph A α hT.le →L[ℝ] F05SourceZeroGraph A α T)
          (B : F05SourceZeroGraph A α T →L[ℝ] F05CompatibleJetGraph A α hT.le),
          ‖L‖ ≤ CL ∧ ‖B‖ ≤ CB ∧
          L.comp B = ContinuousLinearMap.id ℝ (F05SourceZeroGraph A α T) ∧
          B.comp L = ContinuousLinearMap.id ℝ (F05CompatibleJetGraph A α hT.le) ∧
          ∀ u (i : Fin A.count) (p : F05Q A i T),
            holderGraphFun ((L u).val i) p.val = F05JetOperator A c h α hT.le u i p.val := by
  obtain ⟨δ,CL,CB,hδ,hδS,hδ1,hCL,hCB,hFamily⟩ :=
    F05_linear_right_inverse hA hχ h c hS hh hc hPos hα hα1
  obtain ⟨lam,upper,hEll⟩ := F05_linear_coefficients_elliptic_uniform hA h c hS hh hc hPos
  refine ⟨δ,CL,CB,hδ,hδS,hδ1,hCL,hCB,?_⟩
  intro T hT hTδ
  obtain ⟨L,B,hL,hB,hLB,hLValue⟩ := hFamily T hT hTδ
  have hEllQ (i : Fin A.count) : Elliptic (F05Q A i T) (F05FlowPrincipal A i h c) lam upper :=
    ⟨(hEll T (hTδ.trans hδS) i).1,(hEll T (hTδ.trans hδS) i).2.1,
      fun p hp => (hEll T (hTδ.trans hδS) i).2.2 p
        ⟨(by simpa only [Metric.mem_closedBall,dist_zero_right] using hp.1.1),hp.2⟩⟩
  have hInj := F05_linear_operator_injective hA hχ h c hT hEllQ L hLValue
  refine ⟨L,B,hL,hB,hLB,?_,hLValue⟩
  apply ContinuousLinearMap.ext
  intro u
  apply hInj
  have hAt := DFunLike.congr_fun hLB (L u)
  exact hAt

end Yau.Proofs.F05Aux
