import Yau.Proofs.F05ParametrixFamily
import Yau.Proofs.F05ParametrixErrorNorm
import Yau.Proofs.F05BoundedJetOperator
import Yau.Proofs.F05Neumann

/-! The literal finite parametrix and its actual small operator error give
a genuine uniformly bounded right inverse of the original manifold operator. -/

open Set
noncomputable section
set_option maxHeartbeats 2800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_linear_right_inverse {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {χ : Fin A.count → M.Carrier → ℝ} (hχ : F05Partition O A χ)
    (h : ℝ → HermitianField M) (c : M.Carrier → ℝ → ℝ)
    {S : ℝ} (hS : 0 < S) (hh : MetricFamilySmooth h (Icc 0 S))
    (hc : SmoothSpaceTime c (Icc 0 S)) (hPos : ∀ x t, t ∈ Icc 0 S → 0 < c x t)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ δ CL CB : ℝ, 0 < δ ∧ δ ≤ S ∧ δ ≤ 1 ∧ 0 < CL ∧ 0 < CB ∧
      ∀ (T : ℝ) (hT : 0 < T), T ≤ δ →
        ∃ (L : F05CompatibleJetGraph A α hT.le →L[ℝ] F05SourceZeroGraph A α T)
          (B : F05SourceZeroGraph A α T →L[ℝ] F05CompatibleJetGraph A α hT.le),
          ‖L‖ ≤ CL ∧ ‖B‖ ≤ CB ∧ L.comp B = ContinuousLinearMap.id ℝ (F05SourceZeroGraph A α T) ∧
          ∀ u (i : Fin A.count) (p : F05Q A i T),
            holderGraphFun ((L u).val i) p.val = F05JetOperator A c h α hT.le u i p.val := by
  obtain ⟨β,γ,hβ,hγ,hβSupport,hγSupport,hβOne,hγOne,δ,K,E,CP,
    hδ,hδS,hδ1,hK,hE,hCP,hFamily⟩ := F05_flow_parametrix_family hA hχ h c hS hh hc hPos hα hα1
  have hβ75 (j : Fin A.count) : tsupport (β j) ⊆ lift A j '' Metric.closedBall 0 (3/4) :=
    (hβSupport j).trans (image_mono (Metric.closedBall_subset_closedBall (by norm_num : (5/8 : ℝ) ≤ 3/4)))
  obtain ⟨J,hJ,hResidual⟩ := F05_residual_family_budget hA (χ := χ) h c hS hh hc hPos
    β γ hβ hγ hβ75 hγSupport hα hα1 hK hE
  obtain ⟨CL,hCL,hOperators⟩ := F05_bounded_jet_operator hA hχ h c hS hh hc hα hα1
  obtain ⟨δ₀,hδ₀,hδ₀δ,hδ₀1,hSmall⟩ := F05_uniform_small_time hα1 hJ hδ
  refine ⟨δ₀,CL,2*CP,hδ₀,hδ₀δ.trans hδS,hδ₀1,hCL,by positivity,?_⟩
  intro T hT hTδ
  have hTOld : T ≤ δ := hTδ.trans hδ₀δ
  have hTS : T ≤ S := hTOld.trans hδS
  have hT1 : T ≤ 1 := hTδ.trans hδ₀1
  obtain ⟨U,H,P,hData,hP,hPValue⟩ := hFamily T hT hTOld
  obtain ⟨L,hL,hLValue⟩ := hOperators T hT hTS hT1
  obtain ⟨hρ,hρ1,hScale,hPower⟩ := F05_sqrt_scale hT hT1 α
  have hRHolder (f : F05SourceZeroGraph A α T) (i : Fin A.count) :=
    (hResidual T (Real.sqrt T) hTS hρ U H hData f).1 i
  have hError := F05_parametrix_error_norm hA hχ h c β γ hβ hβSupport hγSupport
    hβOne hγOne hα hα1 hT hT1 hρ hJ.le U H hData L P hLValue hPValue hRHolder
  have hQuarter : ‖ContinuousLinearMap.id ℝ (F05SourceZeroGraph A α T)-L.comp P‖ ≤ (1/4 : ℝ) := by
    apply hError.trans
    rw [hPower]
    exact hSmall T hT hTδ
  let Q := L.comp P-ContinuousLinearMap.id ℝ (F05SourceZeroGraph A α T)
  have hQ : ‖Q‖ ≤ (1/4 : ℝ) := by
    have hEq : Q = -(ContinuousLinearMap.id ℝ (F05SourceZeroGraph A α T)-L.comp P) := by
      dsimp only [Q]
      abel
    rw [hEq,norm_neg]
    exact hQuarter
  obtain ⟨N,hLN,hNL,hN⟩ := neumann_inverse Q hQ
  have hIdentity : ContinuousLinearMap.id ℝ (F05SourceZeroGraph A α T)+Q = L.comp P := by
    dsimp only [Q]
    abel
  rw [hIdentity] at hLN hNL
  let B := P.comp N
  refine ⟨L,B,hL,?_,?_,hLValue⟩
  · calc
      ‖B‖ ≤ ‖P‖*‖N‖ := ContinuousLinearMap.opNorm_comp_le P N
      _ ≤ CP*2 := mul_le_mul hP hN (norm_nonneg _) hCP.le
      _ = 2*CP := by ring
  · change L.comp (P.comp N) = _
    rw [← ContinuousLinearMap.comp_assoc]
    exact hLN

end Yau.Proofs.F05Aux
