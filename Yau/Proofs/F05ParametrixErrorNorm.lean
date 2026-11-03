import Yau.Proofs.F05ParametrixEquation
import Yau.Proofs.F05FlowFiniteRegularity
import Yau.Proofs.F05JetOperatorRealization

/-! The actual global PDE identity identifies the literal Banach operator
error with its complete small-factor residual. -/

open Set
noncomputable section
set_option maxHeartbeats 2600000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_holderGraphFun_sub {α : ℝ} {Q : Set (Point n)}
    (u v : holderGraph α Q) (p : Point n) :
    holderGraphFun (u-v) p = holderGraphFun u p-holderGraphFun v p := by
  classical
  by_cases hp : p ∈ Q <;> simp [holderGraphFun,hp]

theorem F05_parametrix_error_norm {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {χ : Fin A.count → M.Carrier → ℝ} (hχ : F05Partition O A χ)
    (h : ℝ → HermitianField M) (c : M.Carrier → ℝ → ℝ)
    (β γ : Fin A.count → M.Carrier → ℝ) (hβ : ∀ j, SmoothFn (β j))
    (hβSupport : ∀ j, tsupport (β j) ⊆ lift A j '' Metric.closedBall 0 (5/8))
    (hγSupport : ∀ j, tsupport (γ j) ⊆ lift A j '' Metric.closedBall 0 (3/4))
    (hβOne : ∀ j z, z ∈ Metric.closedBall (0 : Space n) (1/2) → β j (lift A j z) = 1)
    (hγOne : ∀ j z, z ∈ Metric.closedBall (0 : Space n) (5/8) → γ j (lift A j z) = 1)
    {α T ρ K E J : ℝ} (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1)
    (hρ : 0 < ρ) (hJ : 0 ≤ J)
    (U H : Fin A.count → F05SourceZeroGraph A α T → Point n → ℝ)
    (hData : F05FlowSourcePatchData A χ h c α T ρ K E U H)
    (L : F05CompatibleJetGraph A α hT.le →L[ℝ] F05SourceZeroGraph A α T)
    (P : F05SourceZeroGraph A α T →L[ℝ] F05CompatibleJetGraph A α hT.le)
    (hLValue : ∀ u i (p : F05Q A i T), holderGraphFun ((L u).val i) p.val = F05JetOperator A c h α hT.le u i p.val)
    (hPValue : ∀ f i (p : F05Q A i T), ((P f).val i).val.1 p =
      pull A i (F05FiniteManifoldPatch A β (fun j => U j f)) p.val)
    (hRHolder : ∀ f i, HolderBound α (F05Q A i T)
      (pull A i (F05FiniteManifoldPatch A γ (fun j => F05FlowOuterResidual A h c β U H j f)))
        (J*‖f‖*ρ^(1-α))) :
    ‖ContinuousLinearMap.id ℝ (F05SourceZeroGraph A α T)-L.comp P‖ ≤ J*ρ^(1-α) := by
  have hβ75 (j : Fin A.count) : tsupport (β j) ⊆ lift A j '' Metric.closedBall 0 (3/4) :=
    (hβSupport j).trans (image_mono (Metric.closedBall_subset_closedBall (by norm_num : (5/8 : ℝ) ≤ 3/4)))
  let R := ContinuousLinearMap.id ℝ (F05SourceZeroGraph A α T)-L.comp P
  have hValue (f : F05SourceZeroGraph A α T) (i : Fin A.count) (p : F05Q A i T) :
      holderGraphFun ((R f).val i) p.val =
        pull A i (F05FiniteManifoldPatch A γ (fun j => F05FlowOuterResidual A h c β U H j f)) p.val := by
    have hReg := F05_flow_finite_patch_C2 hA h c β hβ hβ75 hα hα1 hT1 U H hData f
    have hJet := F05JetOperator_eq_intrinsic_of_values hA h c α hT (P f)
      (F05FiniteManifoldPatch A β (fun j => U j f)) hReg (hPValue f) i (p := p.val) p.property
    have hEquation := F05_global_parametrix_equation hA hχ h c β γ hβ hβSupport hγSupport
      hβOne hγOne hα hα1 hT1 U H hData f (F05D_lift_mem_closure hA p.property.1) p.property.2
    have hSource := F05SourceZeroFun_pull f i p.val.1 p.property.1 p.val.2 p.property.2
    change holderGraphFun (f.val i-(L (P f)).val i) p.val = _
    rw [F05_holderGraphFun_sub,hLValue (P f) i p,hJet,hEquation,hSource]
    unfold pull
    ring
  apply ContinuousLinearMap.opNorm_le_bound R (mul_nonneg hJ (Real.rpow_nonneg hρ.le _))
  intro f
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (mul_nonneg hJ (Real.rpow_nonneg hρ.le _)) (norm_nonneg f))).mpr
  intro i
  apply holderGraph_norm_le_of_holderBound ((R f).val i)
  have hBound := holderBound_congr_on (hRHolder f i) (fun p hp => (hValue f i ⟨p,hp⟩).symm)
  convert hBound using 1
  ring

end Yau.Proofs.F05Aux
