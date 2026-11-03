import Yau.Proofs.F05FlowSourceSolvers
import Yau.Proofs.F05FiniteManifoldData
import Yau.Proofs.F05ActualJetLinear
import Yau.Proofs.F05NestedCutoffs
import Yau.Proofs.F05SmallTime

/-! The actual native patches assemble into a genuine uniformly bounded
operator into the original compatible jet Banach space. -/

open Set
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 2800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_flow_parametrix_family {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {χ : Fin A.count → M.Carrier → ℝ} (hχ : F05Partition O A χ)
    (h : ℝ → HermitianField M) (c : M.Carrier → ℝ → ℝ)
    {S : ℝ} (hS : 0 < S) (hh : MetricFamilySmooth h (Icc 0 S))
    (hc : SmoothSpaceTime c (Icc 0 S)) (hPos : ∀ x t, t ∈ Icc 0 S → 0 < c x t)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ β γ : Fin A.count → M.Carrier → ℝ,
      (∀ j, SmoothFn (β j)) ∧ (∀ j, SmoothFn (γ j)) ∧
      (∀ j, tsupport (β j) ⊆ lift A j '' Metric.closedBall 0 (5/8)) ∧
      (∀ j, tsupport (γ j) ⊆ lift A j '' Metric.closedBall 0 (3/4)) ∧
      (∀ j z, z ∈ Metric.closedBall (0 : Space n) (1/2) → β j (lift A j z) = 1) ∧
      (∀ j z, z ∈ Metric.closedBall (0 : Space n) (5/8) → γ j (lift A j z) = 1) ∧
      ∃ δ K E C : ℝ, 0 < δ ∧ δ ≤ S ∧ δ ≤ 1 ∧ 0 < K ∧ 0 < E ∧ 0 < C ∧
        ∀ (T : ℝ) (hT : 0 < T), T ≤ δ →
          ∃ (U H : Fin A.count → F05SourceZeroGraph A α T → Point n → ℝ)
            (P : F05SourceZeroGraph A α T →L[ℝ] F05CompatibleJetGraph A α hT.le),
            F05FlowSourcePatchData A χ h c α T (Real.sqrt T) K E U H ∧ ‖P‖ ≤ C ∧
            ∀ f (i : Fin A.count) (p : F05Q A i T), ((P f).val i).val.1 p =
              pull A i (F05FiniteManifoldPatch A β (fun j => U j f)) p.val := by
  classical
  choose β γ hβ hγ hβSupport hγSupport hβOne hγOne using
    (fun j : Fin A.count => F05_nested_manifold_cutoffs hA j)
  have hSupport (j : Fin A.count) : tsupport (β j) ⊆ lift A j '' Metric.closedBall 0 (3/4) :=
    (hβSupport j).trans (image_mono (Metric.closedBall_subset_closedBall (by norm_num : (5/8 : ℝ) ≤ 3/4)))
  obtain ⟨δ,K,E,hδ,hδS,hδ1,hK,hE,hSolvers⟩ := F05_flow_source_patch_solvers hA hχ h c hS hh hc hPos hα hα1
  obtain ⟨G,hG,hGlue⟩ := F05_finite_manifold_patch_budget hA β hβ hSupport hα hα1
  let C := 2*G*K
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨β,γ,hβ,hγ,hβSupport,hγSupport,hβOne,hγOne,δ,K,E,C,hδ,hδS,hδ1,hK,hE,hC,?_⟩
  intro T hT hTδ
  have hT1 : T ≤ 1 := hTδ.trans hδ1
  obtain ⟨hρ,hρ1,hScale,hPower⟩ := F05_sqrt_scale hT hT1 α
  obtain ⟨U,H,hData⟩ := hSolvers (Real.sqrt T) T hρ hρ1 hT hTδ hScale.le
  have hε : (Real.sqrt T)^(1-α) ≤ 1 := Real.rpow_le_one hρ.le hρ1 (by linarith)
  let F (f : F05SourceZeroGraph A α T) := F05FiniteManifoldPatch A β (fun j => U j f)
  have hHigh (f : F05SourceZeroGraph A α T) (j : Fin A.count) := ((hData j).2.2.2 f).1
  have hLow (f : F05SourceZeroGraph A α T) (j : Fin A.count) := ((hData j).2.2.2 f).2.1
  have hBounds (f : F05SourceZeroGraph A α T) (i : Fin A.count) :
      SchauderBound α (F05Q A i T) (pull A i (F f)) (C*‖f‖) := by
    have hh := (hGlue T (K*‖f‖) (K*‖f‖*(Real.sqrt T)^(1-α)) (fun j => U j f)
      hT1 (mul_nonneg hK.le (norm_nonneg _)) (by positivity) (hHigh f) (hLow f) i).1
    apply schauderBound_mono_const hh
    have hSmall : K*‖f‖*(Real.sqrt T)^(1-α) ≤ K*‖f‖ :=
      mul_le_of_le_one_right (mul_nonneg hK.le (norm_nonneg _)) hε
    dsimp only [C]
    nlinarith [mul_le_mul_of_nonneg_left hSmall hG.le]
  have hPatchC2 (f : F05SourceZeroGraph A α T) (j i : Fin A.count) :
      C2 (F05Q A i T) (pull A i (F05ManifoldPatch A j (β j) (U j f))) := by
    obtain ⟨B,hB,hBudget⟩ := F05_manifold_patch_budget hA j (hβ j) (hSupport j) hα hα1
    exact (hBudget T _ _ (U j f) hT1 (hHigh f j) (hLow f j) i).1.1
  have h0 (f : F05SourceZeroGraph A α T) (x : M.Carrier) (hx : x ∈ closure O) : F f x 0 = 0 :=
    F05FiniteManifoldPatch_initial A β (fun j => ((hData j).2.2.2 f).2.2.1) x
  have hTime0 (f : F05SourceZeroGraph A α T) (i : Fin A.count) (z : Space n) (hz : z ∈ F05D A i) :
      timeD (F05Q A i T) (pull A i (F f)) (z,0) = 0 :=
    F05FiniteManifoldPatch_initial_time hA β hSupport hT.le (fun j => U j f) (hPatchC2 f)
      (fun j => ((hData j).2.2.2 f).2.2.2.2.1) i hz
  have hBoundary (f : F05SourceZeroGraph A α T) (x : M.Carrier) (hx : x ∈ frontier O)
      (t : ℝ) (ht : t ∈ Icc 0 T) : F f x t = 0 :=
    F05FiniteManifoldPatch_lateral hA β hSupport (fun j => ((hData j).2.2.2 f).2.2.2.1) hx ht
  have hAdd (f g : F05SourceZeroGraph A α T) (x : M.Carrier) (hx : x ∈ closure O)
      (t : ℝ) (ht : t ∈ Icc 0 T) : F (f+g) x t = F f x t+F g x t :=
    F05FiniteManifoldPatch_add A β U (fun j => (hData j).1) f g x ht
  have hSmul (d : ℝ) (f : F05SourceZeroGraph A α T) (x : M.Carrier) (hx : x ∈ closure O)
      (t : ℝ) (ht : t ∈ Icc 0 T) : F (d • f) x t = d*F f x t :=
    F05FiniteManifoldPatch_smul A β U (fun j => (hData j).2.1) d f x ht
  let P := F05ActualJetLinearMap hA hα hT hC.le F hBounds h0 hTime0 hBoundary hAdd hSmul
  refine ⟨U,H,P,hData,?_,?_⟩
  · apply ContinuousLinearMap.opNorm_le_bound P hC.le
    intro f
    exact F05ActualJetGraph_norm_le hA hα hT.le (F f) (hBounds f) (h0 f) (hTime0 f) (hBoundary f)
      (mul_nonneg hC.le (norm_nonneg _))
  · intro f i p
    rfl

end Yau.Proofs.F05Aux
