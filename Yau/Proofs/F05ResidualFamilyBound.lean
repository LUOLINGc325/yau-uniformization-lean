import Yau.Proofs.F05FlowSourceSolvers
import Yau.Proofs.F05NestedResidual
import Yau.Proofs.F05FiniteManifoldData

/-! The actual outer residual, including its native and cutoff pieces,
has a uniform small-factor Holder budget and zero initial slice. -/

open Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

def F05FlowOuterResidual (A : AtlasData M) (h : ℝ → HermitianField M)
    (c : M.Carrier → ℝ → ℝ) (β : Fin A.count → M.Carrier → ℝ) {α T : ℝ}
    (U H : Fin A.count → F05SourceZeroGraph A α T → Point n → ℝ)
    (i : Fin A.count) (f : F05SourceZeroGraph A α T) : Point n → ℝ :=
  F05OuterResidual (F05PrincipalExtension (F05FlowPrincipal A i h c))
    (F05DriftExtension (F05FlowDrift A i h c)) (F05ModelOuterCutoff A i (β i)) (U i f) (H i f)

theorem F05_residual_family_budget {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {χ : Fin A.count → M.Carrier → ℝ}
    (h : ℝ → HermitianField M) (c : M.Carrier → ℝ → ℝ)
    {S : ℝ} (hS : 0 < S) (hh : MetricFamilySmooth h (Icc 0 S))
    (hc : SmoothSpaceTime c (Icc 0 S)) (hPos : ∀ x t, t ∈ Icc 0 S → 0 < c x t)
    (β γ : Fin A.count → M.Carrier → ℝ) (hβ : ∀ j, SmoothFn (β j)) (hγ : ∀ j, SmoothFn (γ j))
    (hβSupport : ∀ j, tsupport (β j) ⊆ lift A j '' Metric.closedBall 0 (3/4))
    (hγSupport : ∀ j, tsupport (γ j) ⊆ lift A j '' Metric.closedBall 0 (3/4))
    {α K E : ℝ} (hα : 0 < α) (hα1 : α < 1) (hK : 0 < K) (hE : 0 < E) :
    ∃ J : ℝ, 0 < J ∧ ∀ (T ρ : ℝ), T ≤ S → 0 < ρ →
      ∀ U H : Fin A.count → F05SourceZeroGraph A α T → Point n → ℝ,
        F05FlowSourcePatchData A χ h c α T ρ K E U H → ∀ f,
          (∀ i : Fin A.count, HolderBound α (F05Q A i T)
            (pull A i (F05FiniteManifoldPatch A γ (fun j => F05FlowOuterResidual A h c β U H j f)))
            (J*‖f‖*ρ^(1-α))) ∧
          ∀ x, F05FiniteManifoldPatch A γ (fun j => F05FlowOuterResidual A h c β U H j f) x 0 = 0 := by
  classical
  obtain ⟨lam,upper,B,hB,hCoeff⟩ := F05_global_model_coefficients hA h c hS hh hc hPos hα hα1
  have hCompact (j : Fin A.count) : HasCompactSupport (F05ModelOuterCutoff A j (β j)) :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Space n) (3/4))
      ((subset_tsupport _).trans (F05ModelOuterCutoff_tsupport hA j (hβSupport j)))
  choose D hD hOuter using (fun j : Fin A.count => F05_outer_residual_budget
    (F05ModelOuterCutoff A j (β j)) (F05ModelOuterCutoff_contDiff hA j (hβ j)) (hCompact j) hα hα1 hB.le)
  let D₀ := 1+∑ j,D j
  have hSum : 0 ≤ ∑ j,D j := Finset.sum_nonneg (fun j _ => (hD j).le)
  have hD₀ : 0 < D₀ := by dsimp only [D₀]; positivity
  have hDD (j : Fin A.count) : D j ≤ D₀ := by
    have hi := Finset.single_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin A.count))) => (hD k).le)
      (Finset.mem_univ j)
    dsimp only [D₀]
    linarith
  obtain ⟨G,hG,hGlue⟩ := F05_finite_manifold_source_budget hA γ hγ hγSupport hα hα1
  let J := G*D₀*(K+E)
  refine ⟨J,by dsimp only [J]; positivity,?_⟩
  intro T ρ hTS hρ U H hData f
  have hNormPower : 0 ≤ ‖f‖*ρ^(1-α) := mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hρ.le _)
  have hModel (j : Fin A.count) :
      HolderBound α (cylinder (closure (F05ModelOpen A j)) 0 T)
        (F05FlowOuterResidual A h c β U H j f) ((D₀*(K+E))*‖f‖*ρ^(1-α)) := by
    have hInfo := (hData j).2.2.2 f
    have hCoefficients := hCoeff T hTS j
    have hLowBudget : K*‖f‖*ρ^(1-α) ≤ (K+E)*‖f‖*ρ^(1-α) := by nlinarith
    have hHBudget : E*‖f‖*ρ^(1-α) ≤ (K+E)*‖f‖*ρ^(1-α) := by nlinarith
    have hLow := holderBound_mono (holderBound_mono_const hInfo.2.1 hLowBudget)
      (show cylinder (closure (F05ModelOpen A j)) 0 T ⊆ cylinder univ 0 T from fun p hp => ⟨mem_univ _,hp.2⟩)
    have hH := holderBound_mono_const hInfo.2.2.2.2.2.2 hHBudget
    have hRaw := hOuter j (cylinder (closure (F05ModelOpen A j)) 0 T)
      (F05PrincipalExtension (F05FlowPrincipal A j h c)) (F05DriftExtension (F05FlowDrift A j h c))
      (U j f) (H j f) ((K+E)*‖f‖*ρ^(1-α)) hCoefficients.2.1 hCoefficients.2.2 hLow hH
    apply holderBound_mono_const hRaw
    calc
      D j*((K+E)*‖f‖*ρ^(1-α)) ≤ D₀*((K+E)*‖f‖*ρ^(1-α)) :=
        mul_le_mul_of_nonneg_right (hDD j) (by positivity)
      _ = (D₀*(K+E))*‖f‖*ρ^(1-α) := by ring
  refine ⟨?_,?_⟩
  · intro i
    have h := hGlue T ((D₀*(K+E))*‖f‖*ρ^(1-α))
      (fun j => F05FlowOuterResidual A h c β U H j f) (by positivity) hModel i
    convert h using 1
    dsimp only [J]
    ring
  · apply F05FiniteManifoldPatch_initial A γ
    intro j z
    exact F05OuterResidual_initial _ _ _ _ _ ((hData j).2.2.2 f).2.2.1 ((hData j).2.2.1 f) z

end Yau.Proofs.F05Aux
