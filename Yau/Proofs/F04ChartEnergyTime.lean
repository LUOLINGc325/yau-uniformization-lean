import Yau.Proofs.F04ChartEnergyTest
import Yau.Proofs.F04SupportedProfileDerivative
import Yau.LeafProofs.L16EnergyEquation

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace
noncomputable section
namespace Yau.F04Proof
open Yau.Blueprint Yau.Parabolic Yau.Proofs.F03Aux Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

local instance (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (Ω : Set M.Carrier) :
    CompleteSpace (DirichletEnergy g μ hμ Ω) := dirichletEnergy_completeSpace g μ hμ Ω

theorem chartSupportedTestCore_contDiffOn_one
    (g : SmoothMetric M) (hg : IsKahler g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (Ω K : Set M.Carrier)
    (hΩ : MeasurableSet Ω) (hK : IsCompact K) (hΩK : Ω ⊆ K)
    (c : M.Carrier) {O : Set (Space n)} (hOt : O ⊆ chartTarget c)
    (hMap : chartInv c '' O ⊆ Ω) {S : ℝ} (hS : 0 < S)
    {φ : Point n → ℝ} (hφ : Test (O ×ˢ Ioo 0 S) φ) :
    ContDiffOn ℝ 1 (fun t => dirichletCoreToEnergy g μ hμ Ω
      (chartSupportedTestCore g μ hμ Ω c hOt hMap hφ t)) (Icc 0 S) ∧
      ∀ t ∈ Icc 0 S, HasDerivWithinAt
        (fun s => dirichletCoreToEnergy g μ hμ Ω (chartSupportedTestCore g μ hμ Ω c hOt hMap hφ s))
        (dirichletCoreToEnergy g μ hμ Ω
          (chartSupportedTestCore g μ hμ Ω c hOt hMap (test_timeDerivative hφ) t)) (Icc 0 S) t := by
  let v : M.Carrier → ℝ → ℝ := fun y t => Yau.LeafProofs.L18Aux.chartPushforwardZero c (fun z => φ (z, t)) y
  let ψ : Point n → ℝ := fun p => deriv (fun t => φ (p.1, t)) p.2
  have hψ : Test (O ×ˢ Ioo 0 S) ψ := test_timeDerivative hφ
  let w : M.Carrier → ℝ → ℝ := fun y t => Yau.LeafProofs.L18Aux.chartPushforwardZero c (fun z => ψ (z, t)) y
  have hv : SmoothSpaceTime v (Icc 0 S) := fun b =>
    (chartPushforwardZero_smoothSpaceTime c hOt hφ b).mono (prod_mono (Subset.refl _) (subset_univ _))
  have hw : SmoothSpaceTime w (Icc 0 S) := fun b =>
    (chartPushforwardZero_smoothSpaceTime c hOt hψ b).mono (prod_mono (Subset.refl _) (subset_univ _))
  obtain ⟨Kv, hKv, hKvΩ, hSuppv⟩ := chartPushforwardZero_spacetime_support c hOt hMap hφ
  obtain ⟨Kw, hKw, hKwΩ, hSuppw⟩ := chartPushforwardZero_spacetime_support c hOt hMap hψ
  have hcv (t : ℝ) (_ht : t ∈ Icc 0 S) : HasCompactSupport (v · t) :=
    hKv.of_isClosed_subset (isClosed_tsupport _) (hSuppv t)
  have hSv (t : ℝ) (_ht : t ∈ Icc 0 S) : tsupport (v · t) ⊆ Ω := (hSuppv t).trans hKvΩ
  have hcw (t : ℝ) (_ht : t ∈ Icc 0 S) : HasCompactSupport (w · t) :=
    hKw.of_isClosed_subset (isClosed_tsupport _) (hSuppw t)
  have hSw (t : ℝ) (_ht : t ∈ Icc 0 S) : tsupport (w · t) ⊆ Ω := (hSuppw t).trans hKwΩ
  have hd (y : M.Carrier) (t : ℝ) (_ht : t ∈ Icc 0 S) :
      HasDerivWithinAt (v y) (w y t) (Icc 0 S) t :=
    (chartPushforwardZero_spacetime_hasDerivAt c hφ.1 t y).hasDerivWithinAt
  have hc := supportedProfileCore_contDiffOn_one g hg μ hμ Ω K hΩ hK hΩK hS v w hv hw hcv hSv hcw hSw hd
  let V := fun t => dirichletCoreToEnergy g μ hμ Ω (chartSupportedTestCore g μ hμ Ω c hOt hMap hφ t)
  let W := fun t => dirichletCoreToEnergy g μ hμ Ω (chartSupportedTestCore g μ hμ Ω c hOt hMap hψ t)
  have hEqV (t : ℝ) (ht : t ∈ Icc 0 S) : V t =
      dirichletCoreToEnergy g μ hμ Ω (supportedProfileCore g μ hμ Ω hS v hv hcv hSv t) := by
    apply congrArg (dirichletCoreToEnergy g μ hμ Ω)
    apply Subtype.ext
    apply Subtype.ext
    funext y
    change Yau.LeafProofs.L18Aux.chartPushforwardZero c (fun z => φ (z, t)) y =
      Yau.LeafProofs.L18Aux.chartPushforwardZero c (fun z => φ (z, timeClamp S hS.le t)) y
    rw [timeClamp_eq_of_mem S hS.le ht]
  have hEqW (t : ℝ) (ht : t ∈ Icc 0 S) : W t =
      dirichletCoreToEnergy g μ hμ Ω (supportedProfileCore g μ hμ Ω hS w hw hcw hSw t) := by
    apply congrArg (dirichletCoreToEnergy g μ hμ Ω)
    apply Subtype.ext
    apply Subtype.ext
    funext y
    change Yau.LeafProofs.L18Aux.chartPushforwardZero c (fun z => ψ (z, t)) y =
      Yau.LeafProofs.L18Aux.chartPushforwardZero c (fun z => ψ (z, timeClamp S hS.le t)) y
    rw [timeClamp_eq_of_mem S hS.le ht]
  change ContDiffOn ℝ 1 V (Icc 0 S) ∧ ∀ t ∈ Icc 0 S, HasDerivWithinAt V (W t) (Icc 0 S) t
  refine ⟨hc.1.congr hEqV, ?_⟩
  intro t ht
  have hh := hc.2 t ht
  change HasDerivWithinAt
    (fun s => dirichletCoreToEnergy g μ hμ Ω (supportedProfileCore g μ hμ Ω hS v hv hcv hSv s))
    (dirichletCoreToEnergy g μ hμ Ω (supportedProfileCore g μ hμ Ω hS w hw hcw hSw t)) (Icc 0 S) t at hh
  rw [← hEqW t ht] at hh
  exact hh.congr_of_mem hEqV ht

end Yau.F04Proof
