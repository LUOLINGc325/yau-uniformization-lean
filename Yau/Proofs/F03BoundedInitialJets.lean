import Yau.Proofs.F03FarInitialJets
import Yau.Proofs.F03MinimalCompactHeatClass
import Yau.Proofs.F03BoundedKernelSplit
import Yau.Proofs.F04SupportedCutoff

/-! The original same-kernel bounded smooth evolution has every literal compact spatial initial jet. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff
namespace Yau.Proofs.F03Aux
open Yau Blueprint HeatConcreteBindings HeatTargetCandidates LeafProofs.L18Aux LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2500000

theorem dirichletMinimalBoundedHeat_smooth_initial
    (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : ℕ → Set M.Carrier) (hO : SmoothExhaustion O)
    (f : M.Carrier → ℝ) (hf : SmoothFn f) (hBounded : ∃ C : ℝ,∀ y,|f y| ≤ C) :
    ScalarSmoothInitial
      (boundedKernelEvolution μ (dirichletMinimalKernelCandidate g hK μ hμ O hO) f) f := by
  have hfa : AEStronglyMeasurable f μ := (continuous_of_smoothFn hf).aestronglyMeasurable
  obtain ⟨C0,hC0⟩ := hBounded
  let B := max 1 C0
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hBound : ∀ y,|f y| ≤ B := fun y => (hC0 y).trans (le_max_right _ _)
  refine ⟨?_,?_⟩
  · funext y
    simp [boundedKernelEvolution]
  · intro a K hKc hKt m ε hε
    have hImage : IsCompact (chartInv a '' K) := hKc.image_of_continuousOn
      ((continuousOn_extChartAt_symm (I := ComplexModel n) a).mono hKt)
    obtain ⟨η,W,hηs,hηc,_hηSupp,hW,hImageW,_hWU,hηone,hηrange⟩ :=
      F04Proof.exists_supported_smooth_cutoff (chartInv a '' K) univ hImage isOpen_univ (subset_univ _)
    let eta : ScalarEnergyDomain g μ hμ := ⟨η,hηs,hηc⟩
    let k : ScalarEnergyDomain g μ hμ := ⟨fun y => η y*f y,smoothFn_mul hηs hf,hηc.mul_right⟩
    have hKW : ∀ z ∈ K,chartInv a z ∈ W := fun z hz => hImageW ⟨z,hz,rfl⟩
    have hHalf : 0 < ε/2 := half_pos hε
    obtain ⟨δC,hδC,hCloseC⟩ :=
      (dirichletMinimalBoundedHeat_compact_smooth_initial g hK μ hμ O hO k).2 a K hKc hKt m (ε/2) hHalf
    obtain ⟨δF,hδF,hCloseF⟩ := dirichletMinimalBoundedHeat_far_initial_jets g hK μ hμ O hO
      f hfa B hB hBound eta hηrange W hW hηone a K hKc hKt hKW m (ε/2) hHalf
    refine ⟨min δC δF,lt_min hδC hδF,fun t ht htd z hz => ?_⟩
    let A : ComplexVector n → ℝ := fun w =>
      boundedKernelEvolution μ (dirichletMinimalKernelCandidate g hK μ hμ O hO) (fun y => k y) t
        (chartInv a w)-k (chartInv a w)
    let D : ComplexVector n → ℝ := fun w =>
      boundedKernelEvolution μ (dirichletMinimalKernelCandidate g hK μ hμ O hO)
        (fun y => (1-η y)*f y) t (chartInv a w)
    have hSmallA : ‖iteratedFDeriv ℝ m A z‖ < ε/2 :=
      hCloseC t ht (htd.trans_le (min_le_left _ _)) z hz
    have hSmallD : ‖iteratedFDeriv ℝ m D z‖ < ε/2 :=
      hCloseF t ht (htd.trans_le (min_le_right _ _)) z hz
    have hSplit := dirichletMinimalBoundedHeat_cutoff_split g hK μ hμ O hO f hfa B hBound eta hηrange ht.le
    let R0 := {w | w ∈ chartTarget a ∧ chartInv a w ∈ W}
    have hR0 : IsOpen R0 := dirichletChartInterior_open W hW a
    have hzR0 : z ∈ R0 := ⟨hKt hz,hKW z hz⟩
    have hGerm : (fun w => inChart a
        (boundedKernelEvolution μ (dirichletMinimalKernelCandidate g hK μ hμ O hO) f t) w-inChart a f w)
        =ᶠ[𝓝 z] (fun w => A w+D w) := by
      filter_upwards [hR0.mem_nhds hzR0] with w hw
      have hInitial : k (chartInv a w)=f (chartInv a w) := by
        change η (chartInv a w)*f (chartInv a w)=f (chartInv a w)
        rw [hηone _ hw.2,one_mul]
      have hS : boundedKernelEvolution μ (dirichletMinimalKernelCandidate g hK μ hμ O hO) f t (chartInv a w)=
          boundedKernelEvolution μ (dirichletMinimalKernelCandidate g hK μ hμ O hO) (fun y => k y) t (chartInv a w)+D w :=
        congrFun hSplit (chartInv a w)
      change boundedKernelEvolution μ (dirichletMinimalKernelCandidate g hK μ hμ O hO) f t (chartInv a w)-
        f (chartInv a w)=A w+D w
      dsimp only [A]
      linarith
    have hCompactSmooth := (dirichletMinimalBoundedHeat_compact_class g hK μ hμ O hO k).1
    have hAC : ContDiffAt ℝ ∞ A z :=
      ((smoothFn_sub (smoothFn_of_smoothSpaceTime hCompactSmooth ht) k.2.1) a).contDiffAt
        ((isOpen_extChartAt_target (I := ComplexModel n) a).mem_nhds (hKt hz))
    have hFarSmooth := (dirichletMinimalBoundedHeat_far_source g hK μ hμ O hO f hfa B hB hBound eta hηrange).1
    have hDC : ContDiffAt ℝ ∞ D z :=
      (smoothFn_of_smoothSpaceTime hFarSmooth ht a).contDiffAt
        ((isOpen_extChartAt_target (I := ComplexModel n) a).mem_nhds (hKt hz))
    have hAdd : iteratedFDeriv ℝ m (fun w => A w+D w) z=
        iteratedFDeriv ℝ m A z+iteratedFDeriv ℝ m D z :=
      iteratedFDeriv_add_apply (hAC.of_le (by simp)) (hDC.of_le (by simp))
    have hTensor := ((hGerm.iteratedFDeriv ℝ m).eq_of_nhds).trans hAdd
    exact ((congrArg norm hTensor).trans_le (norm_add_le _ _)).trans_lt (by linarith)

end Yau.Proofs.F03Aux
