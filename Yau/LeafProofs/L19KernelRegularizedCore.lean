import Yau.LeafProofs.L19HeatClassicalCore
import Yau.LeafProofs.L19HeatFixedSlabDuality

/-! The actual regularized backward tests for original kernel identification. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold Matrix ComplexOrder
namespace Yau.LeafProofs.L19Aux
open L12Aux L18Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

def scalarCoreBackwardTest (hn : 0 < n) (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (k : ScalarEnergyDomain g μ hμ) (T ε : ℝ) : M.Carrier → ℝ → ℝ :=
  fun x s => scalarClassicalHeat hn g hK μ hμ (scalarEnergyDomainL2 g μ hμ k) x (T + ε - s)

theorem scalarCoreBackwardTest_smooth (hn : 0 < n) (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (k : ScalarEnergyDomain g μ hμ) (T ε : ℝ) :
    SmoothSpaceTime (scalarCoreBackwardTest hn g hK μ hμ k T ε) (Iio (T + ε)) :=
  LocalTime.smoothSpaceTime_timeReverse
    (scalarClassicalHeat_smooth hn g hK μ hμ (scalarEnergyDomainL2 g μ hμ k)) (T + ε)

theorem scalarCoreBackwardTest_hasDerivAt (hn : 0 < n) (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (k : ScalarEnergyDomain g μ hμ) (T ε : ℝ) (x : M.Carrier) {s : ℝ} (hs : s < T + ε) :
    HasDerivAt (scalarCoreBackwardTest hn g hK μ hμ k T ε x)
      (-laplacian g.form (fun y => scalarCoreBackwardTest hn g hK μ hμ k T ε y s) x) s :=
  LocalTime.scalarHeat_timeReverse_hasDerivAt g
    (fun y _t ht => scalarClassicalHeat_hasDerivAt hn g hK μ hμ (scalarEnergyDomainL2 g μ hμ k) y ht)
    (T + ε) x hs

/-- The Gaussian tail of each true backward compact test holds uniformly
including the trace time zero. -/
theorem scalarCoreBackwardTest_gaussian_tail (hn : 0 < n) (g : SmoothMetric M)
    (hcomplete : IsComplete g) (hK : IsKahler g) (hRic : ∀ x, (ricci g.form x).PosSemidef)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (k : ScalarEnergyDomain g μ hμ) (o : M.Carrier) {T ε : ℝ} (hT : 0 < T) (hε : 0 < ε) :
    ∃ C β : ℝ, 0 < C ∧ 0 < β ∧ ∀ x s, s ∈ Icc (0 : ℝ) T →
      |scalarCoreBackwardTest hn g hK μ hμ k T ε x s| ≤ C * Real.exp (-β * inducedDistance g.form o x ^ 2) := by
  obtain ⟨C, β, hC, hβ, htail⟩ := scalarClassicalCompactHeat_tail hn g hcomplete hK hRic μ hμ k o hε
    (show ε ≤ T + ε by linarith)
  refine ⟨C, β, hC, hβ, ?_⟩
  intro x s hs
  exact htail x (T + ε - s) ⟨by linarith [hs.2], by linarith [hs.1]⟩

/-- Before using any initial trace or mass result, the original kernel
pairs constantly with the internally constructed backward compact test. -/
theorem scalarHeatKernel_regularized_core_duality (hn : 0 < n) (g : SmoothMetric M)
    (hcomplete : IsComplete g) (hK : IsKahler g) (hRic : ∀ x, (ricci g.form x).PosSemidef)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {H : ℝ → M.Carrier → M.Carrier → ℝ} (hH : LeafCandidates.ScalarHeatKernel g.form μ H)
    (k : ScalarEnergyDomain g μ hμ) (y : M.Carrier) {T ε s : ℝ}
    (hT : 0 < T) (hε : 0 < ε) (hs : 0 < s) (hsT : s ≤ T) :
    Integrable (fun x => H s x y * scalarCoreBackwardTest hn g hK μ hμ k T ε x s) μ ∧
    Integrable (fun x => H T x y * scalarClassicalHeat hn g hK μ hμ
      (scalarEnergyDomainL2 g μ hμ k) x ε) μ ∧
    (∫ x, H s x y * scalarCoreBackwardTest hn g hK μ hμ k T ε x s ∂μ) =
      ∫ x, H T x y * scalarClassicalHeat hn g hK μ hμ (scalarEnergyDomainL2 g μ hμ k) x ε ∂μ := by
  let v := scalarCoreBackwardTest hn g hK μ hμ k T ε
  have hv : SmoothSpaceTime v (Ioo 0 (T + ε)) := fun a =>
    (scalarCoreBackwardTest_smooth hn g hK μ hμ k T ε a).mono (fun p hp => ⟨hp.1, hp.2.2⟩)
  obtain ⟨C, β, hC, hβ, htail⟩ := scalarCoreBackwardTest_gaussian_tail hn g hcomplete hK hRic μ hμ k y hT hε
  have hslab : Icc s T ⊆ Ioo 0 (T + ε) := by
    intro t ht
    exact ⟨hs.trans_le ht.1, by linarith [ht.2]⟩
  obtain ⟨his, hiT, heq⟩ := positiveHeatSolution_gaussian_backward_duality g hcomplete hK hRic μ hμ (hH.1 y)
    isOpen_Ioo (fun _ ht => ht.1) hv
    (fun x t ht => scalarCoreBackwardTest_hasDerivAt hn g hK μ hμ k T ε x ht.2)
    y hs hslab hsT hC hβ (fun x t ht => htail x t ⟨hs.le.trans ht.1, ht.2⟩)
  dsimp only [v, scalarCoreBackwardTest] at hiT heq
  rw [show T + ε - T = ε by ring] at hiT heq
  exact ⟨his, hiT, heq.symm⟩

end Yau.LeafProofs.L19Aux
