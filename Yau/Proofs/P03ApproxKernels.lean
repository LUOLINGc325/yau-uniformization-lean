import Yau.Proofs.P03Convolution

open scoped Topology ContDiff Convolution
open MeasureTheory Filter

noncomputable section

namespace Yau.NodeProofs.P03Aux

variable {n : ℕ}

def approxRadius (r : ℝ) (j : ℕ) : ℝ := r / ((j : ℝ) + 2)

theorem approxRadius_pos {r : ℝ} (hr : 0 < r) (j : ℕ) : 0 < approxRadius r j :=
  div_pos hr (by positivity)

theorem approxRadius_le {r : ℝ} (hr : 0 < r) (j : ℕ) : approxRadius r j ≤ r := by
  apply div_le_self hr.le
  have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
  linarith

theorem approxRadius_tendsto (r : ℝ) : Tendsto (approxRadius r) atTop (𝓝 0) := by
  have h := (tendsto_add_atTop_iff_nat 2).mpr (tendsto_const_div_atTop_nhds_zero_nat r)
  change Tendsto (fun j : ℕ => r / ((j : ℝ) + 2)) atTop (𝓝 0)
  simpa only [Nat.cast_add, Nat.cast_ofNat] using h

def shrinkingBump (r : ℝ) (hr : 0 < r) (j : ℕ) : ContDiffBump (0 : ComplexVector n) where
  rIn := approxRadius r j / 2
  rOut := approxRadius r j
  rIn_pos := half_pos (approxRadius_pos hr j)
  rIn_lt_rOut := half_lt_self (approxRadius_pos hr j)

def shrinkingKernel (r : ℝ) (hr : 0 < r) (j : ℕ) : ComplexVector n → ℝ :=
  (shrinkingBump r hr j).normed volume

theorem shrinkingKernel_contDiff {r : ℝ} (hr : 0 < r) (j : ℕ) :
    ContDiff ℝ ∞ (shrinkingKernel (n := n) r hr j) :=
  (shrinkingBump r hr j).contDiff_normed

theorem shrinkingKernel_hasCompactSupport {r : ℝ} (hr : 0 < r) (j : ℕ) :
    HasCompactSupport (shrinkingKernel (n := n) r hr j) :=
  (shrinkingBump r hr j).hasCompactSupport_normed

theorem shrinkingKernel_integral {r : ℝ} (hr : 0 < r) (j : ℕ) :
    (∫ y : ComplexVector n, shrinkingKernel r hr j y) = 1 :=
  (shrinkingBump r hr j).integral_normed

theorem shrinkingKernel_tsupport_subset {r : ℝ} (hr : 0 < r) (j : ℕ) :
    tsupport (shrinkingKernel (n := n) r hr j) ⊆ Metric.closedBall 0 r := by
  rw [shrinkingKernel, ContDiffBump.tsupport_normed_eq]
  exact Metric.closedBall_subset_closedBall (approxRadius_le hr j)

theorem shrinkingSmoothing_contDiff {f : ComplexVector n → ℂ}
    (hf : Integrable f volume) {r : ℝ} (hr : 0 < r) (j : ℕ) :
    ContDiff ℝ ∞ (smoothBy (shrinkingKernel r hr j) f) :=
  (shrinkingBump r hr j).hasCompactSupport_normed.contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) (shrinkingBump r hr j).contDiff_normed hf.locallyIntegrable

/-- Only the approximate-identity kernels use an arbitrary bump base. No
rotation-invariance property is asserted for them. -/
theorem shrinkingKernel_ae_tendsto {f : ComplexVector n → ℂ}
    (hf : Integrable f volume) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ x ∂(volume : Measure (ComplexVector n)),
      Tendsto (fun j => smoothBy (shrinkingKernel r hr j) f x) atTop (𝓝 (f x)) := by
  have hrad : Tendsto (fun j => (shrinkingBump (n := n) r hr j).rOut) atTop (𝓝 0) :=
    approxRadius_tendsto r
  have hratio : ∀ᶠ j in atTop,
      (shrinkingBump (n := n) r hr j).rOut ≤ 2 * (shrinkingBump (n := n) r hr j).rIn := by
    apply Filter.Eventually.of_forall
    intro j
    dsimp only [shrinkingBump]
    linarith
  exact ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (μ := (volume : Measure (ComplexVector n)))
    (φ := fun j => shrinkingBump (n := n) r hr j) hrad hratio hf.locallyIntegrable

theorem shrinkingKernel_tendsto_continuous {g : ComplexVector n → ℂ}
    (hg : Continuous g) {r : ℝ} (hr : 0 < r) (x : ComplexVector n) :
    Tendsto (fun j => smoothBy (shrinkingKernel r hr j) g x) atTop (𝓝 (g x)) := by
  exact ContDiffBump.convolution_tendsto_right_of_continuous
    (μ := (volume : Measure (ComplexVector n)))
    (φ := fun j => shrinkingBump (n := n) r hr j)
    (show Tendsto (fun j => (shrinkingBump (n := n) r hr j).rOut) atTop (𝓝 0) from
      approxRadius_tendsto r) hg x

end Yau.NodeProofs.P03Aux
