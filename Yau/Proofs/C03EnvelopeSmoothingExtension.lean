import Yau.LeafProofs.L22Convolution

/-! A genuine continuous compactly supported extension before normalized convolution. -/
noncomputable section
open scoped Topology ContDiff Convolution
open MeasureTheory Set
namespace Yau.Proofs.C03Aux.EnvelopeSmoothing
open Yau
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

theorem continuous_complex_affine {n : ℕ} (z v : ComplexVector n) :
    Continuous (fun a : ℂ => z + a • v) := by
  change Continuous (fun a : ℂ => WithLp.toLp 2 (fun i => z i + a * v i))
  exact (PiLp.continuous_toLp 2 (fun _ : Fin n => ℂ)).comp
    (continuous_pi fun _ => continuous_const.add (continuous_id.mul continuous_const))

theorem exists_continuous_compact_extension {n : ℕ}
    (r : ℝ) (hr : 0 < r) (f : ComplexVector n → ℝ)
    (hf : ContinuousOn f (Metric.closedBall 0 r)) :
    ∃ F : ComplexVector n → ℝ, Continuous F ∧ HasCompactSupport F ∧
      Integrable F volume ∧ EqOn F f (Metric.closedBall 0 r) := by
  let fc : C(Metric.closedBall (0 : ComplexVector n) r, ℝ) :=
    ⟨fun x => f x, hf.domRestrict⟩
  obtain ⟨G, hG⟩ := fc.exists_restrict_eq Metric.isClosed_closedBall
  let χ : ContDiffBump (0 : ComplexVector n) := ⟨r, r + 1, hr, by linarith⟩
  let F : ComplexVector n → ℝ := fun x => χ x * G x
  have hFc : Continuous F := χ.continuous.mul G.continuous
  have hFs : HasCompactSupport F := χ.hasCompactSupport.mul_right
  refine ⟨F, hFc, hFs, hFc.integrable_of_hasCompactSupport hFs, ?_⟩
  intro x hx
  change χ x * G x = f x
  rw [χ.one_of_mem_closedBall hx, one_mul]
  exact congrArg (fun q : C(Metric.closedBall (0 : ComplexVector n) r, ℝ) => q ⟨x, hx⟩) hG

end Yau.Proofs.C03Aux.EnvelopeSmoothing
