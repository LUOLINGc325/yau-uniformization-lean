import Yau.Proofs.D05HolomorphicDual
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-! The scalar coordinate dual constructed by Cauchy–Green is a genuine
holomorphic continuous complex-linear functional on the same ambient space. -/

open scoped Topology ContDiff

noncomputable section
namespace Yau.Blueprint.D05Proof

variable {ι : Type*} [Fintype ι]

def ambientDualLinear (a : ι → ℂ) : EuclideanSpace ℂ ι →L[ℂ] ℂ :=
  ∑ i, a i • (EuclideanSpace.proj i : EuclideanSpace ℂ ι →L[ℂ] ℂ)

theorem ambientDualLinear_apply (a : ι → ℂ) (v : EuclideanSpace ℂ ι) :
    ambientDualLinear a v = ∑ i, a i * v i := by
  simp [ambientDualLinear, smul_eq_mul]

theorem ambientDualLinear_contDiffOn {U : Set ℂ} {a : ℂ → ι → ℂ}
    (ha : ∀ i, ContDiffOn ℂ ∞ (fun z => a z i) U) :
    ContDiffOn ℂ ∞ (fun z => ambientDualLinear (a z)) U :=
  ContDiffOn.sum (fun i _ => (ha i).smul contDiffOn_const)

theorem ambient_holomorphic_functional_of_nonvanishing
    {e : ℂ → EuclideanSpace ℂ ι} {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    (he : ContDiffOn ℂ ∞ e (Metric.ball 0 R))
    (hne : ∀ z ∈ Metric.ball (0 : ℂ) R, e z ≠ 0) :
    ∃ a : ℂ → EuclideanSpace ℂ ι →L[ℂ] ℂ,
      ContDiffOn ℂ ∞ a (Metric.ball 0 ρ) ∧
      ∀ z ∈ Metric.ball (0 : ℂ) ρ, a z (e z) = 1 := by
  have hec : ∀ i, ContDiffOn ℂ ∞ (fun z => e z i) (Metric.ball 0 R) :=
    (contDiffOn_piLp 2).mp he
  have hnec : ∀ z ∈ Metric.ball (0 : ℂ) R, (fun i => e z i) ≠ 0 := by
    intro z hz hzero
    apply hne z hz
    ext i
    exact congrFun hzero i
  obtain ⟨a, ha, hae⟩ := ambient_holomorphic_dual_of_nonvanishing hρ hρR hec hnec
  refine ⟨fun z => ambientDualLinear (a z), ambientDualLinear_contDiffOn ha, ?_⟩
  intro z hz
  simpa only [ambientDualLinear_apply, mul_comm] using hae z hz

end Yau.Blueprint.D05Proof
