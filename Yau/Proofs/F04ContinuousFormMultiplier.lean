import Yau.Proofs.F04FormMultiplierStrong
import Yau.Proofs.F04UniformOperatorLimit

open MeasureTheory Filter Set
open scoped Topology InnerProductSpace

noncomputable section

namespace Yau.F04Proof

open Yau.LeafProofs.L03

variable {n k : ℕ} {M : ComplexManifold n}

/-- A bounded continuous scalar function of an L2 class defines the actual
bounded multiplier on the completed form fibres. -/
def continuousFormMultiplier (g : SmoothMetric M) (μ : Measure M.Carrier)
    (b : ℝ → ℝ) (hb : Continuous b) (C : ℝ) (hC : 0 ≤ C) (hbC : ∀ s, |b s| ≤ C)
    (f : Lp ℝ 2 μ) : L2FormHilbert g μ k →L[ℝ] L2FormHilbert g μ k :=
  multiplyL2FormHilbert g μ (fun x => b (f x))
    (hb.comp_aestronglyMeasurable (Lp.memLp f).aestronglyMeasurable)
    C hC (fun x => hbC (f x))

theorem continuousFormMultiplier_fixed_tendsto
    (g : SmoothMetric M) (μ : Measure M.Carrier)
    (b : ℝ → ℝ) (hb : Continuous b) (C : ℝ) (hC : 0 ≤ C) (hbC : ∀ s, |b s| ≤ C)
    (f : ℕ → Lp ℝ 2 μ) (f₀ : Lp ℝ 2 μ) (hf : Tendsto f atTop (𝓝 f₀))
    (A : RealForm M k) (hA : L2RealForm g.form μ A) :
    Tendsto (fun j => continuousFormMultiplier g μ b hb C hC hbC (f j)
      (realizeL2Form g μ (L2FormSpace.ofSection A hA))) atTop
      (𝓝 (continuousFormMultiplier g μ b hb C hC hbC f₀
        (realizeL2Form g μ (L2FormSpace.ofSection A hA)))) := by
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ms, _, hms⟩ := (tendstoInMeasure_of_tendsto_Lp (hf.comp hns)).exists_seq_tendsto_ae
  refine ⟨ms, ?_⟩
  apply bounded_form_multipliers_tendsto g μ A hA
    (fun j x => b (f (ns (ms j)) x)) (fun x => b (f₀ x))
    (fun j => hb.comp_aestronglyMeasurable (Lp.memLp (f (ns (ms j)))).aestronglyMeasurable)
    (hb.comp_aestronglyMeasurable (Lp.memLp f₀).aestronglyMeasurable)
    C hC (fun j x => hbC (f (ns (ms j)) x)) (fun x => hbC (f₀ x))
  filter_upwards [hms] with x hx
  have hh := ((hb.continuousAt.tendsto.comp hx).sub
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => b (f₀ x)) atTop (𝓝 (b (f₀ x))))).pow 2
  simpa only [Function.comp_def, sub_self, zero_pow (by norm_num : 2 ≠ 0), zero_mul] using
    hh.mul_const (formNormSq g.form A x)

/-- Simultaneous strong convergence of the scalar L2 input and the genuine
form-Hilbert input.  No pointwise convergence of a full L2 sequence is used. -/
theorem continuousFormMultiplier_tendsto
    (g : SmoothMetric M) (μ : Measure M.Carrier)
    (b : ℝ → ℝ) (hb : Continuous b) (C : ℝ) (hC : 0 ≤ C) (hbC : ∀ s, |b s| ≤ C)
    (f : ℕ → Lp ℝ 2 μ) (f₀ : Lp ℝ 2 μ) (hf : Tendsto f atTop (𝓝 f₀))
    (a : ℕ → L2FormHilbert g μ k) (a₀ : L2FormHilbert g μ k)
    (ha : Tendsto a atTop (𝓝 a₀)) :
    Tendsto (fun j => continuousFormMultiplier g μ b hb C hC hbC (f j) (a j)) atTop
      (𝓝 (continuousFormMultiplier g μ b hb C hC hbC f₀ a₀)) := by
  obtain ⟨A, hA, hrep⟩ := l2FormHilbert_exists_section g μ a₀
  apply uniformly_bounded_operators_apply_tendsto
    (fun j => continuousFormMultiplier g μ b hb C hC hbC (f j)) C
    (fun j => multiplyL2FormHilbert_opNorm_le g μ _ _ C hC _) a a₀ _ ha
  rw [← hrep]
  exact continuousFormMultiplier_fixed_tendsto g μ b hb C hC hbC f f₀ hf A hA

end Yau.F04Proof
