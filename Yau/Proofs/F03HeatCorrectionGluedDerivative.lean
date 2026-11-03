import Yau.Proofs.F03HeatCorrectionGluedTime

/-! Ordinary positive-time differentiability of the actual finite dyadic gluing. -/
noncomputable section
open MeasureTheory
namespace Yau.Proofs.F03Aux
open Yau Blueprint HeatConcreteBindings
variable {n : ℕ}

theorem metricDefectDyadicCorrection_differentiableAt_pos
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) (u : Pt X → ℝ) (hu : ControlledExhaustion X o u)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (O : ℕ → Set (Pt X)) (hO : SmoothExhaustion O)
    (x : Pt X) {s : ℝ} (hs : 0 < s) :
    DifferentiableAt ℝ (metricDefectDyadicCorrection X h μ hμ O hO u x) s := by
  let F : ℕ → Pt X → ℝ → ℝ := fun j => metricDefectHeatCorrection X h μ hμ O hO ((2:ℝ)^j)
  obtain ⟨N,_hN,hSum⟩ := dyadicGluing_finite_partition u F x (hu.2.2.1 x)
  change DifferentiableAt ℝ (dyadicGluing u F x) s
  rw [show dyadicGluing u F x=(fun t => ∑ j ∈ Finset.range (N+1),dyadicPartition j (u x)*F j x t) from funext hSum]
  exact DifferentiableAt.fun_sum (fun j _ =>
    (metricDefectHeatCorrection_differentiableAt_pos X o h U P ρ hf u hu μ hμ O hO (by positivity) x hs).const_mul _)

end Yau.Proofs.F03Aux
