import Yau.Proofs.F03HeatCorrectionRegularity
import Yau.Proofs.F03DyadicGluingRegularity
import Yau.Proofs.F03HeatCorrectionSize

/-! One actual heat kernel and one actual dyadic partition define the glued correction. -/
noncomputable section
open MeasureTheory Set
namespace Yau.Proofs.F03Aux
open Yau Blueprint HeatConcreteBindings
variable {n : ℕ}

def metricDefectDyadicCorrection (X : KahlerManifold n) (h : Flow X)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (O : ℕ → Set (Pt X)) (hO : SmoothExhaustion O) (u : Pt X → ℝ) : STF X :=
  dyadicGluing u (fun j => metricDefectHeatCorrection X h μ hμ O hO ((2:ℝ)^j))

theorem metricDefectDyadicCorrection_smoothSpaceC1Time
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) (u : Pt X → ℝ) (hu : ControlledExhaustion X o u)
    {T : ℝ} (hT : 0 < T)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (O : ℕ → Set (Pt X)) (hO : SmoothExhaustion O) :
    SmoothSpaceC1Time (metricDefectDyadicCorrection X h μ hμ O hO u) (Icc 0 T) :=
  dyadicGluing_smoothSpaceC1Time u hu.1 _ (fun j =>
    metricDefectHeatCorrection_smoothSpaceC1Time X o h U P ρ hf u hu hT μ hμ O hO (by positivity))

theorem metricDefectDyadicCorrection_zero
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (O : ℕ → Set (Pt X)) (hO : SmoothExhaustion O) (u : Pt X → ℝ) (x : Pt X) :
    metricDefectDyadicCorrection X h μ hμ O hO u x 0=0 := by
  simp only [metricDefectDyadicCorrection,dyadicGluing,
    metricDefectHeatCorrection_zero X o h U P ρ hf μ hμ O hO,mul_zero,tsum_zero]

theorem metricDefectDyadicCorrection_nonpos
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (O : ℕ → Set (Pt X)) (hO : SmoothExhaustion O) (u : Pt X → ℝ)
    (hu0 : ∀ x,0 ≤ u x) (x : Pt X) {s : ℝ} (hs : 0 ≤ s) :
    metricDefectDyadicCorrection X h μ hμ O hO u x s ≤ 0 := by
  obtain ⟨N,V,_hV,hVx,hTail⟩ := dyadicPartition_locally_eventually_zero (u x)
  change dyadicGluing u _ x s ≤ 0
  rw [dyadicGluing_eq_sum_of_tail u _ x s N (fun j hj => hTail j hj _ hVx)]
  exact Finset.sum_nonpos (fun j _ => mul_nonpos_of_nonneg_of_nonpos
    (dyadicPartition_nonnegative j (hu0 x))
    (metricDefectHeatCorrection_nonpos X o h U P ρ hf μ hμ O hO _ x hs))

end Yau.Proofs.F03Aux
