import Yau.Proofs.V04FactorColumnEstimates

/-! Apply the actual deformation estimate to disc-dependent inverse-factor
columns on one common tail. The penalty coefficient stays independent of
the energy cap, the chosen directions, and the sequence index. -/

open Filter
open scoped Matrix ComplexOrder Topology ContDiff
noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n}

theorem majorant_sequence_upper {d : VariationData X q} {j a : ℕ} {δ C CE ε E₀ : ℝ}
    (hδ : 0 < δ) (hC : 0 ≤ C) (hCE : 0 ≤ CE) (hε : 0 < ε)
    (hdef : DeformationEstimateWith d j a ((Real.sqrt δ)⁻¹) CE)
    (F : ℕ → VariationDisc X) (E H Hinv : ℕ → ℂ → CotangentMatrix n)
    (v : ℕ → EuclideanSpace ℂ (CotangentIndex n))
    (hF : MinimizingSequence d j ε F)
    (Kc : Set (CotangentCoord n × ℝ)) (hKc : IsCompact Kc)
    (hKint : Kc ⊆ interior (centerCylinder d))
    (hcenter : ∀ ν, InCotangentTimeChart d.chart ((F ν).f 0) (F ν).s Kc)
    (henergy : ∀ ν, (variationEnergy d j (F ν)).toReal ≤ E₀)
    (hframe : ∀ ν, NormalizedDiscFrame d.G (F ν).f (E ν))
    (hfactor : ∀ ν, SpectralFactorFor d j a δ (F ν) (E ν) (H ν) (Hinv ν))
    (hnorm : ∀ ν z, z ∈ Metric.closedBall (0 : ℂ) 1 → rectOpNorm (Hinv ν z) ≤ (Real.sqrt δ)⁻¹)
    (hsemi : ∀ ν, matrixDSq (fun θ => Hinv ν (circlePoint θ)) ≤
      ENNReal.ofReal C * (1 + variationEnergy d j (F ν)))
    (hv : ∀ ν, ‖v ν‖ ≤ 1)
    (hboundary : ∀ ν, circleAverage (fun θ =>
      quadValue (boundarySymbol d j a (F ν) (E ν) (circlePoint θ))
        (Hinv ν (circlePoint θ) *ᵥ WithLp.ofLp (v ν))) ≤ 1) :
    SeqUpperZero (fun ν => outerCenter d j a (F ν) ^ 2 *
      quadValue (centerTestHessian d (F ν) (E ν)) (Hinv ν 0 *ᵥ WithLp.ofLp (v ν)) - 1 -
        (CE * (1 + C)) * ε * (1 + (variationEnergy d j (F ν)).toReal)) := by
  let l : ℕ → ℂ → CotangentIndex n → ℂ := fun ν z => Hinv ν z *ᵥ WithLp.ofLp (v ν)
  have hcol (ν : ℕ) := spectralFactor_unit_column_estimates hδ hC (hF.1 ν)
    (hfactor ν) (hnorm ν) (hsemi ν) (v ν) (hv ν)
  have hE₀ : 0 ≤ E₀ := ENNReal.toReal_nonneg.trans (henergy 0)
  let D₀ := Real.sqrt (C * (1 + E₀))
  have hD₀ : D₀ ^ 2 = C * (1 + E₀) := Real.sq_sqrt (mul_nonneg hC (by linarith))
  have hD (ν : ℕ) : boundaryDSq (fun θ => l ν (circlePoint θ)) ≤ ENNReal.ofReal (D₀ ^ 2) := by
    have hreal := (hcol ν).2.2.2.2
    have hcap : (boundaryDSq (fun θ => l ν (circlePoint θ))).toReal ≤ C * (1 + E₀) :=
      hreal.trans (mul_le_mul_of_nonneg_left (add_le_add_right (henergy ν) 1) hC)
    rw [← ENNReal.ofReal_toReal (hcol ν).2.2.1, hD₀]
    exact ENNReal.ofReal_le_ofReal hcap
  have hseq := hdef ε hε E₀ D₀ F E l hF ⟨Kc, hKc, hKint, hcenter⟩
    (fun ν => ⟨henergy ν, hframe ν, (hcol ν).1, (hcol ν).2.1, hD ν⟩)
  intro r hr
  filter_upwards [hseq r hr] with ν hν
  have hsum : 1 + (variationEnergy d j (F ν)).toReal +
      (boundaryDSq (fun θ => l ν (circlePoint θ))).toReal ≤
      (1 + C) * (1 + (variationEnergy d j (F ν)).toReal) := by
    have hh := (hcol ν).2.2.2.2
    nlinarith
  have hpen := mul_le_mul_of_nonneg_left hsum (mul_nonneg hCE hε.le)
  have hb := hboundary ν
  dsimp only [l] at hν hpen
  nlinarith

end Yau.Blueprint.V04Proof
