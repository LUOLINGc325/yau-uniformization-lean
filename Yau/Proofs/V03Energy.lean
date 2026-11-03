import Yau.Proofs.V03Elementary

/-! Finite-energy conversion for the complete computed V03 energy. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n}

def mixedReal (u : ℂ → ℝ) : ℝ :=
  (wirt (fun z => wirtBar (fun z' => (u z' : ℂ)) z 1) 0 1).re

def logTrace (d : VariationData X q) (j : ℕ)
    (f : ℂ → CotangentPoint X.manifold) (θ : ℝ) : ℝ :=
  Real.log (wallProduct d j (f (circlePoint θ)))

def clockArea (F : VariationDisc X) : ENNReal :=
  ∫⁻ ζ in Metric.ball (0 : ℂ) 1, ENNReal.ofReal (2 * ‖deriv F.w ζ‖ ^ 2)

def spatialArea (d : VariationData X q) (f : ℂ → CotangentPoint X.manifold) : ℝ :=
  (discArea X.metric.form (fun ζ => (f ζ).1)).toReal +
  (euclideanArea (fun ζ => d.G (f ζ))).toReal + gaussArea d.G f

theorem energy_components_ne_top {d : VariationData X q} {j : ℕ}
    {F : VariationDisc X} (hF : variationEnergy d j F ≠ ⊤) :
    discArea X.metric.form (fun ζ => (F.f ζ).1) ≠ ⊤ ∧
    euclideanArea (fun ζ => d.G (F.f ζ)) ≠ ⊤ ∧
    clockArea F ≠ ⊤ ∧ scalarDSq (logTrace d j F.f) ≠ ⊤ := by
  simp only [variationEnergy, ENNReal.add_ne_top] at hF
  exact ⟨hF.1.1.1.1, hF.1.1.1.2, hF.1.2, hF.2⟩

theorem variationEnergy_toReal_split {d : VariationData X q} {j : ℕ}
    {F : VariationDisc X} (hF : variationEnergy d j F ≠ ⊤) :
    (variationEnergy d j F).toReal =
      (discArea X.metric.form (fun ζ => (F.f ζ).1)).toReal +
      (euclideanArea (fun ζ => d.G (F.f ζ))).toReal +
      (ENNReal.ofReal (gaussArea d.G F.f)).toReal +
      (clockArea F).toReal + (scalarDSq (logTrace d j F.f)).toReal := by
  obtain ⟨hA, hB, hD, hE⟩ := energy_components_ne_top hF
  have hAB := ENNReal.add_ne_top.mpr ⟨hA, hB⟩
  have hABC := ENNReal.add_ne_top.mpr ⟨hAB,
    (ENNReal.ofReal_ne_top : ENNReal.ofReal (gaussArea d.G F.f) ≠ ⊤)⟩
  have hABCD := ENNReal.add_ne_top.mpr ⟨hABC, hD⟩
  change (((discArea X.metric.form (fun ζ => (F.f ζ).1) +
      euclideanArea (fun ζ => d.G (F.f ζ)) + ENNReal.ofReal (gaussArea d.G F.f)) +
      clockArea F) + scalarDSq (logTrace d j F.f)).toReal = _
  rw [ENNReal.toReal_add hABCD hE, ENNReal.toReal_add hABC hD,
    ENNReal.toReal_add hAB ENNReal.ofReal_ne_top, ENNReal.toReal_add hA hB]

theorem variationEnergy_toReal_split_of_gauss_nonneg {d : VariationData X q} {j : ℕ}
    {F : VariationDisc X} (hF : variationEnergy d j F ≠ ⊤)
    (hG : 0 ≤ gaussArea d.G F.f) :
    (variationEnergy d j F).toReal =
      spatialArea d F.f + (clockArea F).toReal +
      (scalarDSq (logTrace d j F.f)).toReal := by
  rw [variationEnergy_toReal_split hF, ENNReal.toReal_ofReal hG]
  rfl

theorem logSeminorm_toReal_le_energy {d : VariationData X q} {j : ℕ}
    {F : VariationDisc X} (hF : variationEnergy d j F ≠ ⊤) :
    (scalarDSq (logTrace d j F.f)).toReal ≤ (variationEnergy d j F).toReal := by
  rw [variationEnergy_toReal_split hF]
  have hA : 0 ≤ (discArea X.metric.form (fun ζ => (F.f ζ).1)).toReal :=
    ENNReal.toReal_nonneg
  have hB : 0 ≤ (euclideanArea (fun ζ => d.G (F.f ζ))).toReal :=
    ENNReal.toReal_nonneg
  have hC : 0 ≤ (ENNReal.ofReal (gaussArea d.G F.f)).toReal := ENNReal.toReal_nonneg
  have hD : 0 ≤ (clockArea F).toReal := ENNReal.toReal_nonneg
  linarith

theorem radial_clockArea (F : VariationDisc X) (r : ℝ) :
    clockArea (radialVariationDisc F r) =
      ∫⁻ ζ in Metric.ball (0 : ℂ) 1,
        ENNReal.ofReal (2 * ‖deriv (fun η => F.w ((r : ℂ) * η)) ζ‖ ^ 2) := rfl

end Yau.Blueprint.V03Proof
