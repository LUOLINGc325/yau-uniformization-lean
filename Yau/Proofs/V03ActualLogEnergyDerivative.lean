import Yau.Proofs.V03ActualLogFirstBoundaryBound
import Yau.Proofs.V03ActualLogMixedBoundaryBound
import Yau.Proofs.V03ActualLogEnergyJetBound
import Yau.Proofs.V03ActualEuclideanEnergyDerivative

/-! The full original logarithmic wall seminorm satisfies the actual
mixed energy derivative bound, with one constant before every realization. -/

open scoped Topology ContDiff

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem actualLogEnergyDerivative {n q : ℕ} {X : KahlerManifold n}
    {d : VariationData X q} (hd : VariationSetup d) (j a : ℕ) (ha : 4 ≤ a)
    (L : ℝ) (hL : 0 ≤ L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : VariationDisc X) (E : ℂ → CotangentMatrix n)
      (l : ℂ → CotangentIndex n → ℂ) (h α : ℂ → ℂ)
      (fz : ℂ → ℂ → CotangentPoint X.manifold) (R : ℝ),
      AdmissibleVariationDisc d j F → NormalizedDiscFrame d.G F.f E → HolomorphicColumn l →
      (∀ ζ ∈ Metric.closedBall (0 : ℂ) 1, ∑ i, ‖l ζ i‖ ^ 2 ≤ L ^ 2) →
      RealizesFirstField d j a F E l h α fz R →
      |mixedReal (fun z => (scalarDSq (logTrace d j (fz z))).toReal)| ≤
        C * (1 + (variationEnergy d j F).toReal +
          (boundaryDSq (fun θ => l (circlePoint θ))).toReal) := by
  obtain ⟨C₁, hC₁, hfirst⟩ := actualLogFirstJet_uniform_boundaryDSq hd j a ha L hL
  obtain ⟨C₂, hC₂, hmixed⟩ := actualLogMixedJet_uniform_boundaryDSq hd j a ha L hL
  refine ⟨C₁ + 1 + C₂, by positivity, fun F E l h α fz R hF hE hl hlL hR => ?_⟩
  let T : ENNReal := 1 + variationEnergy d j F + boundaryDSq (fun θ => l (circlePoint θ))
  let t : ℝ := 1 + (variationEnergy d j F).toReal +
    (boundaryDSq (fun θ => l (circlePoint θ))).toReal
  have hEn : variationEnergy d j F ≠ ⊤ := hF.2.2.2.2.2.2.2.2
  have hDl := holomorphicColumn_boundaryDSq_ne_top hl
  have hT : T ≠ ⊤ := by dsimp only [T]; finiteness
  have hTreal : T.toReal = t := by
    dsimp only [T, t]
    rw [ENNReal.toReal_add (by finiteness : 1 + variationEnergy d j F ≠ ⊤) hDl,
      ENNReal.toReal_add ENNReal.one_ne_top hEn, ENNReal.toReal_one]
  have hfirstR (v : ℂ) (hv : ‖v‖ ≤ 1) :
      (boundaryDSq (fun θ (_ : Unit) => realParameterDerivative
        (fun p : ℂ × ℝ => (logTrace d j (fz p.1) p.2 : ℂ)) v (0, θ))).toReal ≤ C₁ * t := by
    have hb := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hT)
      (hfirst F E l h α fz R hF hE hl hlL hR v hv)
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC₁, hTreal] using hb
  have hmixedR : (scalarDSq (fun θ => mixedReal (fun z => logTrace d j (fz z) θ))).toReal ≤ C₂ * t := by
    have hb := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hT)
      (hmixed F E l h α fz R hF hE hl hlL hR)
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC₂, hTreal] using hb
  have hlogT : (scalarDSq (logTrace d j F.f)).toReal ≤ t := by
    have hh := logSeminorm_toReal_le_energy hEn
    dsimp only [t]
    linarith [ENNReal.toReal_nonneg (a := boundaryDSq (fun θ => l (circlePoint θ)))]
  have hamgm : 2 * Real.sqrt (scalarDSq (logTrace d j F.f)).toReal *
      Real.sqrt (scalarDSq (fun θ => mixedReal (fun z => logTrace d j (fz z) θ))).toReal ≤
      (scalarDSq (logTrace d j F.f)).toReal +
        (scalarDSq (fun θ => mixedReal (fun z => logTrace d j (fz z) θ))).toReal := by
    nlinarith [sq_nonneg (Real.sqrt (scalarDSq (logTrace d j F.f)).toReal -
      Real.sqrt (scalarDSq (fun θ => mixedReal (fun z => logTrace d j (fz z) θ))).toReal),
      Real.sq_sqrt (ENNReal.toReal_nonneg (a := scalarDSq (logTrace d j F.f))),
      Real.sq_sqrt (ENNReal.toReal_nonneg
        (a := scalarDSq (fun θ => mixedReal (fun z => logTrace d j (fz z) θ))))]
  have hb := actualLogEnergy_bound_by_boundary_jets hd j hR.1 hR.2.1
  dsimp only at hb
  have hfirst₁ := hfirstR 1 (by simp)
  have hfirstI := hfirstR Complex.I (by simp)
  change _ ≤ (C₁ + 1 + C₂) * t
  nlinarith

end Yau.Blueprint.V03Proof
