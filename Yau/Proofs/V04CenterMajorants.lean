import Yau.Proofs.V04MajorantFamily
import Yau.Proofs.V04UniformCenters
import Yau.Proofs.V04PenaltyLimits
import Yau.Proofs.V04CenterGeometry

/-! The original center-majorant conclusion follows from the original
localization, symbol, spectral-factor, and deformation components. Every
given factor is retained, and the unit direction may vary with the disc. -/

open Filter
open scoped Matrix ComplexOrder Topology ContDiff
noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n}

theorem admissible_center_majorant_violation {d : VariationData X q}
    (hd : VariationSetup d) {j a : ℕ} {δ : ℝ} {F : VariationDisc X}
    (hF : AdmissibleVariationDisc d j F) {E H Hinv : ℂ → CotangentMatrix n}
    (hH : SpectralFactorFor d j a δ F E H Hinv) (r : ℝ)
    (hnot : ¬ (((1 + r : ℝ) : ℂ) • ((H 0)ᴴ * H 0) -
      (outerCenter d j a F ^ 2 : ℂ) • centerTestHessian d F E).PosSemidef) :
    ∃ v : EuclideanSpace ℂ (CotangentIndex n), ‖v‖ = 1 ∧
      1 + r < outerCenter d j a F ^ 2 *
        quadValue (centerTestHessian d F E) (Hinv 0 *ᵥ WithLp.ofLp v) := by
  have h0 : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) 1 := by simp
  exact center_majorant_unit_violation (n := n) _ _ _
    (admissible_centerTestHessian_isHermitian hd hF E)
    (hH.2.1 0 h0).1 (hH.2.1 0 h0).2 _ r (by
      simpa only [Complex.ofReal_pow] using hnot)

theorem centerMajorants_of_original_components {d : VariationData X q}
    (hd : VariationSetup d) {a : ℕ} (ha : 4 ≤ a)
    (hloc : LocalizationEstimates d) (hsymbol : SymbolBounds d a)
    (hspec : SpectralFactorEstimates d a)
    (hdeform : ∀ᶠ j in atTop, DeformationEstimate d j a) : CenterMajorants d a := by
  classical
  obtain ⟨Kc, hKc, hKint, hcenters⟩ := uniform_minimizing_centers hd hloc
  filter_upwards [hcenters, hdeform] with j hj hdef
  intro δ hδ F E H Hinv hdata hzero r hr
  obtain ⟨C, hC, hbound⟩ := spectralFactorEstimates_all_factors hspec j δ hδ
  obtain ⟨CE, hCE, hdefCE⟩ := hdef ((Real.sqrt δ)⁻¹) (by positivity)
  have hdefWith : DeformationEstimateWith d j a ((Real.sqrt δ)⁻¹) CE :=
    hdefCE d.test hd.2.2.2.2.2.2.2.1
  let val : ℝ → ℕ → EuclideanSpace ℂ (CotangentIndex n) → ℝ := fun ε ν v =>
    outerCenter d j a (F ε ν) ^ 2 * quadValue (centerTestHessian d (F ε ν) (E ε ν))
      (Hinv ε ν 0 *ᵥ WithLp.ofLp v)
  have hvex (ε : ℝ) (ν : ℕ) : ∃ v : EuclideanSpace ℂ (CotangentIndex n),
      ‖v‖ ≤ 1 ∧ ((∃ u : EuclideanSpace ℂ (CotangentIndex n),
        ‖u‖ = 1 ∧ 1 + r < val ε ν u) → 1 + r < val ε ν v) := by
    by_cases ht : ∃ u : EuclideanSpace ℂ (CotangentIndex n), ‖u‖ = 1 ∧ 1 + r < val ε ν u
    · obtain ⟨u, hu, hut⟩ := ht
      exact ⟨u, hu.le, fun _ => hut⟩
    · exact ⟨0, by simp, fun h => False.elim (ht h)⟩
  choose v hvnorm hvtest using hvex
  have hseq := majorant_family_upper hd ha hδ hC hCE hdefWith hbound hsymbol
    Kc hKc hKint hj F E H Hinv v hdata hzero hvnorm
  have hupper := eps_upper_of_seq_upper_penalty
    (fun ε ν => val ε ν (v ε ν) - 1)
    (fun ε ν => (variationEnergy d j (F ε ν)).toReal)
    (mul_nonneg hCE (by linarith only [hC] : 0 ≤ 1 + C)) hzero hseq
  refine ((hupper r hr).and hdata).mono ?_
  intro ε hεboth
  obtain ⟨hεbound, hε⟩ := hεboth
  refine hεbound.mono ?_
  intro ν hν
  by_contra hnot
  have hmatrix : ∃ u : EuclideanSpace ℂ (CotangentIndex n),
      ‖u‖ = 1 ∧ 1 + r < val ε ν u :=
    admissible_center_majorant_violation hd (hε.1.1 ν) (hε.2 ν).2 r hnot
  have hbad := hvtest ε ν hmatrix
  linarith only [hbad, hν]

end Yau.Blueprint.V04Proof
