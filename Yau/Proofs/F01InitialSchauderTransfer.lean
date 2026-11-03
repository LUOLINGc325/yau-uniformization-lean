import Yau.Proofs.F01NormalizedInitialInputs
import Yau.Proofs.F01InitialCylinderRescale

/-! Compose the exact original analytic estimate with the constructed
native initial data. The estimate parameter is discharged by the original
L05 producer; it supplies no solution, flow, or regularity realization. -/
noncomputable section
open Set Metric
open scoped ContDiff Manifold Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.ParabolicCandidates Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem normalized_initial_schauder_of_estimate
    (hInitial : MongeAmpereInitialSchauder)
    (g : HermitianField M) (hg : MetricSmooth g) (A : BoundedChartFamily g)
    {C α β : ℝ} (hC : 1 ≤ C) (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β) (hβ1 : β < 1) :
    ∃ Cv : ℝ, 0 < Cv ∧
      ∀ (h : ℝ → HermitianField M) (U : M.Carrier → ℝ → ℝ) (T ρ : ℝ),
      0 < ρ → 2 * ρ ≤ A.radius → 2 * ρ ≤ 1 → (2 * ρ) ^ 2 ≤ T →
      SmoothSpaceTime U (Icc 0 T) → h 0 = g → (∀ x, U x 0 = 0) →
      (∀ s ∈ Icc 0 T, ∀ x,
        gMat (h s) x = gMat g x - (s : ℂ) • ricci g x + levi (fun y => U y s) x) →
      (∀ x s, s ∈ Icc 0 T → HasDerivWithinAt (U x)
        (flowLogDetRatio g h x s) (Icc 0 T) s) →
      (∀ x s, s ∈ Icc 0 T →
        (gMat (h s) x - ((C⁻¹ : ℝ) : ℂ) • gMat g x).PosSemidef ∧
        ((C : ℂ) • gMat g x - gMat (h s) x).PosSemidef) →
      ∀ a : M.Carrier,
      SchauderBound (min α β) (cylinder (ball 0 1) (-1) 1)
        (forwardZeroSpaceTime (parabolicRescalePotential ρ
          (fun p : Point n => U (A.chart a p.1) p.2))) Cv := by
  obtain ⟨ell, upper, K, B, hell, hlu, hK, hB, hInputs⟩ :=
    exists_normalized_initial_inputs g hg A hC hα1.le hβ1.le
  obtain ⟨Cv0, hCv0, hEstimate⟩ := hInitial n
    (Yau.LeafProofs.L12Aux.manifold_dimension_pos M) α β ell upper K B
    hα hα1 hβ hβ1 hell hlu hK hB
  refine ⟨4 * Cv0, by positivity, ?_⟩
  intro h U T ρ hρ hρr hρ1 hρT hU hh0 hU0 hpot hpde hflow a
  obtain ⟨hSmooth, hPositive, hHolder, hSource, hC2, hSup, hZero, hRange, hEquation⟩ :=
    hInputs h U T (2 * ρ) (mul_pos (by norm_num) hρ) hρr hρ1 hρT
      hU hh0 hU0 hpot hpde hflow a
  have hBound := hEstimate (fun z => pullbackMatrix g (A.chart a) ((2 * ρ) • z))
    (forwardZeroSpaceTime (parabolicRescalePotential (2 * ρ)
      (fun p : Point n => U (A.chart a p.1) p.2)))
    hSmooth hPositive hHolder hSource hC2 hSup hZero hRange hEquation
  exact normalized_initial_half_scale_schauder hρ.ne'
    (fun p : Point n => U (A.chart a p.1) p.2) (le_min hα.le hβ.le) hBound

end Yau.NodeProofs.F01Aux
