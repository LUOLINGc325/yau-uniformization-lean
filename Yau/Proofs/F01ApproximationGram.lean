import Yau.Proofs.F01RescaledGram
import Yau.Proofs.F01BoundaryExtension
import Yau.Proofs.F01InteriorExtension

/-! The actual conformally restricted metric has exactly the coefficient
family whose smoothness and uniform budgets were proved. -/
open Set TopologicalSpace
open scoped Manifold ContDiff
noncomputable section
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} (M : ComplexManifold n) (S : Opens M.Carrier)
  (hS : IsConnected (S : Set M.Carrier))

theorem conformal_open_rescaled_chart_coefficient (g : HermitianField M)
    (u : M.Carrier → ℝ) (L c δ : ℝ)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : ContMDiffOn (ComplexModel n) (ComplexModel n) ∞ e e.source)
    (z₀ : ComplexVector n) (hs : ((c * δ : ℝ) : ℂ) ≠ 0) {z : ComplexVector n}
    (hz : z ∈ (openRestrictedChart M S hS
      (rescaledChart e z₀ ((c * δ : ℝ) : ℂ) hs)).source) (i j : Fin n) :
    chartGramCoefficient
      (conformalField (openRestrictedField M S hS g)
        (fun x => conformalProfile (u (openInclusion M S hS x) / L)))
      (openRestrictedChart M S hS (rescaledChart e z₀ ((c * δ : ℝ) : ℂ) hs)) z i j =
      interiorExtension (fun y => u (e y)) (fun y => chartGramCoefficient g e y i j)
        L c (z₀, δ, z) := by
  let eR := rescaledChart e z₀ ((c * δ : ℝ) : ℂ) hs
  let eL := openRestrictedChart M S hS eR
  have hzR : z ∈ eR.source := targetRestriction_source_subset eR S hS.nonempty.to_subtype hz
  have heR : ContMDiffOn (ComplexModel n) (ComplexModel n) ∞ eR eR.source :=
    rescaledChart_contMDiffOn e he z₀ _ hs
  have hrestr := openRestrictedField_targetRestriction_coefficient M S hS g eR heR hz i j
  have hrescale := chartGramCoefficient_rescaled_real g e he z₀ (c * δ) hs hzR i j
  have hpoint : openInclusion M S hS (eL z) = eR z :=
    targetRestriction_value eR S hS.nonempty.to_subtype hz
  change (Real.exp (conformalProfile (u (openInclusion M S hS (eL z)) / L)) : ℂ) *
      chartGramCoefficient (openRestrictedField M S hS g) eL z i j = _
  have hp := congrArg (fun x : M.Carrier =>
    (Real.exp (conformalProfile (u x / L)) : ℂ)) hpoint
  rw [hp, hrestr, hrescale]
  change (Real.exp (conformalProfile (u (e (z₀ + ((c * δ : ℝ) : ℂ) • z)) / L)) : ℂ) *
      ((((c * δ) ^ 2 : ℝ) : ℂ) * chartGramCoefficient g e (z₀ + (c * δ) • z) i j) = _
  have hsmul : ((c * δ : ℝ) : ℂ) • z = (c * δ) • z := by rfl
  rw [hsmul]
  simp only [interiorExtension, scaledEvaluation, Complex.real_smul,
    Complex.ofReal_mul]
  ring

end Yau.NodeProofs.F01Aux
