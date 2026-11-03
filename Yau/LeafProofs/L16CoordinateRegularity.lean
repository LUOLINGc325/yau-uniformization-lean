import Yau.LeafProofs.L16WeakJetMollification
import Yau.LeafProofs.L16SmoothLimit

open MeasureTheory Filter
open scoped Topology ContDiff
noncomputable section
namespace Yau.LeafProofs.L16Aux

set_option backward.isDefEq.respectTransparency.types false

theorem smooth_representative_of_finite_coordinate_weak_jets_with_kernel {m : ℕ}
    {ρ u : (Fin m → ℝ) → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : (∫ x, ρ x) = 1)
    (hjets : ∀ N : ℕ, ∃ U : List (Fin m) → (Fin m → ℝ) → ℝ,
      FiniteCoordinateWeakJet N u U) :
    ∃ v : (Fin m → ℝ) → ℝ, ContDiff ℝ ∞ v ∧ v =ᵐ[volume] u ∧
      ∀ w : List (Fin m), TendstoUniformly
        (fun k => coordinateWordDerivative (coordinateMollify ρ k u) w)
        (coordinateWordDerivative v w) atTop := by
  obtain ⟨U0,hU0⟩ := hjets 0
  have hu : MemLp u 2 volume ∧ HasCompactSupport u := by
    simpa only [List.length_nil,hU0.1] using hU0.2.1 [] le_rfl
  have hui := Yau.LeafProofs.L03.memLp_two_compact_integrable volume u hu.1 hu.2
  have hLim : Tendsto (fun k => ∫ x, (coordinateMollify ρ k u x-u x)^2) atTop (𝓝 0) := by
    simpa only [Real.norm_eq_abs,sq_abs] using coordinateMollify_L2_tendsto hρ hcρ hρ0 hρ1 hu.1 hu.2
  exact exists_contDiff_ae_eq_of_coordinateWordDerivative_uniform_cauchy
    (fun k => coordinateMollify_smooth hρ hcρ hui k)
    (fun k => coordinateMollify_compact hcρ hu.2 k) hu.1
    (coordinateWordDerivative_coordinateMollify_uniformCauchy_of_finiteJets hρ hcρ hρ0 hρ1 hjets) hLim

theorem smooth_representative_of_finite_coordinate_weak_jets {m : ℕ}
    {u : (Fin m → ℝ) → ℝ}
    (hjets : ∀ N : ℕ, ∃ U : List (Fin m) → (Fin m → ℝ) → ℝ,
      FiniteCoordinateWeakJet N u U) :
    ∃ v : (Fin m → ℝ) → ℝ, ContDiff ℝ ∞ v ∧ v =ᵐ[volume] u := by
  let B : ContDiffBump (0 : Fin m → ℝ) := ⟨1,2,by norm_num,by norm_num⟩
  obtain ⟨v,hv,hAE,_hLim⟩ := smooth_representative_of_finite_coordinate_weak_jets_with_kernel
    B.contDiff_normed B.hasCompactSupport_normed (fun x => B.nonneg_normed x) B.integral_normed hjets
  exact ⟨v,hv,hAE⟩

end Yau.LeafProofs.L16Aux
