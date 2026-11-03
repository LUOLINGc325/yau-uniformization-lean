import Yau.Proofs.C03SourceSpeed

/-! Global curve extensions preserve the actual geodesic, speed and
parallel-transport equations when they preserve the original local germs. -/

noncomputable section
open Filter
open scoped Topology ContDiff

namespace Yau.Proofs.C03Aux
open Yau Yau.LeafProofs L12Aux L23Aux L23LocalDistanceContract
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

theorem source_speed_congr_germ (hn : 1 ≤ n)
    (k : HermitianField (ComplexEuclideanManifold n hn))
    (γ₁ γ₀ : ℝ → ComplexVector n) (t : ℝ)
    (h₁ : ContDiffAt ℝ 1 γ₁ t) (h₀ : ContDiffAt ℝ 1 γ₀ t)
    (heq : γ₁ =ᶠ[𝓝 t] γ₀) : actualSpeedSq k γ₁ t = actualSpeedSq k γ₀ t := by
  rw [actualSpeedSq_source_chart hn k γ₁ t h₁, actualSpeedSq_source_chart hn k γ₀ t h₀,
    heq.self_of_nhds, heq.deriv_eq]

theorem source_geodesic_equation_congr_germ
    (Γ : ComplexVector n → ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n)
    (γ₁ γ₀ : ℝ → ComplexVector n) (t : ℝ) (heq : γ₁ =ᶠ[𝓝 t] γ₀)
    (hgeo : HasDerivAt (deriv γ₀) (-Γ (γ₀ t) (deriv γ₀ t) (deriv γ₀ t)) t) :
    HasDerivAt (deriv γ₁) (-Γ (γ₁ t) (deriv γ₁ t) (deriv γ₁ t)) t := by
  rw [heq.self_of_nhds, heq.deriv_eq]
  exact hgeo.congr_of_eventuallyEq heq.deriv

theorem source_parallel_equation_congr_germs
    (Γ : ComplexVector n → ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n)
    (γ₁ γ₀ W₁ W₀ : ℝ → ComplexVector n) (t : ℝ) (a : ℂ)
    (hγ : γ₁ =ᶠ[𝓝 t] γ₀) (hW : W₁ =ᶠ[𝓝 t] W₀)
    (hpar : HasDerivAt (fun s => a • W₀ s)
      (-Γ (γ₀ t) (deriv γ₀ t) (a • W₀ t)) t) :
    HasDerivAt (fun s => a • W₁ s)
      (-Γ (γ₁ t) (deriv γ₁ t) (a • W₁ t)) t := by
  rw [hγ.self_of_nhds, hγ.deriv_eq, hW.self_of_nhds]
  exact hpar.congr_of_eventuallyEq (hW.fun_comp (fun v => a • v))

end Yau.Proofs.C03Aux
