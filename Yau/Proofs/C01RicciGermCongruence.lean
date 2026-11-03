import Yau.Proofs.C01PathEnergyCongruence
import Yau.Proofs.C01FixedPathEnergyDensity

/-! Actual Ricci quadratics of two equal path germs agree. The proof
uses uniqueness of their genuine time derivatives, without identifying
tangent vectors in fibers over different expressions for the same point. -/

noncomputable section
open Filter MeasureTheory
open scoped Topology ContDiff Manifold

namespace Yau.NodeProofs.C01Aux
open Yau Yau.Blueprint Yau.LeafProofs.L12Aux
variable {n : ℕ} {X : KahlerManifold n} {o : Pt X}
  {h : Flow X} {U P ρ : STF X}

theorem localizedFlow_pathRicci_germ_congr
    (hflow : LocalizedFlow X o h U P ρ) (γ β : ℝ → Pt X) (u : ℝ)
    (heq : γ =ᶠ[𝓝 u] β) (a : ℝ) (ha : 0 < a) :
    letI := manifold_realSmooth X.manifold
    ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 γ u →
    ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 β u →
    actualRealRicciQuadratic (h a) (γ u) (realCurveVelocity γ u) =
      actualRealRicciQuadratic (h a) (β u) (realCurveVelocity β u) := by
  letI := manifold_realSmooth X.manifold
  intro hγ hβ
  have HE : (fun t => fixedActualPathEnergyDensity h γ (t, u)) =
      (fun t => fixedActualPathEnergyDensity h β (t, u)) := by
    funext t
    exact actualPathSpeed_sq_congr_eventuallyEq (h t) γ β u heq hγ hβ
  have HG := localizedFlow_fixed_energyDensity_hasDerivAt hflow γ u a ha
  have HB := localizedFlow_fixed_energyDensity_hasDerivAt hflow β u a ha
  rw [HE] at HG
  exact neg_injective (HG.unique HB)

theorem localizedFlow_pathRicci_weighted_integral_germ_congr
    (hflow : LocalizedFlow X o h U P ρ) (γ β : ℝ → Pt X) (w : ℝ → ℝ)
    (heq : ∀ u ∈ Set.Icc (0 : ℝ) 1, γ =ᶠ[𝓝 u] β) (a : ℝ) (ha : 0 < a) :
    letI := manifold_realSmooth X.manifold
    (∀ u ∈ Set.Icc (0 : ℝ) 1, ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 γ u) →
    (∀ u ∈ Set.Icc (0 : ℝ) 1, ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 β u) →
    (∫ u in Set.Icc (0 : ℝ) 1, w u * actualRealRicciQuadratic (h a) (γ u) (realCurveVelocity γ u)) =
      ∫ u in Set.Icc (0 : ℝ) 1, w u * actualRealRicciQuadratic (h a) (β u) (realCurveVelocity β u) := by
  letI := manifold_realSmooth X.manifold
  intro hγ hβ
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
  rw [localizedFlow_pathRicci_germ_congr hflow γ β u (heq u hu) a ha (hγ u hu) (hβ u hu)]

end Yau.NodeProofs.C01Aux
