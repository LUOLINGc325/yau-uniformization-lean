import Yau.Proofs.F03CompactTestFunctional
import Yau.Proofs.F03DirichletClassicalHeat

/-! The actual compact-cylinder value map, before bounded evaluation is proved. -/
noncomputable section
open MeasureTheory
open scoped Topology
namespace Yau.Proofs.F03Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- This is an algebraic source-linear map into the genuine continuous
functions on K, constructed solely from actual interior heat regularity. -/
def dirichletCompactHeatValue (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) (a : M.Carrier)
    (K : Set (Parabolic.Point n)) [CompactSpace K]
    (hKQ : K ⊆ {z | z ∈ chartTarget a ∧ chartInv a z ∈ Ω} ×ˢ Set.Ioi (0 : ℝ)) :
    Lp ℝ 2 (μ.restrict Ω) →ₗ[ℝ] C(K,ℝ) where
  toFun f := compactContinuousRestriction K
    (fun p => dirichletClassicalHeat g hK μ hμ Ω hΩ f (chartInv a p.1) p.2)
      ((dirichletClassicalHeat_smooth g hK μ hμ Ω hΩ f a).continuousOn.mono hKQ)
  map_add' f k := by
    ext p
    change dirichletClassicalHeat g hK μ hμ Ω hΩ (f+k) (chartInv a p.val.1) p.val.2 =
      dirichletClassicalHeat g hK μ hμ Ω hΩ f (chartInv a p.val.1) p.val.2 +
        dirichletClassicalHeat g hK μ hμ Ω hΩ k (chartInv a p.val.1) p.val.2
    exact dirichletClassicalHeat_add g hK μ hμ Ω hΩ f k (hKQ p.property).2
      (chartInv a p.val.1) (hKQ p.property).1.2
  map_smul' c f := by
    ext p
    change dirichletClassicalHeat g hK μ hμ Ω hΩ (c • f) (chartInv a p.val.1) p.val.2 =
      c * dirichletClassicalHeat g hK μ hμ Ω hΩ f (chartInv a p.val.1) p.val.2
    exact dirichletClassicalHeat_smul g hK μ hμ Ω hΩ c f (hKQ p.property).2
      (chartInv a p.val.1) (hKQ p.property).1.2

end Yau.Proofs.F03Aux
