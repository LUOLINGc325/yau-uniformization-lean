import Yau.LeafProofs.L19HeatRegularityEllipticity
import Yau.LeafProofs.L19HeatRegularitySlices
import Yau.LeafProofs.L16InteriorSmoothing

/-! The exact L16 theorem applied to the actual constructed scalar heat. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff Manifold InnerProductSpace
namespace Yau.LeafProofs.L19Aux
open L18Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The internally proved L16 interior smoothing theorem produces a
smooth classical chart solution for the actual scalar CFC heat family. -/
theorem scalarHeat_chartInteriorRepresentative (hn : 0 < n)
    (g : SmoothMetric M) (hK : IsKahler g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (x : M.Carrier)
    {O : Set (ComplexVector n)} (hO : IsOpen O) (hOc : IsCompact (closure O))
    (hOt : closure O ⊆ chartTarget x) {l r : ℝ} (hl : 0 < l) (hlr : l < r) (f : Lp ℝ 2 μ) :
    ∃ v : Parabolic.Point n → ℝ, ContDiffOn ℝ ∞ v (O ×ˢ Set.Ioo l r) ∧
      (∀ᵐ t ∂volume.restrict (Set.Ioo l r), (fun z => v (z,t)) =ᵐ[volume.restrict O]
        scalarEnergy_chartRestrictionCLM g μ hμ x hO hOc hOt (scalarHeatFamily g μ hμ t f)) ∧
      ∀ p ∈ O ×ˢ Set.Ioo l r,
        Parabolic.linearOp (O ×ˢ Set.Ioo l r) (scalarHeatChartCoeff g x) (fun _ _ => 0) v p = 0 := by
  obtain ⟨u,G,hE,hEq,hSlices⟩ := scalarHeat_chartWeakSolution g hK μ hμ x hO hOc hOt hl hlr f
  obtain ⟨lam,upper,hEll⟩ := scalarHeatChartCoeff_elliptic g x hOc hOt (Set.Ioo l r)
  have hEllO : Parabolic.Elliptic (O ×ˢ Set.Ioo l r) (scalarHeatChartCoeff g x) lam upper :=
    ⟨hEll.1,hEll.2.1,fun p hp => hEll.2.2 p ⟨subset_closure hp.1,hp.2⟩⟩
  obtain ⟨v,hv,hAE,hClass⟩ := L16Interior.homogeneousInteriorSmoothing n hn O l r lam upper hO hlr
    (scalarHeatChartCoeff g x) (fun _ _ => 0) u G
    (scalarHeatChartCoeff_smooth g x (subset_closure.trans hOt) (Set.Ioo l r)) hEllO hE hEq
  refine ⟨v,hv,?_,hClass⟩
  have hAEslice := Measure.ae_ae_of_ae_prod (Measure.measurePreserving_swap.quasiMeasurePreserving.ae hAE)
  filter_upwards [hAEslice,hSlices] with t ht hS
  filter_upwards [ht,hS] with z hz hR
  exact hz.symm.trans hR

/-- The classical chart solution represents the actual heat at EVERY
time in the positive slab on every relatively compact inner chart domain. -/
theorem scalarHeat_chartClassicalRepresentative (hn : 0 < n)
    (g : SmoothMetric M) (hK : IsKahler g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (x : M.Carrier)
    {O V : Set (ComplexVector n)} (hO : IsOpen O) (hOc : IsCompact (closure O))
    (hOt : closure O ⊆ chartTarget x) (hV : IsOpen V) (hVc : IsCompact (closure V))
    (hVO : closure V ⊆ O) {l r : ℝ} (hl : 0 < l) (hlr : l < r) (f : Lp ℝ 2 μ) :
    ∃ v : Parabolic.Point n → ℝ, ContDiffOn ℝ ∞ v (O ×ˢ Set.Ioo l r) ∧
      (∀ t ∈ Set.Ioo l r, (fun z => v (z,t)) =ᵐ[volume.restrict V]
        (fun z => (scalarHeatFamily g μ hμ t f) (chartInv x z))) ∧
      ∀ p ∈ O ×ˢ Set.Ioo l r,
        Parabolic.linearOp (O ×ˢ Set.Ioo l r) (scalarHeatChartCoeff g x) (fun _ _ => 0) v p = 0 := by
  obtain ⟨v,hv,hAE,hClass⟩ := scalarHeat_chartInteriorRepresentative hn g hK μ hμ x hO hOc hOt hl hlr f
  exact ⟨v,hv,scalarHeat_chart_smoothSlice_every_time g μ hμ x hO hOc hOt hV hVc hVO hl f hv hAE,hClass⟩

end Yau.LeafProofs.L19Aux
