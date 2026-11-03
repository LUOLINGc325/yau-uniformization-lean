import Yau.Proofs.F03DirichletChartInterior
import Yau.LeafProofs.L19HeatRegularityChartTransport

/-! Actual interior chart cylinders for the constructed supported heat. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff Manifold InnerProductSpace
namespace Yau.Proofs.F03Aux
open Yau LeafProofs.L18Aux LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

/-- The actual chart interior of an open manifold domain is open. -/
theorem dirichletChartInterior_open (Ω : Set M.Carrier) (hΩ : IsOpen Ω)
    (x : M.Carrier) : IsOpen {z | z ∈ chartTarget x ∧ chartInv x z ∈ Ω} :=
  (continuousOn_extChartAt_symm (I := ComplexModel n) x).isOpen_inter_preimage
    (isOpen_extChartAt_target (I := ComplexModel n) x) hΩ

/-- Every actual interior point admits compactly buffered chart cylinders
and a classical representative of the same supported heat at every time. -/
theorem dirichletHeat_local_chart_data (hn : 0 < n)
    (g : SmoothMetric M) (hK : IsKahler g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (Ω : Set M.Carrier) (hΩ : IsOpen Ω)
    (f : Lp ℝ 2 (μ.restrict Ω)) (x : M.Carrier) (hx : x ∈ Ω)
    {t : ℝ} (ht : 0 < t) :
    ∃ (O V : Set (ComplexVector n)) (l r : ℝ) (v : Parabolic.Point n → ℝ),
      IsOpen O ∧ IsCompact (closure O) ∧ closure O ⊆ chartTarget x ∧
      chartInv x '' closure O ⊆ Ω ∧
      IsOpen V ∧ IsCompact (closure V) ∧ closure V ⊆ O ∧ chartPt x x ∈ V ∧
      0 < l ∧ l < t ∧ t < r ∧ ContDiffOn ℝ ∞ v (O ×ˢ Set.Ioo l r) ∧
      (∀ s ∈ Set.Ioo l r, (fun z => v (z,s)) =ᵐ[volume.restrict V]
        (fun z => (l2ZeroExtension μ Ω hΩ.measurableSet
          (dirichletHeat g μ hμ Ω s f)) (chartInv x z))) ∧
      ∀ p ∈ O ×ˢ Set.Ioo l r,
        Parabolic.linearOp (O ×ˢ Set.Ioo l r) (scalarHeatChartCoeff g x) (fun _ _ => 0) v p = 0 := by
  have hIn : chartPt x x ∈ {z | z ∈ chartTarget x ∧ chartInv x z ∈ Ω} := by
    refine ⟨mem_extChartAt_target x,?_⟩
    rw [show chartInv x (chartPt x x) = x from
      (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)]
    exact hx
  obtain ⟨O,hO,hxO,hOD,hOc⟩ := exists_open_between_and_isCompact_closure isCompact_singleton
    (dirichletChartInterior_open Ω hΩ x) (Set.singleton_subset_iff.mpr hIn)
  have hOt : closure O ⊆ chartTarget x := fun z hz => (hOD hz).1
  have hOΩ : chartInv x '' closure O ⊆ Ω := by
    rintro y ⟨z,hz,rfl⟩
    exact (hOD hz).2
  obtain ⟨V,hV,hxV,hVO,hVc⟩ := exists_open_between_and_isCompact_closure isCompact_singleton hO hxO
  have hl : 0 < t / 2 := half_pos ht
  have hlt : t / 2 < t := half_lt_self ht
  have htr : t < t + 1 := by linarith
  obtain ⟨v,hv,hAE,hClass⟩ := dirichletHeat_chartClassicalRepresentative hn g hK μ hμ Ω
    hΩ.measurableSet x hO hOc hOt ((Set.image_mono subset_closure).trans hOΩ)
    hV hVc hVO hl (hlt.trans htr) f
  exact ⟨O,V,t/2,t+1,v,hO,hOc,hOt,hOΩ,hV,hVc,hVO,hxV (Set.mem_singleton _),
    hl,hlt,htr,hv,hAE,hClass⟩

end Yau.Proofs.F03Aux
