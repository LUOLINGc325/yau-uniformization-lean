import Yau.Proofs.P03TopRepresentativeOverlap

open scoped Manifold Topology ContDiff
open MeasureTheory Bundle

noncomputable section

namespace Yau.NodeProofs.P03Aux

open Yau.BundleDbar Yau.LeafProofs.L14Aux

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

theorem bundleChartSource_self (x : M.Carrier) :
    x ∈ bundleChartSource (r := r) E x :=
  ⟨mem_extChartAt_source x, FiberBundle.mem_baseSet_trivializationAt' x⟩

/-- The local tensor representatives glue to one global holomorphic top
form, and its equality to the given measurable tensor uses a countable cover. -/
theorem glue_holomorphic_top_representatives
    (g : Yau.SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (hE : Holomorphic (r := r) E)
    (u : NQForm E 0) (F : M.Carrier → ComplexVector n → ComplexVector r)
    (hF : ∀ a, DifferentiableOn ℂ (F a) (localDomain (r := r) E a))
    (hae : ∀ a, (fun z => coefficients (r := r) E u a z Fin.elim0)
      =ᵐ[(lebesgueC n).restrict (localDomain (r := r) E a)] F a) :
    ∃ v : NQForm E 0, HolomorphicTopForm (r := r) E v ∧ ∀ᵐ x ∂μ, v x = u x := by
  let v : NQForm E 0 := fun x => topFormPushforward (r := r) E x (F x) x
  have hveq (a : M.Carrier) (x : M.Carrier)
      (hx : x ∈ bundleChartSource (r := r) E a) :
      v x = topFormPushforward (r := r) E a (F a) x :=
    topFormPushforward_eqOn_overlap E g μ hμ hE u x a (F x) (F a)
      (hF x) (hF a) (hae x) (hae a) x ⟨bundleChartSource_self E x, hx⟩
  have hcoeff (a : M.Carrier) (z : ComplexVector n)
      (hz : z ∈ localDomain (r := r) E a) :
      coefficients (r := r) E v a z Fin.elim0 = F a z := by
    have hx : chartInv a z ∈ bundleChartSource (r := r) E a :=
      ⟨(extChartAt (ComplexModel n) a).map_target hz.1, hz.2⟩
    have hp := hveq a (chartInv a z) hx
    have he : coefficients (r := r) E v a z Fin.elim0 =
        coefficients (r := r) E (topFormPushforward (r := r) E a (F a)) a z Fin.elim0 := by
      unfold coefficients
      rw [hp]
    exact he.trans (topFormPushforward_coefficients E a (F a) z hz)
  refine ⟨v, ?_, ?_⟩
  · intro a α
    exact ((differentiableOn_piLp (𝕜 := ℂ) 2).mp (hF a) α).congr
      fun z hz => congrArg (fun w : ComplexVector r => w α) (hcoeff a z hz)
  · apply ae_of_bundleCharts (r := r) E g.form μ hμ (fun x => v x = u x)
    intro a
    have hlocal : ∀ᵐ x ∂μ.restrict (bundleChartSource (r := r) E a), v x = u x := by
      filter_upwards [topFormPushforward_ae_eq_local E g.form μ hμ u a (F a) (hae a),
        ae_restrict_mem (bundleChartSource_isOpen (r := r) E a).measurableSet] with x hx hxdom
      exact (hveq a x hxdom).trans hx
    have ht := (chartInvExtension_quasiMeasurePreserving (r := r) E g μ hμ a).ae hlocal
    filter_upwards [ht, ae_restrict_mem (localDomain_isOpen E a).measurableSet] with z hz hzdom
    have hi : Yau.LeafProofs.chartInvExtension a z = chartInv a z := by
      exact if_pos hzdom.1
    rw [hi] at hz
    exact hz

end Yau.NodeProofs.P03Aux
