import Yau.Proofs.P03TopPushforwardRegularity
import Yau.Proofs.P03TopPushforwardAE

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

theorem topFormPushforward_coordinates_continuousOn
    (hE : Holomorphic (r := r) E) (a : M.Carrier)
    (F : ComplexVector n → ComplexVector r)
    (hF : DifferentiableOn ℂ F (localDomain (r := r) E a)) (b : M.Carrier) :
    ContinuousOn (fun x => coefficients (r := r) E
      (topFormPushforward (r := r) E a F) b (chartPt b x) Fin.elim0)
      (bundleChartSource (r := r) E a ∩ bundleChartSource (r := r) E b) := by
  intro x hx
  have hi := Yau.LeafProofs.chartInv_chartPt_of_mem b x
    (by simpa only [extChartAt_source] using hx.2.1)
  have ha : chartInv b (chartPt b x) ∈ bundleChartSource (r := r) E a := by
    rw [hi]
    exact hx.1
  have hd := topFormPushforward_coefficients_differentiableAt E hE a F hF b
    (chartPt_mem_localDomain E b x hx.2) ha
  have hcp : ContMDiffAt (ComplexModel n) (ComplexModel n) ∞ (chartPt b) x :=
    contMDiffAt_extChartAt' (I := ComplexModel n)
      (by simpa only [extChartAt_source] using hx.2.1)
  exact (hd.continuousAt.comp hcp.continuousAt).continuousWithinAt

/-- The local holomorphic representatives of one intrinsic tensor agree
pointwise on overlaps. Positivity comes from the original geometric volume. -/
theorem topFormPushforward_eqOn_overlap
    (g : Yau.SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (hE : Holomorphic (r := r) E)
    (u : NQForm E 0) (a b : M.Carrier)
    (F G : ComplexVector n → ComplexVector r)
    (hF : DifferentiableOn ℂ F (localDomain (r := r) E a))
    (hG : DifferentiableOn ℂ G (localDomain (r := r) E b))
    (ha : (fun z => coefficients (r := r) E u a z Fin.elim0)
      =ᵐ[(lebesgueC n).restrict (localDomain (r := r) E a)] F)
    (hb : (fun z => coefficients (r := r) E u b z Fin.elim0)
      =ᵐ[(lebesgueC n).restrict (localDomain (r := r) E b)] G) :
    ∀ x ∈ bundleChartSource (r := r) E a ∩ bundleChartSource (r := r) E b,
      topFormPushforward (r := r) E a F x = topFormPushforward (r := r) E b G x := by
  letI : μ.IsOpenPosMeasure := Yau.LeafProofs.L18Aux.riemannianVolume_isOpenPosMeasure g μ hμ
  let O := bundleChartSource (r := r) E a ∩ bundleChartSource (r := r) E b
  have hO : IsOpen O := (bundleChartSource_isOpen (r := r) E a).inter
    (bundleChartSource_isOpen (r := r) E b)
  have hla := ae_restrict_of_ae_restrict_of_subset (s := O) Set.inter_subset_left
    (topFormPushforward_ae_eq_local E g.form μ hμ u a F ha)
  have hlb := ae_restrict_of_ae_restrict_of_subset (s := O) Set.inter_subset_right
    (topFormPushforward_ae_eq_local E g.form μ hμ u b G hb)
  have he : (fun x => coefficients (r := r) E (topFormPushforward (r := r) E a F)
      a (chartPt a x) Fin.elim0) =ᵐ[μ.restrict O]
        (fun x => coefficients (r := r) E (topFormPushforward (r := r) E b G)
          a (chartPt a x) Fin.elim0) := by
    filter_upwards [hla, hlb, ae_restrict_mem hO.measurableSet] with x hxa hxb hx
    rw [← topTensorCoordinatesEquiv_at_chartPt E _ a x hx.1,
      ← topTensorCoordinatesEquiv_at_chartPt E _ a x hx.1, hxa, hxb]
  have hca := (topFormPushforward_coordinates_continuousOn E hE a F hF a).mono
    (show O ⊆ bundleChartSource (r := r) E a ∩ bundleChartSource (r := r) E a from
      fun _ hx => ⟨hx.1, hx.1⟩)
  have hcb := (topFormPushforward_coordinates_continuousOn E hE b G hG a).mono
    (show O ⊆ bundleChartSource (r := r) E b ∩ bundleChartSource (r := r) E a from
      fun _ hx => ⟨hx.2, hx.1⟩)
  have hpoint := μ.eqOn_open_of_ae_eq he hO hca hcb
  intro x hx
  apply (topTensorCoordinatesEquiv (r := r) E a x hx.1).injective
  rw [topTensorCoordinatesEquiv_at_chartPt E _ a x hx.1,
    topTensorCoordinatesEquiv_at_chartPt E _ a x hx.1]
  exact hpoint hx

end Yau.NodeProofs.P03Aux
