import Yau.Proofs.P04CanonicalRegularity

noncomputable section
open Set Filter MeasureTheory Bundle
open scoped Topology Manifold ContDiff

namespace Yau.Proofs.P04Aux
open Yau Yau.LeafProofs
variable {n : ℕ} {M : ComplexManifold n}

def localCanonicalTop (a : M.Carrier) (f : ComplexVector n → ℂ) :
    BundleDbar.NQForm (CanonicalCoefficients M) 0 :=
  L14Aux.topFormPushforward (CanonicalCoefficients M) a (fun z => scalarToCoefficient (f z))

theorem coefficient_bundleChartSource (a : M.Carrier) :
    L14Aux.bundleChartSource (r := 1) (CanonicalCoefficients M) a = (extChartAt (ComplexModel n) a).source := by
  simp only [L14Aux.bundleChartSource,coefficient_localTriv,
    Bundle.Trivial.trivialization_baseSet,inter_univ]

theorem localCanonicalTop_coefficient (a : M.Carrier) (f : ComplexVector n → ℂ)
    {z : ComplexVector n} (hz : z ∈ chartTarget a) :
    BundleDbar.coefficients (r := 1) (CanonicalCoefficients M) (localCanonicalTop a f) a z Fin.elim0 0=f z := by
  have hz' : z ∈ BundleDbar.localDomain (r := 1) (CanonicalCoefficients M) a := by
    rwa [coefficient_localDomain]
  have H := congrArg (fun v : ComplexVector 1 => v 0)
    (L14Aux.topFormPushforward_coefficients (CanonicalCoefficients M) a
      (fun z => scalarToCoefficient (f z)) z hz')
  exact H.trans (scalarToCoefficient_apply _ _)

set_option backward.isDefEq.respectTransparency false in
/-- A local coefficient AE representative gives an AE representative of the
ACTUAL intrinsic tensor on that chart, via the exact volume transport. -/
theorem localCanonicalTop_ae_on_chart (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (a : M.Carrier)
    (u : BundleDbar.NQForm (CanonicalCoefficients M) 0) (f : ComplexVector n → ℂ)
    (hae : (fun z => BundleDbar.coefficients (r := 1) (CanonicalCoefficients M) u a z Fin.elim0 0)
      =ᵐ[(lebesgueC n).restrict (chartTarget a)] f) :
    ∀ᵐ x ∂μ.restrict ((extChartAt (ComplexModel n) a).source), u x=localCanonicalTop a f x := by
  have hq := L14Aux.chartPtExtension_quasiMeasurePreserving (r := 1) (CanonicalCoefficients M)
    g.form μ hμ a
  rw [coefficient_localDomain] at hq
  have ht := hq.ae hae
  rw [← coefficient_bundleChartSource a]
  filter_upwards [ht,ae_restrict_mem (L14Aux.bundleChartSource_isOpen (r := 1) (CanonicalCoefficients M) a).measurableSet]
    with x hx hxs
  have hz : chartPt a x ∈ chartTarget a := (extChartAt (ComplexModel n) a).map_source hxs.1
  have hz' : chartPt a x ∈ BundleDbar.localDomain (r := 1) (CanonicalCoefficients M) a := by
    rwa [coefficient_localDomain]
  change BundleDbar.coefficients (CanonicalCoefficients M) u a
    (L14Aux.chartPtExtension a x) Fin.elim0 0=f (L14Aux.chartPtExtension a x) at hx
  rw [L14Aux.chartPtExtension,if_pos hxs.1] at hx
  apply (L14Aux.topTensorCoordinatesEquiv (CanonicalCoefficients M) a x hxs).injective
  have hcoords (v : BundleDbar.NQForm (CanonicalCoefficients M) 0) :
      L14Aux.topTensorCoordinatesEquiv (CanonicalCoefficients M) a x hxs (v x) =
        BundleDbar.coefficients (CanonicalCoefficients M) v a (chartPt a x) Fin.elim0 := by
    rw [L14Aux.topTensorCoordinatesEquiv_apply,L14Aux.topTensorValueEquiv_form]
    ext α
    rw [L14Aux.coefficients_topFormValue]
    have hpoint : chartInv a (chartPt a x)=x := (extChartAt (ComplexModel n) a).left_inv hxs.1
    rw [hpoint]
  rw [hcoords,hcoords]
  ext α
  have hα : α=(0 : Fin 1) := Subsingleton.elim _ _
  subst α
  exact hx.trans (localCanonicalTop_coefficient a f hz).symm

end Yau.Proofs.P04Aux
