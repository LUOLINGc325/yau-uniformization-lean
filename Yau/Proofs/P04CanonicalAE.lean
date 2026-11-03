import Yau.Proofs.P04CanonicalOverlapAE

noncomputable section
open Set Filter MeasureTheory Bundle
open scoped Topology Manifold ContDiff

namespace Yau.Proofs.P04Aux
open Yau Yau.LeafProofs
variable {n : ℕ} {M : ComplexManifold n}

/-- An intrinsic AE identity gives the actual coefficient AE identity in
each original chart, using the genuine positive Riemannian density. -/
theorem canonical_coefficients_ae (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ)
    (u v : BundleDbar.NQForm (CanonicalCoefficients M) 0)
    (hae : ∀ᵐ x ∂μ, u x=v x) (a : M.Carrier) :
    (fun z => BundleDbar.coefficients (r := 1) (CanonicalCoefficients M) u a z Fin.elim0 0)
      =ᵐ[(lebesgueC n).restrict (chartTarget a)]
    (fun z => BundleDbar.coefficients (r := 1) (CanonicalCoefficients M) v a z Fin.elim0 0) := by
  have hlocal : ∀ᵐ x ∂μ.restrict (L14Aux.bundleChartSource (r := 1) (CanonicalCoefficients M) a),
      u x=v x := ae_restrict_of_ae hae
  have hz := (L14Aux.chartInvExtension_quasiMeasurePreserving (CanonicalCoefficients M)
    g μ hμ a).ae hlocal
  rw [coefficient_localDomain] at hz
  filter_upwards [hz,ae_restrict_mem (isOpen_extChartAt_target a).measurableSet] with z hx hzs
  rw [Yau.LeafProofs.chartInvExtension,if_pos hzs] at hx
  unfold BundleDbar.coefficients
  rw [hx]

theorem canonical_coefficients_sub
    (u v : BundleDbar.NQForm (CanonicalCoefficients M) 0)
    (a : M.Carrier) (z : ComplexVector n) :
    BundleDbar.coefficients (r := 1) (CanonicalCoefficients M) (u-v) a z Fin.elim0 0 =
      BundleDbar.coefficients (r := 1) (CanonicalCoefficients M) u a z Fin.elim0 0-
      BundleDbar.coefficients (r := 1) (CanonicalCoefficients M) v a z Fin.elim0 0 := by
  simp only [BundleDbar.coefficients,L14Aux.nqForm_sub_apply,AlternatingMap.sub_apply,
    map_sub,PiLp.sub_apply]

theorem canonical_ne_zero_of_coefficient_one (S : CanonicalSection M) (p : M.Carrier)
    (h : canonicalCoeff S p (chartPt p p)=1) : S p ≠ 0 := by
  intro hzero
  have hi : chartInv p (chartPt p p)=p :=
    (extChartAt (ComplexModel n) p).left_inv (mem_extChartAt_source p)
  unfold canonicalCoeff at h
  rw [hi,hzero] at h
  simpa using h

end Yau.Proofs.P04Aux
