import Yau.Proofs.P04CanonicalRegularity

noncomputable section
open Filter
open scoped Topology ContDiff Manifold

namespace Yau.Proofs.P04Aux
open Yau Yau.LeafProofs
variable {n : ℕ} {M : ComplexManifold n}

/-- Continuity follows already from the actual holomorphic coefficients,
with no holomorphic regularity or nonzero-section premise. -/
theorem canonicalNormSq_continuous (g : SmoothMetric M) (S : CanonicalSection M)
    (hS : IsHolomorphicCanonical S) : Continuous (canonicalNormSq g.form S) := by
  have hc (a : M.Carrier) :
      ContinuousOn (inChart a (canonicalNormSq g.form S)) (chartTarget a) := by
    have hd : ContinuousOn (fun z => (hMat g.form a z).det.re) (chartTarget a) :=
      (Complex.reCLM.contDiff.comp_contDiffOn
        (L18Aux.contDiffOn_matrix_det (L18Aux.hMat_contDiffOn g a))).continuousOn
    apply (((hS a).continuousOn.norm.pow 2).div hd
      (fun z hz => (L18Aux.hMat_det_re_pos g.form a hz).ne')).congr
    intro z hz
    exact canonicalNormSq_inChart g.form S a hz
  rw [continuous_iff_continuousAt]
  intro x
  have hlocal := (hc x).continuousAt
    ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds (mem_extChartAt_target x))
  apply (hlocal.comp (continuousAt_extChartAt (I := ComplexModel n) x)).congr
  filter_upwards [(isOpen_extChartAt_source (I := ComplexModel n) x).mem_nhds
    (mem_extChartAt_source x)] with y hy
  exact congrArg (canonicalNormSq g.form S) ((extChartAt (ComplexModel n) x).left_inv hy)

end Yau.Proofs.P04Aux
