import Yau.Proofs.F01LeviSpatialCommutation
import Yau.Proofs.F01RealHessianContractionCLM
import Yau.Proofs.F01ClosedSpatialTimeJet

/-! Exact spatial differentiation of the real nondivergence equation.
Its principal coefficient is unchanged; the commutator source is the actual
derivative of that coefficient contracted with the original spatial Hessian. -/
noncomputable section
open Set
open scoped ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ}

theorem linearOp_zero_drift_eq_contraction (a : Point n → Mat n) (u : Point n → ℝ)
    (Q : Set (Point n)) (p : Point n) :
    linearOp Q a (fun _ _ => 0) u p = timeD Q u p - realHessianContractionCLM (a p) (spatialDD u p) := by
  rw [realHessianContractionCLM_apply]
  simp only [linearOp, zero_mul, Finset.sum_const_zero, sub_zero]

theorem linear_spatial_direction_commutator
    (a : Point n → Mat n) (u f : Point n → ℝ) {O : Set (Space n)} {T : ℝ}
    (hO : IsOpen O) (hT : 0 < T) (hu : ContDiffOn ℝ ∞ u (O ×ˢ Icc 0 T))
    (ha : ∀ t ∈ Icc 0 T, ContDiffOn ℝ ∞ (fun x => a (x, t)) O)
    (hf : ∀ t ∈ Icc 0 T, ContDiffOn ℝ ∞ (fun x => f (x, t)) O)
    (hpde : ∀ x ∈ O, ∀ t ∈ Icc 0 T,
      HasDerivWithinAt (fun s => u (x, s))
        (realHessianContractionCLM (a (x, t)) (spatialDD u (x, t)) + f (x, t)) (Icc 0 T) t)
    (v : Space n) {p : Point n} (hp : p ∈ O ×ˢ Icc 0 T) :
    linearOp (O ×ˢ Icc 0 T) a (fun _ _ => 0)
      (fun q => fderiv ℝ (fun z => u (z, q.2)) q.1 v) p =
      realHessianContractionCLM (fderiv ℝ (fun z => a (z, p.2)) p.1 v) (spatialDD u p) +
        fderiv ℝ (fun z => f (z, p.2)) p.1 v := by
  have hI := uniqueDiffOn_Icc hT
  have hUs : ContDiffOn ℝ ∞ (fun z => u (z, p.2)) O := contDiffOn_space_slice hu hp.2
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ (fun z => u (z, p.2))) O := hUs.fderiv_of_isOpen hO (by simp)
  have hB : ContDiffOn ℝ ∞ (fderiv ℝ (fderiv ℝ (fun z => u (z, p.2)))) O :=
    hD.fderiv_of_isOpen hO (by simp)
  have hBd := (hB.contDiffAt (hO.mem_nhds hp.1)).differentiableAt (by simp)
  have hAd := ((ha p.2 hp.2).contDiffAt (hO.mem_nhds hp.1)).differentiableAt (by simp)
  have hC : DifferentiableAt ℝ (fun z => realHessianContractionCLM (a (z, p.2))) p.1 :=
    (realHessianContractionCLM (n := n)).differentiableAt.comp p.1 hAd
  have hDC : fderiv ℝ (fun z => realHessianContractionCLM (a (z, p.2))) p.1 v =
      realHessianContractionCLM (fderiv ℝ (fun z => a (z, p.2)) p.1 v) := by
    have hd := (realHessianContractionCLM (n := n)).hasFDerivAt.comp p.1 hAd.hasFDerivAt
    exact congrArg (fun D : Space n →L[ℝ] ((Space n →L[ℝ] Space n →L[ℝ] ℝ) →L[ℝ] ℝ) => D v) hd.fderiv
  have hBcomm : fderiv ℝ (fderiv ℝ (fderiv ℝ (fun z => u (z, p.2)))) p.1 v =
      fderiv ℝ (fderiv ℝ (fun z => fderiv ℝ (fun w => u (w, p.2)) z v)) p.1 := by
    ext r s
    exact ((spatial_second_direction_commute hO hUs hp.1 v r s).trans
      (fderiv_bilinear_evaluation_const hBd r s v)).symm
  have hprod := congrArg (fun D : Space n →L[ℝ] ℝ => D v) (fderiv_clm_apply hC hBd)
  simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply] at hprod
  rw [hDC, hBcomm] at hprod
  have hDeriv : fderiv ℝ (fun z => realHessianContractionCLM (a (z, p.2)) (spatialDD u (z, p.2)) +
      f (z, p.2)) p.1 v =
      realHessianContractionCLM (a p)
        (spatialDD (fun q => fderiv ℝ (fun z => u (z, q.2)) q.1 v) p) +
      realHessianContractionCLM (fderiv ℝ (fun z => a (z, p.2)) p.1 v) (spatialDD u p) +
      fderiv ℝ (fun z => f (z, p.2)) p.1 v := by
    change fderiv ℝ (fun z => realHessianContractionCLM (a (z, p.2))
      (fderiv ℝ (fderiv ℝ (fun w => u (w, p.2))) z) + f (z, p.2)) p.1 v = _
    rw [fderiv_fun_add (hC.clm_apply hBd)
      (((hf p.2 hp.2).contDiffAt (hO.mem_nhds hp.1)).differentiableAt (by simp))]
    simp only [add_apply]
    exact congrArg (fun r : ℝ => r + fderiv ℝ (fun z => f (z, p.2)) p.1 v) hprod
  have hj := closed_space_direction_time_jet
    (P := fun q => realHessianContractionCLM (a q) (spatialDD u q) + f q)
    hO hT hu hpde hp.1 hp.2 v
  have hs : {s : ℝ | (p.1, s) ∈ O ×ˢ Icc 0 T} = Icc 0 T := by
    ext s
    exact and_iff_right hp.1
  rw [linearOp_zero_drift_eq_contraction]
  unfold timeD
  rw [hs, hj.derivWithin (hI p.2 hp.2), hDeriv]
  ring

end Yau.NodeProofs.F01Aux
