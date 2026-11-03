import Yau.Proofs.F01CommutatorWordPairs
import Yau.Proofs.F01SpatialWordHessian
import Yau.Proofs.F01IteratedLinearCommutator

/-! The actual recursive forcing equals a finite sum with at least one
coefficient derivative in every commutator term. The principal Hessian
is absent from this sum, with no higher-jet or solver premise. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ}

theorem linearCommutatorSource_expansion (a : Point n → Mat n) (u f : Point n → ℝ)
    {S : Set (Space n)} {t : ℝ} (hS : IsOpen S)
    (ha : ContDiffOn ℝ ∞ (fun z => a (z, t)) S)
    (hu : ContDiffOn ℝ ∞ (fun z => u (z, t)) S)
    (hf : ContDiffOn ℝ ∞ (fun z => f (z, t)) S)
    (vs : List (Space n)) {x : Space n} (hx : x ∈ S) :
    linearCommutatorSource a u f vs (x, t) = spatialDerivativeWord vs f (x, t) +
      ((linearSpatialCommutatorPairs vs).map (fun ab =>
        realHessianContractionCLM (spatialDerivativeWord ab.1 a (x, t))
          (spatialDD (spatialDerivativeWord ab.2 u) (x, t)))).sum := by
  induction vs generalizing x with
  | nil => simp [linearCommutatorSource, linearSpatialCommutatorPairs, spatialDerivativeWord]
  | cons v vs ih =>
    let terms := linearSpatialCommutatorPairs vs
    let H (bs : List (Space n)) (z : Space n) := spatialDD (spatialDerivativeWord bs u) (z, t)
    have hHs (bs : List (Space n)) : ContDiffOn ℝ ∞ (H bs) S := by
      have hw := spatialDerivativeWord_smooth_slice hS hu bs
      have hDw : ContDiffOn ℝ ∞ (fderiv ℝ (fun z => spatialDerivativeWord bs u (z, t))) S :=
        hw.fderiv_of_isOpen hS (by simp)
      exact hDw.fderiv_of_isOpen hS (by simp)
    let D (ab : List (Space n) × List (Space n)) : Space n →L[ℝ] ℝ :=
      fderiv ℝ (fun z => realHessianContractionCLM
        (spatialDerivativeWord ab.1 a (z, t)) (H ab.2 z)) x
    have hD (ab : List (Space n) × List (Space n)) :
        HasFDerivAt (fun z => realHessianContractionCLM
          (spatialDerivativeWord ab.1 a (z, t)) (H ab.2 z)) (D ab) x := by
      have hA := (realHessianContractionCLM (n := n)).contDiff.comp_contDiffOn
        (spatialDerivativeWord_smooth_slice hS ha ab.1)
      exact (((hA.clm_apply (hHs ab.2)).contDiffAt
        (hS.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt
    have hDval (ab : List (Space n) × List (Space n)) : D ab v =
        realHessianContractionCLM (spatialDerivativeWord ab.1 a (x, t))
          (spatialDD (spatialDerivativeWord (v :: ab.2) u) (x, t)) +
        realHessianContractionCLM (spatialDerivativeWord (v :: ab.1) a (x, t))
          (H ab.2 x) := by
      have hAd := ((spatialDerivativeWord_smooth_slice hS ha ab.1).contDiffAt
        (hS.mem_nhds hx)).differentiableAt (by simp)
      have hBd := ((hHs ab.2).contDiffAt (hS.mem_nhds hx)).differentiableAt (by simp)
      have hC : DifferentiableAt ℝ (fun z =>
          realHessianContractionCLM (spatialDerivativeWord ab.1 a (z, t))) x :=
        (realHessianContractionCLM (n := n)).differentiableAt.comp x hAd
      have hDC : fderiv ℝ (fun z =>
          realHessianContractionCLM (spatialDerivativeWord ab.1 a (z, t))) x v =
          realHessianContractionCLM (spatialDerivativeWord (v :: ab.1) a (x, t)) := by
        have hd := (realHessianContractionCLM (n := n)).hasFDerivAt.comp x hAd.hasFDerivAt
        exact congrArg (fun D : Space n →L[ℝ]
          ((Space n →L[ℝ] Space n →L[ℝ] ℝ) →L[ℝ] ℝ) => D v) hd.fderiv
      have hprod := congrArg (fun D : Space n →L[ℝ] ℝ => D v) (fderiv_clm_apply hC hBd)
      simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply] at hprod
      rw [hDC] at hprod
      have hess : fderiv ℝ (H ab.2) x v =
          spatialDD (spatialDerivativeWord (v :: ab.2) u) (x, t) :=
        (spatial_word_hessian_direction hS hu ab.2 v hx).symm
      rw [hess] at hprod
      exact hprod
    have hsum := hasFDerivAt_list_sum_native terms
      (fun ab z => realHessianContractionCLM
        (spatialDerivativeWord ab.1 a (z, t)) (H ab.2 z)) D (fun ab _ => hD ab)
    have he : (fun z => linearCommutatorSource a u f vs (z, t)) =ᶠ[𝓝 x]
        (fun z => spatialDerivativeWord vs f (z, t) +
          (terms.map (fun ab => realHessianContractionCLM
            (spatialDerivativeWord ab.1 a (z, t)) (H ab.2 z))).sum) := by
      filter_upwards [hS.mem_nhds hx] with z hz
      exact ih hz
    have hfd := ((spatialDerivativeWord_smooth_slice hS hf vs).contDiffAt
      (hS.mem_nhds hx)).differentiableAt (by simp)
    change realHessianContractionCLM (fderiv ℝ (fun z => a (z, t)) x v)
      (spatialDD (spatialDerivativeWord vs u) (x, t)) +
      fderiv ℝ (fun z => linearCommutatorSource a u f vs (z, t)) x v = _
    rw [he.fderiv_eq, fderiv_fun_add hfd hsum.differentiableAt, hsum.fderiv]
    have hEval (l : List (List (Space n) × List (Space n))) :
        (l.map D).sum v =
          (l.map (fun ab => realHessianContractionCLM
            (spatialDerivativeWord (v :: ab.1) a (x, t)) (H ab.2 x))).sum +
          (l.map (fun ab => realHessianContractionCLM
            (spatialDerivativeWord ab.1 a (x, t))
            (spatialDD (spatialDerivativeWord (v :: ab.2) u) (x, t)))).sum := by
      induction l with
      | nil => simp
      | cons ab l ihl =>
        simp only [List.map_cons, List.sum_cons, add_apply, ihl, hDval]
        abel
    simp only [add_apply]
    rw [hEval]
    simp only [linearSpatialCommutatorPairs, List.map_cons, List.sum_cons,
      List.map_append, List.sum_append, List.map_map]
    change _ = spatialDerivativeWord (v :: vs) f (x, t) +
      (realHessianContractionCLM (spatialDerivativeWord [v] a (x, t))
        (spatialDD (spatialDerivativeWord vs u) (x, t)) + _)
    change realHessianContractionCLM (spatialDerivativeWord [v] a (x, t))
      (spatialDD (spatialDerivativeWord vs u) (x, t)) +
      (spatialDerivativeWord (v :: vs) f (x, t) + _) = _
    abel

end Yau.NodeProofs.F01Aux
