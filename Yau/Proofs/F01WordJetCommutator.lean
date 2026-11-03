import Yau.Proofs.F01LinearCommutatorExpansion

/-! Spatial commutation needs smooth spatial slices and the genuine
first time jets of the spatial words. This applies on a zero-extended
initial cylinder without a jointly smooth time extension. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ}

theorem linearCommutatorSource_smooth_slice_of_slices
    (a : Point n → Mat n) (u f : Point n → ℝ) {S : Set (Space n)} {t : ℝ}
    (hS : IsOpen S) (ha : ContDiffOn ℝ ∞ (fun z => a (z, t)) S)
    (hu : ContDiffOn ℝ ∞ (fun z => u (z, t)) S)
    (hf : ContDiffOn ℝ ∞ (fun z => f (z, t)) S) (vs : List (Space n)) :
    ContDiffOn ℝ ∞ (fun z => linearCommutatorSource a u f vs (z, t)) S := by
  induction vs with
  | nil => exact hf
  | cons v vs ih =>
    have hA : ContDiffOn ℝ ∞ (fun z => fderiv ℝ (fun w => a (w, t)) z v) S :=
      (ha.fderiv_of_isOpen hS (by simp)).clm_apply contDiffOn_const
    have hw := spatialDerivativeWord_smooth_slice hS hu vs
    have hD : ContDiffOn ℝ ∞ (fderiv ℝ (fun z => spatialDerivativeWord vs u (z, t))) S :=
      hw.fderiv_of_isOpen hS (by simp)
    have hDD : ContDiffOn ℝ ∞
        (fderiv ℝ (fderiv ℝ (fun z => spatialDerivativeWord vs u (z, t)))) S :=
      hD.fderiv_of_isOpen hS (by simp)
    have hF : ContDiffOn ℝ ∞
        (fun z => fderiv ℝ (fun w => linearCommutatorSource a u f vs (w, t)) z v) S :=
      (ih.fderiv_of_isOpen hS (by simp)).clm_apply contDiffOn_const
    exact (((realHessianContractionCLM (n := n)).contDiff.comp_contDiffOn hA).clm_apply hDD).add hF

theorem iterated_linear_equation_of_word_jets
    (a : Point n → Mat n) (u P f : Point n → ℝ) {S : Set (Space n)} {l r : ℝ}
    (hS : IsOpen S) (hlr : l < r)
    (ha : ∀ t ∈ Icc l r, ContDiffOn ℝ ∞ (fun z => a (z, t)) S)
    (hu : ∀ t ∈ Icc l r, ContDiffOn ℝ ∞ (fun z => u (z, t)) S)
    (hf : ∀ t ∈ Icc l r, ContDiffOn ℝ ∞ (fun z => f (z, t)) S)
    (hJet : ∀ vs : List (Space n), ∀ x ∈ S, ∀ t ∈ Icc l r,
      HasDerivWithinAt (fun s => spatialDerivativeWord vs u (x, s))
        (spatialDerivativeWord vs P (x, t)) (Icc l r) t)
    (hEq : ∀ p ∈ S ×ˢ Icc l r, P p - realHessianContractionCLM (a p) (spatialDD u p) = f p)
    (vs : List (Space n)) :
    ∀ p ∈ S ×ˢ Icc l r, linearOp (S ×ˢ Icc l r) a (fun _ _ => 0)
      (spatialDerivativeWord vs u) p = linearCommutatorSource a u f vs p := by
  have hTime (ws : List (Space n)) (p : Point n) (hp : p ∈ S ×ˢ Icc l r) :
      timeD (S ×ˢ Icc l r) (spatialDerivativeWord ws u) p = spatialDerivativeWord ws P p := by
    have hSet : {s : ℝ | (p.1, s) ∈ S ×ˢ Icc l r} = Icc l r := by
      ext s
      exact and_iff_right hp.1
    simpa only [timeD, hSet] using
      (hJet ws p.1 hp.1 p.2 hp.2).derivWithin (uniqueDiffOn_Icc hlr p.2 hp.2)
  induction vs with
  | nil =>
    intro p hp
    rw [linearOp_zero_drift_eq_contraction, hTime [] p hp]
    exact hEq p hp
  | cons v vs ih =>
    intro p hp
    have hWord := spatialDerivativeWord_smooth_slice hS (hu p.2 hp.2) vs
    have hD : ContDiffOn ℝ ∞ (fderiv ℝ (fun z => spatialDerivativeWord vs u (z, p.2))) S :=
      hWord.fderiv_of_isOpen hS (by simp)
    have hDD : ContDiffOn ℝ ∞ (fderiv ℝ (fderiv ℝ
        (fun z => spatialDerivativeWord vs u (z, p.2)))) S := hD.fderiv_of_isOpen hS (by simp)
    have hAd := ((ha p.2 hp.2).contDiffAt (hS.mem_nhds hp.1)).differentiableAt (by simp)
    have hBd := (hDD.contDiffAt (hS.mem_nhds hp.1)).differentiableAt (by simp)
    have hC : DifferentiableAt ℝ (fun z => realHessianContractionCLM (a (z, p.2))) p.1 :=
      (realHessianContractionCLM (n := n)).differentiableAt.comp p.1 hAd
    have hDC : fderiv ℝ (fun z => realHessianContractionCLM (a (z, p.2))) p.1 v =
        realHessianContractionCLM (fderiv ℝ (fun z => a (z, p.2)) p.1 v) := by
      have hd := (realHessianContractionCLM (n := n)).hasFDerivAt.comp p.1 hAd.hasFDerivAt
      exact congrArg (fun D : Space n →L[ℝ]
        ((Space n →L[ℝ] Space n →L[ℝ] ℝ) →L[ℝ] ℝ) => D v) hd.fderiv
    have hBcomm : fderiv ℝ (fun z => spatialDD (spatialDerivativeWord vs u) (z, p.2)) p.1 v =
        spatialDD (spatialDerivativeWord (v :: vs) u) p :=
      (spatial_word_hessian_direction hS (hu p.2 hp.2) vs v hp.1).symm
    have hprod := congrArg (fun D : Space n →L[ℝ] ℝ => D v) (fderiv_clm_apply hC hBd)
    simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply] at hprod
    dsimp only [spatialDD] at hBcomm
    rw [hDC, hBcomm] at hprod
    have hSource := linearCommutatorSource_smooth_slice_of_slices a u f hS
      (ha p.2 hp.2) (hu p.2 hp.2) (hf p.2 hp.2) vs
    have he : (fun z => spatialDerivativeWord vs P (z, p.2)) =ᶠ[𝓝 p.1]
        (fun z => realHessianContractionCLM (a (z, p.2))
          (spatialDD (spatialDerivativeWord vs u) (z, p.2)) +
          linearCommutatorSource a u f vs (z, p.2)) := by
      filter_upwards [hS.mem_nhds hp.1] with z hz
      have hi := ih (z, p.2) ⟨hz, hp.2⟩
      rw [linearOp_zero_drift_eq_contraction, hTime vs (z, p.2) ⟨hz, hp.2⟩] at hi
      linarith
    have hd := congrArg (fun D : Space n →L[ℝ] ℝ => D v) he.fderiv_eq
    dsimp only [spatialDD] at hd
    rw [fderiv_fun_add (hC.clm_apply hBd)
      ((hSource.contDiffAt (hS.mem_nhds hp.1)).differentiableAt (by simp))] at hd
    simp only [add_apply] at hd
    rw [hprod] at hd
    change _ = realHessianContractionCLM (a p)
      (spatialDD (spatialDerivativeWord (v :: vs) u) p) +
      realHessianContractionCLM (fderiv ℝ (fun z => a (z, p.2)) p.1 v)
        (spatialDD (spatialDerivativeWord vs u) p) +
      fderiv ℝ (fun z => linearCommutatorSource a u f vs (z, p.2)) p.1 v at hd
    rw [linearOp_zero_drift_eq_contraction, hTime (v :: vs) p hp]
    change fderiv ℝ (fun z => spatialDerivativeWord vs P (z, p.2)) p.1 v -
      realHessianContractionCLM (a p) (spatialDD (spatialDerivativeWord (v :: vs) u) p) = _
    change _ = realHessianContractionCLM
      (fderiv ℝ (fun z => a (z, p.2)) p.1 v) (spatialDD (spatialDerivativeWord vs u) p) +
      fderiv ℝ (fun z => linearCommutatorSource a u f vs (z, p.2)) p.1 v
    linarith

end Yau.NodeProofs.F01Aux
