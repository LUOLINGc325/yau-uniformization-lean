import Yau.Proofs.F01SpatialDerivativeWords
import Yau.Proofs.F01LinearSpatialCommutator

/-! Every finite spatial derivative word satisfies the same genuine
principal operator. Its forcing is defined recursively by the actual
coefficient derivatives and actual preceding Hessians, not supplied as data. -/
noncomputable section
open Set
open scoped ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ}

def linearCommutatorSource (a : Point n → Mat n) (u f : Point n → ℝ) :
    List (Space n) → Point n → ℝ
  | [] => f
  | v :: vs => fun p =>
      realHessianContractionCLM (fderiv ℝ (fun z => a (z, p.2)) p.1 v)
        (spatialDD (spatialDerivativeWord vs u) p) +
      fderiv ℝ (fun z => linearCommutatorSource a u f vs (z, p.2)) p.1 v

theorem linearCommutatorSource_smooth_slice
    (a : Point n → Mat n) (u f : Point n → ℝ) {O : Set (Space n)} {T : ℝ}
    (hO : IsOpen O) (hT : 0 < T) (hu : ContDiffOn ℝ ∞ u (O ×ˢ Icc 0 T))
    (ha : ∀ t ∈ Icc 0 T, ContDiffOn ℝ ∞ (fun x => a (x, t)) O)
    (hf : ∀ t ∈ Icc 0 T, ContDiffOn ℝ ∞ (fun x => f (x, t)) O)
    (vs : List (Space n)) :
    ∀ t ∈ Icc 0 T, ContDiffOn ℝ ∞ (fun x => linearCommutatorSource a u f vs (x, t)) O := by
  induction vs with
  | nil => exact hf
  | cons v vs ih =>
    intro t ht
    have hA : ContDiffOn ℝ ∞ (fun x => fderiv ℝ (fun z => a (z, t)) x v) O :=
      ((ha t ht).fderiv_of_isOpen hO (by simp)).clm_apply contDiffOn_const
    have hWord := contDiffOn_space_slice (spatialDerivativeWord_smooth hO hT hu vs) ht
    have hD : ContDiffOn ℝ ∞ (fderiv ℝ (fun x => spatialDerivativeWord vs u (x, t))) O :=
      hWord.fderiv_of_isOpen hO (by simp)
    have hDD : ContDiffOn ℝ ∞ (fderiv ℝ (fderiv ℝ (fun x => spatialDerivativeWord vs u (x, t)))) O :=
      hD.fderiv_of_isOpen hO (by simp)
    have hF : ContDiffOn ℝ ∞ (fun x => fderiv ℝ (fun z => linearCommutatorSource a u f vs (z, t)) x v) O :=
      ((ih t ht).fderiv_of_isOpen hO (by simp)).clm_apply contDiffOn_const
    exact (((realHessianContractionCLM (n := n)).contDiff.comp_contDiffOn hA).clm_apply hDD).add hF

theorem iterated_linear_spatial_equation
    (a : Point n → Mat n) (u f : Point n → ℝ) {O : Set (Space n)} {T : ℝ}
    (hO : IsOpen O) (hT : 0 < T) (hu : ContDiffOn ℝ ∞ u (O ×ˢ Icc 0 T))
    (ha : ∀ t ∈ Icc 0 T, ContDiffOn ℝ ∞ (fun x => a (x, t)) O)
    (hf : ∀ t ∈ Icc 0 T, ContDiffOn ℝ ∞ (fun x => f (x, t)) O)
    (hEq : ∀ p ∈ O ×ˢ Icc 0 T, linearOp (O ×ˢ Icc 0 T) a (fun _ _ => 0) u p = f p)
    (vs : List (Space n)) :
    ∀ p ∈ O ×ˢ Icc 0 T,
      linearOp (O ×ˢ Icc 0 T) a (fun _ _ => 0) (spatialDerivativeWord vs u) p =
        linearCommutatorSource a u f vs p := by
  induction vs with
  | nil => exact hEq
  | cons v vs ih =>
    have hWord := spatialDerivativeWord_smooth hO hT hu vs
    have hSource := linearCommutatorSource_smooth_slice a u f hO hT hu ha hf vs
    have hJet : ∀ x ∈ O, ∀ t ∈ Icc 0 T,
        HasDerivWithinAt (fun s => spatialDerivativeWord vs u (x, s))
          (realHessianContractionCLM (a (x, t)) (spatialDD (spatialDerivativeWord vs u) (x, t)) +
            linearCommutatorSource a u f vs (x, t)) (Icc 0 T) t := by
      intro x hx t ht
      have hcurve : ContDiffOn ℝ ∞ (fun s => spatialDerivativeWord vs u (x, s)) (Icc 0 T) :=
        hWord.comp (contDiffOn_const.prodMk contDiffOn_id) (fun s hs => ⟨hx, hs⟩)
      have hd := ((hcurve t ht).differentiableWithinAt (by simp)).hasDerivWithinAt
      have he := ih (x, t) ⟨hx, ht⟩
      rw [linearOp_zero_drift_eq_contraction] at he
      have hs : {s : ℝ | (x, s) ∈ O ×ˢ Icc 0 T} = Icc 0 T := by
        ext s
        exact and_iff_right hx
      simp only [timeD, hs] at he
      have hv : derivWithin (fun s => spatialDerivativeWord vs u (x, s)) (Icc 0 T) t =
          realHessianContractionCLM (a (x, t)) (spatialDD (spatialDerivativeWord vs u) (x, t)) +
            linearCommutatorSource a u f vs (x, t) := by linarith
      exact hd.congr_deriv hv
    intro p hp
    exact linear_spatial_direction_commutator a (spatialDerivativeWord vs u)
      (linearCommutatorSource a u f vs) hO hT hWord ha hSource hJet v hp

end Yau.NodeProofs.F01Aux
