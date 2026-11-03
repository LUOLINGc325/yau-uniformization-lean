import Yau.LeafProofs.L21GraphBrackets
import Yau.LeafProofs.L21WirtingerGraph

/-! Derivatives of the actual graph fields and their matrix coefficients. -/

open scoped ContDiff
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

def graphR (C : X n → X n →L[ℝ] X n) (v : X n) : X n → X n :=
  fun x => graphReal (C x) v

def graphS (C : X n → X n →L[ℝ] X n) (v : X n) : X n → X n :=
  fun x => graphImag (C x) v

theorem differentiableAt_graphR
    {C : X n → X n →L[ℝ] X n} {x : X n}
    (hC : DifferentiableAt ℝ C x) (v : X n) :
    DifferentiableAt ℝ (graphR C v) x := by
  change DifferentiableAt ℝ (fun y => (1 / 2 : ℝ) • (v + C y v)) x
  exact ((hC.clm_apply (differentiableAt_const v)).const_add v).const_smul (1 / 2 : ℝ)

theorem fderiv_graphR
    {C : X n → X n →L[ℝ] X n} {x : X n}
    (hC : DifferentiableAt ℝ C x) (v : X n) :
    fderiv ℝ (graphR C v) x = (1 / 2 : ℝ) • (fderiv ℝ C x).flip v := by
  have hd : HasFDerivAt (fun y => C y v) ((fderiv ℝ C x).flip v) x := by
    rw [← fderiv_structure_apply_const hC]
    exact (hC.clm_apply (differentiableAt_const v)).hasFDerivAt
  exact ((hd.const_add v).const_smul (1 / 2 : ℝ)).fderiv

theorem fderiv_graphS
    {C : X n → X n →L[ℝ] X n} {x : X n}
    (hC : DifferentiableAt ℝ C x) (v : X n) :
    fderiv ℝ (graphS C v) x = -Complex.I • fderiv ℝ (graphR C v) x := by
  have hd : HasFDerivAt (fun y => C y v) ((fderiv ℝ C x).flip v) x := by
    rw [← fderiv_structure_apply_const hC]
    exact (hC.clm_apply (differentiableAt_const v)).hasFDerivAt
  have he : fderiv ℝ (graphS C v) x =
      (1 / 2 : ℝ) • (Complex.I • (-(fderiv ℝ C x).flip v)) :=
    (((hd.const_sub v).const_smul Complex.I).const_smul (1 / 2 : ℝ)).fderiv
  rw [he, fderiv_graphR hC]
  ext u
  simp only [_root_.smul_apply, _root_.neg_apply, smul_neg, neg_smul]
  rw [smul_comm]

theorem graph_coefficient_bracket
    {C : X n → X n →L[ℝ] X n} {x : X n}
    (hC : DifferentiableAt ℝ C x) (v w : X n) :
    (fderiv ℝ C x (graphR C v x) w +
      Complex.I • fderiv ℝ C x (graphS C v x) w) -
      (fderiv ℝ C x (graphR C w x) v +
        Complex.I • fderiv ℝ C x (graphS C w x) v) =
    (2 : ℝ) • (Yau.LeafCandidates.bracket (graphR C v) (graphR C w) x -
      Yau.LeafCandidates.bracket (graphS C v) (graphS C w) x) := by
  simp only [Yau.LeafCandidates.bracket, fderiv_graphR hC, fderiv_graphS hC,
    _root_.smul_apply, ContinuousLinearMap.flip_apply]
  module

theorem dbarA_graph_component
    {G : X n → X n} {x : X n} (hG : DifferentiableAt ℝ G x)
    (C : X n → X n →L[ℝ] X n) (i k : Fin n) :
    dbarA (graphMatrix C) i (fun y => G y k) x =
      (fderiv ℝ G x (graphR C (Yau.stdVec i) x) +
        Complex.I • fderiv ℝ G x (graphS C (Yau.stdVec i) x)) k := by
  let pr : X n →L[ℝ] ℂ := (EuclideanSpace.proj k).restrictScalars ℝ
  have hd : fderiv ℝ (fun y => G y k) x = pr.comp (fderiv ℝ G x) :=
    (pr.hasFDerivAt.comp x hG.hasFDerivAt).fderiv
  rw [dbarA_graphMatrix_eq, hd]
  rfl

theorem contDiffAt_cayleyMap
    {J : X n → X n →L[ℝ] X n} {x : X n}
    (hJ : ContDiffAt ℝ ∞ J x) (hi : (J x + stdComplex n).IsInvertible) :
    ContDiffAt ℝ ∞ (fun y => cayleyMap (J y)) x := by
  exact (hi.contDiffAt_map_inverse.comp x (hJ.add contDiffAt_const)).clm_comp
    (contDiffAt_const.sub hJ)

end Yau.LeafProofs.L21Aux
