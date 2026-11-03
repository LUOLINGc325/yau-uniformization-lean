import Yau.Proofs.P03TangentTransitions

open scoped Manifold Topology ContDiff

noncomputable section

namespace Yau.NodeProofs.P03Aux

variable {n : ℕ} {M : ComplexManifold n}

theorem determinantOfCLM_contDiff :
    ContDiff ℂ ⊤ (fun L : ComplexVector n →L[ℂ] ComplexVector n =>
      Matrix.det (fun i j => L (stdVec j) i)) := by
  classical
  have he : (fun L : ComplexVector n →L[ℂ] ComplexVector n =>
      Matrix.det (fun i j => L (stdVec j) i)) =
      fun L => ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ∏ i, L (stdVec i) (σ i) := by
    funext L
    exact Matrix.det_apply' _
  rw [he]
  fun_prop

theorem determinantTransitionDet_contMDiffOn (a b : M.Carrier) :
    ContMDiffOn (ComplexModel n) 𝓘(ℂ, ℂ) ⊤
      (fun x => (determinantTransitionMatrix a b x).det)
      ((extChartAt (ComplexModel n) a).source ∩
        (extChartAt (ComplexModel n) b).source) := by
  have hp := (contMDiff_iff_contDiff.mpr (determinantOfCLM_contDiff (n := n)))
  exact hp.comp_contMDiffOn (determinantTransition_contMDiffOn a b)

def antiCanonicalTransition (a b x : M.Carrier) : ComplexVector 1 →L[ℂ] ComplexVector 1 :=
  (determinantTransitionMatrix a b x).det • ContinuousLinearMap.id ℂ _

def tangentAntiCanonicalTransition (a b x : M.Carrier) : ComplexVector n →L[ℂ] ComplexVector n :=
  (determinantTransitionMatrix a b x).det • determinantTransition a b x

theorem antiCanonicalTransition_contMDiffOn (a b : M.Carrier) :
    ContMDiffOn (ComplexModel n) 𝓘(ℂ, ComplexVector 1 →L[ℂ] ComplexVector 1) ⊤
      (antiCanonicalTransition a b)
      ((extChartAt (ComplexModel n) a).source ∩
        (extChartAt (ComplexModel n) b).source) :=
  (determinantTransitionDet_contMDiffOn a b).smul contMDiffOn_const

theorem tangentAntiCanonicalTransition_contMDiffOn (a b : M.Carrier) :
    ContMDiffOn (ComplexModel n) 𝓘(ℂ, ComplexVector n →L[ℂ] ComplexVector n) ⊤
      (tangentAntiCanonicalTransition a b)
      ((extChartAt (ComplexModel n) a).source ∩
        (extChartAt (ComplexModel n) b).source) :=
  (determinantTransitionDet_contMDiffOn a b).smul (determinantTransition_contMDiffOn a b)

end Yau.NodeProofs.P03Aux
