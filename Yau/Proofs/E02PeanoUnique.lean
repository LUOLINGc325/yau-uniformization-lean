import Yau.Proofs.E02PeanoMinimum
import Yau.Proofs.E02LocalPeano

open Set Filter Asymptotics
open scoped Topology ContDiff Asymptotics
noncomputable section
namespace Yau.NodeProofs.E02Aux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Symmetric Peano tensors are unique even when the derivative field of
f is not differentiable. The second Frechet derivative is identified only
in the separate theorem with an actual C² hypothesis below. -/
theorem realSecondJet_unique {f : E → ℝ} {x : E} {p q : E →L[ℝ] ℝ}
    {A B : E →L[ℝ] E →L[ℝ] ℝ} (hf : RealSecondJet f x p A) (hg : RealSecondJet f x q B) :
    p = q ∧ A = B := by
  have hSubtract {u v : E → ℝ} {pu pv : E →L[ℝ] ℝ} {Au Av : E →L[ℝ] E →L[ℝ] ℝ}
      (hu : RealSecondJet u x pu Au) (hv : RealSecondJet v x pv Av) :
      RealSecondJet (fun y => u y-v y) x (pu-pv) (Au-Av) := by
    refine ⟨?_,?_⟩
    · intro w z
      simp only [_root_.sub_apply]
      rw [hu.1 w z,hv.1 w z]
    · convert hu.2.sub hv.2 using 1
      funext y
      simp only [_root_.sub_apply]
      ring
  have hMin : IsLocalMin (fun y => f y-f y) x := Eventually.of_forall (fun _ => by simp)
  have hAB := realSecondJet_localMin_quadratic_nonneg (hSubtract hf hg) hMin
  have hBA := realSecondJet_localMin_quadratic_nonneg (hSubtract hg hf) hMin
  refine ⟨(realSecondJet_hasFDerivAt hf).unique (realSecondJet_hasFDerivAt hg),?_⟩
  have hDiag : ∀ v, A v v = B v v := by
    intro v
    have h1 := hAB v
    have h2 := hBA v
    change 0 ≤ A v v-B v v at h1
    change 0 ≤ B v v-A v v at h2
    linarith
  ext v w
  have hCross := hDiag (v+w)
  simp only [map_add,_root_.add_apply] at hCross
  linarith [hDiag v,hDiag w,hf.1 v w,hg.1 v w]

/-- Only a genuinely C² function permits the Peano tensor to be
identified with the actual second Frechet derivative. -/
theorem realSecondJet_second_fderiv_eq {f : E → ℝ} {x : E} {p : E →L[ℝ] ℝ}
    {A : E →L[ℝ] E →L[ℝ] ℝ} (hf : RealSecondJet f x p A) (hc : ContDiffAt ℝ 2 f x) :
    fderiv ℝ (fderiv ℝ f) x = A :=
  (realSecondJet_unique (realSecondJet_of_contDiffAt_two hc) hf).2

end Yau.NodeProofs.E02Aux
