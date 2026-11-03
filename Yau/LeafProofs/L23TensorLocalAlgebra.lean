import Yau.LeafProofs.L23TensorChart
import Yau.LeafProofs.L23CurvatureCalculus

/-! Local equality and linearity for the original covariant derivative. -/

noncomputable section
open Filter
open scoped Topology ContDiff

namespace Yau.LeafProofs.L23Aux
open L18Aux L19Aux
set_option backward.isDefEq.respectTransparency false

variable {n r : ℕ} {M : ComplexManifold n}

theorem covariantD_eventuallyEq (h : HermitianField M) (c : M.Carrier)
    (A B : ComplexVector n → CovTensor n r) (z : ComplexVector n)
    (hAB : A=ᶠ[𝓝 z] B) : covariantD h c A z=covariantD h c B z := by
  funext v
  have heq : (fun w => A w (fun j => v j.succ))=ᶠ[𝓝 z]
      (fun w => B w (fun j => v j.succ)) := hAB.mono (fun _ hw => congrFun hw _)
  simp only [covariantD,rDeriv,heq.fderiv_eq,hAB.self_of_nhds]

theorem covariantD_add_at (h : HermitianField M) (c : M.Carrier)
    (A B : ComplexVector n → CovTensor n r) (z : ComplexVector n)
    (hA : ∀ v, DifferentiableAt ℝ (fun w => A w v) z)
    (hB : ∀ v, DifferentiableAt ℝ (fun w => B w v) z) :
    covariantD h c (fun w => A w+B w) z=covariantD h c A z+covariantD h c B z := by
  funext v
  simp only [covariantD,Pi.add_apply]
  rw [rDeriv_add (hA _) (hB _)]
  simp only [mul_add,Finset.sum_add_distrib]
  ring

theorem covariantD_sub_at (h : HermitianField M) (c : M.Carrier)
    (A B : ComplexVector n → CovTensor n r) (z : ComplexVector n)
    (hA : ∀ v, DifferentiableAt ℝ (fun w => A w v) z)
    (hB : ∀ v, DifferentiableAt ℝ (fun w => B w v) z) :
    covariantD h c (fun w => A w-B w) z=covariantD h c A z-covariantD h c B z := by
  funext v
  simp only [covariantD,Pi.sub_apply]
  rw [rDeriv_sub (hA _) (hB _)]
  simp only [mul_sub,Finset.sum_sub_distrib]
  ring

theorem covariantD_const_mul_at (h : HermitianField M) (c : M.Carrier)
    (A : ComplexVector n → CovTensor n r) (z : ComplexVector n)
    (hA : ∀ v, DifferentiableAt ℝ (fun w => A w v) z) (a : ℝ) :
    covariantD h c (fun w v => a*A w v) z=fun v => a*covariantD h c A z v := by
  funext v
  change rDeriv (fun w => a*A w (fun j => v j.succ)) z (v 0)-
    (∑ j, ∑ p, christoffel h c z p (v 0) (v j.succ)*
      (a*A z (Function.update (fun j => v j.succ) j p)))=
        a*(rDeriv (fun w => A w (fun j => v j.succ)) z (v 0)-
          ∑ j, ∑ p, christoffel h c z p (v 0) (v j.succ)*
            A z (Function.update (fun j => v j.succ) j p))
  rw [rDeriv_const_mul (hA _) a]
  simp only [mul_sub,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro p _
  ring

end Yau.LeafProofs.L23Aux
