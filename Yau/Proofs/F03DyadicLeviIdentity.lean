import Yau.Proofs.F03LeviScalarCalculus
import Yau.Proofs.F03GradientLocality
import Yau.LeafProofs.L22Locality

/-! The exact finite local product formula for the actual dyadic Levi matrix. -/
noncomputable section
open Filter Set
open scoped Topology ContDiff ComplexOrder Matrix
namespace Yau.Proofs.F03Aux
open Yau Blueprint
variable {n : ℕ} {M : ComplexManifold n}

theorem scalarFirstCovector_scalar_comp {f : M.Carrier → ℝ} (hf : SmoothFn f)
    (F : ℝ → ℝ) (hF : ContDiff ℝ ∞ F) (x : M.Carrier) :
    scalarFirstCovector (fun y => F (f y)) x=
      Complex.ofReal (deriv F (f x)) • scalarFirstCovector f x := by
  have hinv : chartInv x (chartPt x x)=x := (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  have hOuter : HasDerivAt F (deriv F (f x)) (inChart x f (chartPt x x)) := by
    simpa only [inChart,hinv] using (hF.differentiable (by simp) (f x)).hasDerivAt
  have hD := hOuter.comp_hasFDerivAt (chartPt x x) (smoothFn_center_differentiableAt hf x).hasFDerivAt
  change realFirstCovector (F ∘ inChart x f) (chartPt x x)=_
  unfold scalarFirstCovector realFirstCovector
  rw [hD.fderiv]
  ext i
  simp only [ContinuousLinearMap.smul_apply,smul_eq_mul,Complex.ofReal_mul,Pi.smul_apply]
  ring

theorem dyadicProfile_covector_zero (u : M.Carrier → ℝ) (hu : SmoothFn u) (j : ℕ)
    (x : M.Carrier) (hZero : deriv (dyadicPartition j) (u x)=0) :
    scalarFirstCovector (fun y => dyadicPartition j (u y)) x=0 := by
  rw [scalarFirstCovector_scalar_comp hu (dyadicPartition j) (dyadicPartition_contDiff j),hZero,
    Complex.ofReal_zero,zero_smul]

theorem dyadicProfile_levi_zero (u : M.Carrier → ℝ) (hu : SmoothFn u) (j : ℕ)
    (x : M.Carrier) (hZero : deriv (dyadicPartition j) (u x)=0)
    (hZero' : deriv (deriv (dyadicPartition j)) (u x)=0) :
    levi (fun y => dyadicPartition j (u y)) x=0 := by
  rw [levi_real_scalar_comp hu (dyadicPartition j) (dyadicPartition_contDiff j),hZero,hZero',
    Complex.ofReal_zero,zero_smul,zero_add]
  simp only [zero_smul]

theorem dyadicGluing_levi_finite_identity (u : M.Carrier → ℝ) (hu : SmoothFn u)
    (F : ℕ → M.Carrier → ℝ → ℝ) (t : ℝ) (hF : ∀ j,SmoothFn (fun y => F j y t))
    (x : M.Carrier) (hx : 1 ≤ u x) :
    ∃ N : ℕ,(∑ j ∈ Finset.range (N+1),dyadicPartition j (u x))=1 ∧
      levi (fun y => dyadicGluing u F y t) x=
        ∑ j ∈ Finset.range (N+1),
          (Complex.ofReal (dyadicPartition j (u x)) • levi (fun y => F j y t) x+
            Complex.ofReal (F j x t) • levi (fun y => dyadicPartition j (u y)) x+
            Matrix.vecMulVec (star (scalarFirstCovector (fun y => dyadicPartition j (u y)) x))
              (scalarFirstCovector (fun y => F j y t) x)+
            Matrix.vecMulVec (star (scalarFirstCovector (fun y => F j y t) x))
              (scalarFirstCovector (fun y => dyadicPartition j (u y)) x)) := by
  obtain ⟨N,hN,hEq⟩ := dyadicGluing_local_finite_partition u hu F x hx t
  refine ⟨N,hN,?_⟩
  rw [LeafProofs.L22Aux.levi_congr_of_eventuallyEq hEq]
  have hProfile (j : ℕ) : SmoothFn (fun y => dyadicPartition j (u y)) :=
    fun a => (dyadicPartition_contDiff j).comp_contDiffOn (hu a)
  have hProd (j : ℕ) : SmoothFn (fun y => dyadicPartition j (u y)*F j y t) :=
    fun a => (hProfile j a).mul (hF j a)
  rw [levi_real_sum _ hProd]
  exact Finset.sum_congr rfl (fun j _ => levi_real_mul (hProfile j) (hF j) x)

end Yau.Proofs.F03Aux
