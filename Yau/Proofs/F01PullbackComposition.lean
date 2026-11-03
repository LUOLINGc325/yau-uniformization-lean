import Yau.LeafProofs.L17ChartNaturality

/-! Composition of actual chart Gram matrices under genuine complex smooth
coordinate changes, with the native manifold derivative chain rule. -/
noncomputable section
open scoped Manifold ContDiff Matrix
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem mfderiv_coordinate_composition {e : ComplexVector n → M.Carrier}
    {T : ComplexVector n → ComplexVector n} {z : ComplexVector n}
    (he : MDifferentiableAt (ComplexModel n) (ComplexModel n) e (T z))
    (hT : ContDiffAt ℂ ∞ T z) (v : ComplexVector n) :
    mfderiv (ComplexModel n) (ComplexModel n) (e ∘ T) z v =
      mfderiv (ComplexModel n) (ComplexModel n) e (T z) (fderiv ℂ T z v) := by
  have hm := hT.contMDiffAt.mdifferentiableAt (by simp)
  have h := DFunLike.congr_fun (mfderiv_comp z he hm) v
  change mfderiv (ComplexModel n) (ComplexModel n) (e ∘ T) z v =
    mfderiv (ComplexModel n) (ComplexModel n) e (T z)
      (mfderiv (ComplexModel n) (ComplexModel n) T z v) at h
  rw [mfderiv_eq_fderiv] at h
  exact h

theorem pullbackMatrix_coordinate_composition (g : HermitianField M)
    {e : ComplexVector n → M.Carrier} {T : ComplexVector n → ComplexVector n}
    {z : ComplexVector n}
    (he : MDifferentiableAt (ComplexModel n) (ComplexModel n) e (T z))
    (hT : ContDiffAt ℂ ∞ T z) :
    pullbackMatrix g (e ∘ T) z =
      (linearMatrix (fderiv ℂ T z))ᴴ * pullbackMatrix g e (T z) *
        linearMatrix (fderiv ℂ T z) := by
  apply matrix_eq_of_quadratic_eq
  intro v
  rw [congruence_quadratic]
  have hv := linearMatrix_mulVec (fderiv ℂ T z) (WithLp.toLp 2 v)
  simp only [WithLp.ofLp_toLp] at hv
  rw [hv, pullbackMatrix_sesquilinear, pullbackMatrix_sesquilinear]
  exact congrArg₂ (g (e (T z))).toFun
    (mfderiv_coordinate_composition he hT (WithLp.toLp 2 v))
    (mfderiv_coordinate_composition he hT (WithLp.toLp 2 v))

end Yau.NodeProofs.F01Aux
