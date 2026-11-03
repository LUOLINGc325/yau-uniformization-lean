import Yau.Proofs.F03DualNormIntegral
import Yau.LeafProofs.L18

/-! A fixed real linear map sends the actual real differential to the paper's Wirtinger covector. -/
noncomputable section
open scoped ComplexOrder
namespace Yau.Proofs.F03Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def realWirtingerMap (n : ℕ) : (ComplexVector n →L[ℝ] ℝ) →L[ℝ] ComplexVector n := by
  let L : (ComplexVector n →L[ℝ] ℝ) →ₗ[ℝ] ComplexVector n :=
    { toFun := fun D => WithLp.toLp 2 (fun i => (1/2:ℂ)*
        ((D (stdVec i):ℂ)-Complex.I*(D (Complex.I • stdVec i):ℂ)))
      map_add' := by
        intro D E
        ext i
        simp only [WithLp.toLp_add,PiLp.add_apply,ContinuousLinearMap.add_apply,Complex.ofReal_add]
        ring
      map_smul' := by
        intro r D
        ext i
        simp only [PiLp.smul_apply,ContinuousLinearMap.smul_apply,smul_eq_mul,Complex.ofReal_mul,
          RCLike.real_smul_eq_coe_smul (K := ℂ),RingHom.id_apply]
        apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im] <;> ring }
  exact L.toContinuousLinearMap

theorem realWirtingerMap_apply (D : ComplexVector n →L[ℝ] ℝ) :
    realWirtingerMap n D=WithLp.toLp 2 (fun i => (1/2:ℂ)*
      ((D (stdVec i):ℂ)-Complex.I*(D (Complex.I • stdVec i):ℂ))) := rfl

theorem realWirtingerMap_fderiv (f : ComplexVector n → ℝ) (z : ComplexVector n)
    (hf : DifferentiableAt ℝ f z) :
    realWirtingerMap n (fderiv ℝ f z)=WithLp.toLp 2
      (fun i => wirt (fun w => (f w:ℂ)) z (stdVec i)) := by
  have hd : fderiv ℝ (fun w => (f w:ℂ)) z=Complex.ofRealCLM.comp (fderiv ℝ f z) := by
    change fderiv ℝ (Complex.ofRealCLM ∘ f) z=_
    rw [fderiv_comp z Complex.ofRealCLM.differentiableAt hf]
    simp
  rw [realWirtingerMap_apply]
  simp only [wirt,hd,ContinuousLinearMap.comp_apply,Complex.ofRealCLM_apply]

theorem sqrt_gradNormSq_eq_factor_norm (g : HermitianField M) (f : M.Carrier → ℝ)
    (hf : SmoothFn f) (x : M.Carrier) :
    Real.sqrt (gradNormSq g f x)=
      ‖dualNormFactor (gMat g x) (realWirtingerMap n (fderiv ℝ (inChart x f) (chartPt x x)))‖ := by
  have hd : DifferentiableAt ℝ (inChart x f) (chartPt x x) :=
    ((hf x).contDiffAt ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds
    (mem_extChartAt_target x))).differentiableAt (by simp)
  have hg : (gMat g x).PosDef :=
    LeafProofs.L18Aux.hMat_posDef g x (chartPt x x) (mem_extChartAt_target x)
  rw [realWirtingerMap_fderiv (inChart x f) (chartPt x x) hd,dualNormFactor_norm (gMat g x) hg]
  rfl

end Yau.Proofs.F03Aux
