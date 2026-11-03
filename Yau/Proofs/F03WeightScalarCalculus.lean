import Yau.Proofs.F03LeviScalarCalculus
import Yau.Proofs.F03WeightBasic
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Pointwise real scalar calculus for the actual polynomial-exponential weight. -/
noncomputable section
open scoped ContDiff ComplexOrder Topology
namespace Yau.Proofs.F03Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

theorem levi_real_scalar_comp_at {f : M.Carrier → ℝ} (hf : SmoothFn f)
    (F : ℝ → ℝ) (x : M.Carrier) (hF : ContDiffAt ℝ 2 F (f x)) :
    levi (fun y => F (f y)) x=Complex.ofReal (deriv F (f x)) • levi f x+
      Complex.ofReal (deriv (deriv F) (f x)) •
        Matrix.vecMulVec (star (scalarFirstCovector f x)) (scalarFirstCovector f x) := by
  have hinv : chartInv x (chartPt x x)=x := (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  have hOuter : ContDiffAt ℝ 2 F (inChart x f (chartPt x x)) := by simpa only [inChart,hinv] using hF
  change leviC (F ∘ inChart x f) (chartPt x x)=_
  simpa only [levi,scalarFirstCovector,inChart,hinv,Function.comp_def] using
    leviC_real_scalar_comp (smoothFn_center_contDiffAt_two hf x) hOuter

theorem sqrt_gradNormSq_scalar_comp_at (g : HermitianField M)
    {f : M.Carrier → ℝ} (hf : SmoothFn f) (F : ℝ → ℝ)
    (hComp : SmoothFn (fun y => F (f y))) (x : M.Carrier)
    (hF : DifferentiableAt ℝ F (f x)) :
    Real.sqrt (gradNormSq g (fun y => F (f y)) x)=
      |deriv F (f x)| * Real.sqrt (gradNormSq g f x) := by
  rw [sqrt_gradNormSq_eq_physicalCovector g hComp,sqrt_gradNormSq_eq_physicalCovector g hf,
    physicalCovector_scalar_comp g hf F x hF,norm_smul,Real.norm_eq_abs]

theorem smoothFn_log_of_pos (u : M.Carrier → ℝ) (hu : SmoothFn u) (hu0 : ∀ x,0 < u x) :
    SmoothFn (fun x => Real.log (u x)) :=
  fun a => (hu a).log (fun z _ => (hu0 _).ne')

theorem smoothFn_inverseSquare_of_pos (u : M.Carrier → ℝ) (hu : SmoothFn u) (hu0 : ∀ x,0 < u x) :
    SmoothFn (fun x => (u x)^(-2:ℤ)) := by
  intro a
  simp only [inChart,zpow_neg,zpow_natCast]
  exact ((hu a).pow 2).inv (fun z _ => pow_ne_zero _ (hu0 _).ne')

theorem inverseSquare_deriv (r : ℝ) : deriv (fun z : ℝ => z^(-2:ℤ)) r= -2/r^3 := by
  rw [deriv_zpow]
  norm_num [zpow_neg,zpow_natCast,div_eq_mul_inv]

theorem inverseSquare_secondDeriv (r : ℝ) :
    deriv (deriv (fun z : ℝ => z^(-2:ℤ))) r=6/r^4 := by
  rw [deriv_zpow',deriv_const_mul_field,deriv_zpow]
  norm_num [zpow_neg,zpow_natCast,div_eq_mul_inv] <;> ring

theorem levi_log_of_pos (u : M.Carrier → ℝ) (hu : SmoothFn u) (x : M.Carrier) (hu0 : 0 < u x) :
    levi (fun y => Real.log (u y)) x=Complex.ofReal (1/u x) • levi u x-
      Complex.ofReal (1/(u x)^2) •
        Matrix.vecMulVec (star (scalarFirstCovector u x)) (scalarFirstCovector u x) := by
  rw [levi_real_scalar_comp_at hu Real.log x (Real.contDiffAt_log.mpr hu0.ne'),
    Real.deriv_log,Real.deriv_log',deriv_inv]
  simp only [one_div,Complex.ofReal_neg,neg_smul,sub_eq_add_neg]

theorem levi_inverseSquare_of_pos (u : M.Carrier → ℝ) (hu : SmoothFn u) (x : M.Carrier) (hu0 : 0 < u x) :
    levi (fun y => (u y)^(-2:ℤ)) x=Complex.ofReal (-2/(u x)^3) • levi u x+
      Complex.ofReal (6/(u x)^4) •
        Matrix.vecMulVec (star (scalarFirstCovector u x)) (scalarFirstCovector u x) := by
  have hF : ContDiffAt ℝ 2 (fun r : ℝ => r^(-2:ℤ)) (u x) := by
    simp only [zpow_neg,zpow_natCast]
    exact (contDiffAt_id.pow 2).inv (pow_ne_zero _ hu0.ne')
  rw [levi_real_scalar_comp_at hu _ x hF,inverseSquare_deriv,inverseSquare_secondDeriv]

def comparisonLogWeight (u f : M.Carrier → ℝ) (A : ℝ) (k : ℕ) (x : M.Carrier) : ℝ :=
  -(k:ℝ)*Real.log (u x)-A*(f x*(u x)^(-2:ℤ))

theorem comparisonWeight_eq_exp_logWeight (u : M.Carrier → ℝ) (H : M.Carrier → ℝ → ℝ)
    (A : ℝ) (k : ℕ) (x : M.Carrier) (t : ℝ) (hu0 : 0 < u x) :
    comparisonWeight u H A k x t=Real.exp (comparisonLogWeight u (fun y => H y t) A k x) := by
  have hPow : (u x)^(-(k:ℤ))=Real.exp (-(k:ℝ)*Real.log (u x)) := by
    rw [← Real.rpow_intCast,Real.rpow_def_of_pos hu0]
    push_cast
    congr 1
    ring
  rw [comparisonWeight,hPow,← Real.exp_add]
  congr 1
  have hInverse : (u x)^(-2:ℤ)=((u x)^2)⁻¹ := zpow_negSucc (u x) 1
  simp only [comparisonLogWeight,hInverse,div_eq_mul_inv]
  ring

theorem comparisonLogWeight_smooth (u f : M.Carrier → ℝ) (hu : SmoothFn u)
    (hu0 : ∀ x,0 < u x) (hf : SmoothFn f) (A : ℝ) (k : ℕ) :
    SmoothFn (comparisonLogWeight u f A k) := by
  intro a
  exact (contDiffOn_const.mul (smoothFn_log_of_pos u hu hu0 a)).sub
    (contDiffOn_const.mul ((hf a).mul (smoothFn_inverseSquare_of_pos u hu hu0 a)))

end Yau.Proofs.F03Aux
