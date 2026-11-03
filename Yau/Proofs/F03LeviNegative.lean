import Yau.Geometry.Calculus

/-! Negation commutes with the actual Wirtinger and Levi calculators, including nonsmooth inputs. -/
noncomputable section
namespace Yau.Proofs.F03Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

theorem wirt_negative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : E → ℂ) (z v : E) : wirt (fun x => -f x) z v= -wirt f z v := by
  simp only [wirt,fderiv_fun_neg,ContinuousLinearMap.neg_apply]
  ring

theorem wirtBar_negative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : E → ℂ) (z v : E) : wirtBar (fun x => -f x) z v= -wirtBar f z v := by
  simp only [wirtBar,fderiv_fun_neg,ContinuousLinearMap.neg_apply]
  ring

theorem levi_negative (f : M.Carrier → ℝ) (x : M.Carrier) :
    levi (fun y => -f y) x= -levi f x := by
  ext a b
  simp only [levi,leviC,leviMatrix,inChart,Complex.ofReal_neg,Matrix.neg_apply]
  simp_rw [wirtBar_negative]
  exact wirt_negative _ _ _

end Yau.Proofs.F03Aux
