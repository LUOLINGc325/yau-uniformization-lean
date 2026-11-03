import Yau.Proofs.E02PeanoUnique
import Yau.Proofs.E02NormQuadraticJet
import Mathlib.Analysis.Convex.Deriv

open Set Filter Function
open scoped Topology ContDiff InnerProductSpace
noncomputable section
namespace Yau.NodeProofs.E02Aux

variable {E : Type*} [NormedAddCommGroup E]

/-- Convexity follows from the actual second Frechet derivative, by
applying the one-dimensional second-derivative criterion on every line. -/
theorem convexOn_univ_of_second_fderiv_nonneg [NormedSpace ℝ E]
    (f : E → ℝ) (hf : ContDiff ℝ 2 f)
    (hH : ∀ x v, 0 ≤ fderiv ℝ (fderiv ℝ f) x v v) : ConvexOn ℝ univ f := by
  have hLine (x v : E) : ConvexOn ℝ univ (fun t : ℝ => f (x+t • v)) := by
    let p : ℝ → ℝ := fun t => fderiv ℝ f (x+t • v) v
    let A : ℝ → ℝ := fun t => fderiv ℝ (fderiv ℝ f) (x+t • v) v v
    have hD (t : ℝ) : HasDerivAt (fun s : ℝ => x+s • v) v t := by
      simpa using (hasDerivAt_id t).smul_const v |>.const_add x
    have hp (t : ℝ) : HasDerivAt (fun t : ℝ => f (x+t • v)) (p t) t :=
      (hf.differentiable (by norm_num) (x+t • v)).hasFDerivAt.comp_hasDerivAt t (hD t)
    have hA (t : ℝ) : HasDerivAt p (A t) t := by
      have hd := ((hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
        (x+t • v)).hasFDerivAt.comp_hasDerivAt t (hD t)
      simpa only [p,A,Function.comp_def,ContinuousLinearMap.map_zero,add_zero] using
        hd.clm_apply (hasDerivAt_const t v)
    apply convexOn_of_hasDerivWithinAt2_nonneg convex_univ
      ((hf.continuous.comp (by fun_prop : Continuous (fun t : ℝ => x+t • v))).continuousOn)
      (fun t _ => (hp t).hasDerivWithinAt) (fun t _ => (hA t).hasDerivWithinAt)
    exact fun t _ => hH (x+t • v) v
  refine ⟨convex_univ,?_⟩
  intro x _ y _ a b ha hb hab
  have h := (hLine x (y-x)).2 (mem_univ 0) (mem_univ 1) ha hb hab
  have hArg : x+b • (y-x) = a • x+b • y := by
    calc
      x+b • (y-x) = (a+b) • x+b • (y-x) := by rw [hab,one_smul]
      _ = a • x+b • y := by module
  simpa only [smul_eq_mul,mul_zero,mul_one,zero_add,zero_smul,one_smul,add_zero,
    add_sub_cancel,hArg] using h

section InnerProduct
variable [InnerProductSpace ℝ E]

/-- A bound on the true Hessian supplies the global quadratic correction
used to apply Jensen. The touching comparison itself is not changed. -/
theorem convexOn_add_quadratic_of_second_fderiv_bound (f : E → ℝ)
    (hf : ContDiff ℝ 2 f) (C : ℝ)
    (hC : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ C) :
    ConvexOn ℝ univ (fun x => f x+C*(‖x‖^2/2)) := by
  have hQ : ContDiff ℝ 2 (fun x : E => C*(‖x‖^2/2)) :=
    contDiff_const.mul ((contDiff_norm_sq ℝ).div_const 2)
  apply convexOn_univ_of_second_fderiv_nonneg _ (hf.add hQ)
  intro x v
  have hJQ : RealSecondJet (fun y : E => C*(‖y‖^2/2)) x
      (C • innerSL ℝ x) (C • innerSL ℝ (E := E)) := by
    simpa using (realSecondJet_const_mul (realSecondJet_norm_sq_div_two (E := E) 1 x) C)
  have hSecond := realSecondJet_second_fderiv_eq
    (realSecondJet_add (realSecondJet_of_contDiffAt_two hf.contDiffAt) hJQ)
    (hf.add hQ).contDiffAt
  rw [hSecond]
  change 0 ≤ fderiv ℝ (fderiv ℝ f) x v v+C*⟪v,v⟫_ℝ
  rw [real_inner_self_eq_norm_sq]
  have hNorm : |fderiv ℝ (fderiv ℝ f) x v v| ≤ C*‖v‖^2 := by
    calc
      |fderiv ℝ (fderiv ℝ f) x v v| ≤
          ‖fderiv ℝ (fderiv ℝ f) x‖*‖v‖*‖v‖ :=
        (fderiv ℝ (fderiv ℝ f) x).le_opNorm₂ v v
      _ ≤ C*‖v‖*‖v‖ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hC x) (norm_nonneg v)) (norm_nonneg v)
      _ = C*‖v‖^2 := by ring
  linarith [neg_abs_le (fderiv ℝ (fderiv ℝ f) x v v)]

end InnerProduct
end Yau.NodeProofs.E02Aux
