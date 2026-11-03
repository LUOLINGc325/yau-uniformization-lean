import Yau.LeafProofs.L05AutonomousSecondFTC
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Calculus

noncomputable section
open Filter Set MeasureTheory
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic

/-- The real-line second derivative criterion gives convexity on the genuine spatial convex set. -/
theorem auto_convexOn_of_spatial_second_nonneg {n : ℕ} {O : Set (Space n)} (hO : Convex ℝ O)
    {f : Space n → ℝ} (hf : ContDiff ℝ ∞ f)
    (hSecond : ∀ x∈O, ∀ v : Space n, 0 ≤ fderiv ℝ (fderiv ℝ f) x v v) : ConvexOn ℝ O f := by
  refine ⟨hO,?_⟩
  intro x hx y hy a b ha hb hab
  let g : ℝ → ℝ := fun s => f (x+s • (y-x))
  have hg : ContDiff ℝ ∞ g := hf.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  have hgp : ContDiff ℝ ∞ (deriv g) := (contDiff_infty_iff_deriv.mp hg).2
  have hIn (s : ℝ) (hs : s∈Icc (0 : ℝ) 1) : x+s • (y-x)∈O := by
    have hh := hO hx hy (sub_nonneg.mpr hs.2) hs.1 (sub_add_cancel 1 s)
    convert hh using 1 <;> module
  have hgc : ConvexOn ℝ (Icc (0 : ℝ) 1) g := convexOn_of_deriv2_nonneg' (convex_Icc _ _)
    (hg.differentiable (by simp)).differentiableOn (hgp.differentiable (by simp)).differentiableOn (by
      intro s hs
      change 0 ≤ deriv (deriv g) s
      rw [auto_line_second_derivative hf x (y-x) s]
      exact hSecond _ (hIn s hs) _)
  have h := hgc.2 (by norm_num : (0 : ℝ)∈Icc 0 1) (by norm_num : (1 : ℝ)∈Icc 0 1) ha hb hab
  have hPoint : x+b • (y-x)=a • x+b • y := by
    rw [show a=1-b by linarith only [hab]]
    module
  simp only [smul_eq_mul,mul_zero,mul_one,zero_add,g,zero_smul,one_smul,add_zero] at h
  have hY : x+(y-x)=y := by abel
  simpa only [hPoint,hY,smul_eq_mul] using h

/-- Pointwise convergence on the actual convex set preserves its literal convex inequalities. -/
theorem auto_convexOn_of_pointwise_limit {n : ℕ} {O : Set (Space n)}
    {f : ℕ → Space n → ℝ} {u : Space n → ℝ} (hf : ∀ j, ConvexOn ℝ O (f j))
    (hlim : ∀ x∈O, Tendsto (fun j => f j x) atTop (𝓝 (u x))) : ConvexOn ℝ O u := by
  have hO : Convex ℝ O := (hf 0).1
  refine ⟨hO,?_⟩
  intro x hx y hy a b ha hb hab
  exact le_of_tendsto_of_tendsto (hlim _ (hO hx hy ha hb hab))
    (((hlim x hx).const_mul a).add ((hlim y hy).const_mul b))
    (Eventually.of_forall fun j => (hf j).2 hx hy ha hb hab)

/-- This is the actual scalar quadratic's second Frechet derivative. -/
theorem auto_spatial_quadratic_second {n : ℕ} (C : ℝ) (x v : Space n) :
    fderiv ℝ (fderiv ℝ (fun y : Space n => (C/2)*‖y‖^2)) x v v=C*‖v‖^2 := by
  have hFirst : fderiv ℝ (fun y : Space n => (C/2)*‖y‖^2)=fun y => C • innerSL ℝ y := by
    funext y
    rw [fderiv_const_mul ((contDiff_norm_sq ℝ : ContDiff ℝ ∞ (fun z : Space n => ‖z‖^2)).differentiable (by simp) y),
      fderiv_norm_sq_apply,two_smul]
    ext z
    change (C/2)*(inner ℝ y z+inner ℝ y z)=C*inner ℝ y z
    ring
  rw [hFirst]
  have hd : HasFDerivAt (fun y : Space n => C • innerSL ℝ y) (C • innerSL ℝ) x :=
    (innerSL ℝ).hasFDerivAt.const_smul C
  rw [hd.fderiv]
  change C*(inner ℝ v v)=C*‖v‖^2
  rw [real_inner_self_eq_norm_sq]

end Yau.LeafProofs.L05AutonomousAux
