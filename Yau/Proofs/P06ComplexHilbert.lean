import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

/-! Genuine complexification of a real Hilbert space. The norm and topology
are the existing product L² norm and topology, and scalar multiplication is
the usual real-imaginary matrix action. -/

noncomputable section
open scoped Topology InnerProductSpace

namespace Yau.NodeProofs.P06Aux

def ComplexHilbert (H : Type*) := WithLp 2 (H × H)

namespace ComplexHilbert
variable {H : Type*}

instance [NormedAddCommGroup H] : NormedAddCommGroup (ComplexHilbert H) :=
  inferInstanceAs (NormedAddCommGroup (WithLp 2 (H × H)))

instance [NormedAddCommGroup H] [CompleteSpace H] : CompleteSpace (ComplexHilbert H) :=
  inferInstanceAs (CompleteSpace (WithLp 2 (H × H)))

def re (x : ComplexHilbert H) : H := (WithLp.ofLp x).1
def im (x : ComplexHilbert H) : H := (WithLp.ofLp x).2
def mk (x y : H) : ComplexHilbert H := WithLp.toLp 2 (x, y)

@[simp] theorem re_mk (x y : H) : re (mk x y) = x := rfl
@[simp] theorem im_mk (x y : H) : im (mk x y) = y := rfl

@[ext] theorem ext {x y : ComplexHilbert H} (hr : re x = re y) (hi : im x = im y) : x = y := by
  apply WithLp.ofLp_injective 2
  exact Prod.ext hr hi

section Module
variable [NormedAddCommGroup H] [NormedSpace ℝ H]

@[simp] theorem re_zero : re (0 : ComplexHilbert H) = 0 := rfl
@[simp] theorem im_zero : im (0 : ComplexHilbert H) = 0 := rfl
@[simp] theorem re_add (x y : ComplexHilbert H) : re (x + y) = re x + re y := rfl
@[simp] theorem im_add (x y : ComplexHilbert H) : im (x + y) = im x + im y := rfl
@[simp] theorem re_neg (x : ComplexHilbert H) : re (-x) = -re x := rfl
@[simp] theorem im_neg (x : ComplexHilbert H) : im (-x) = -im x := rfl
@[simp] theorem re_sub (x y : ComplexHilbert H) : re (x - y) = re x - re y := rfl
@[simp] theorem im_sub (x y : ComplexHilbert H) : im (x - y) = im x - im y := rfl

instance : SMul ℂ (ComplexHilbert H) where
  smul c x := mk (c.re • re x - c.im • im x) (c.im • re x + c.re • im x)

@[simp] theorem re_smul (c : ℂ) (x : ComplexHilbert H) :
    re (c • x) = c.re • re x - c.im • im x := rfl
@[simp] theorem im_smul (c : ℂ) (x : ComplexHilbert H) :
    im (c • x) = c.im • re x + c.re • im x := rfl

instance : Module ℂ (ComplexHilbert H) where
  smul_add c x y := by apply ext <;> simp only [re_smul, im_smul, re_add, im_add] <;> module
  add_smul c d x := by
    apply ext <;> simp only [re_smul, im_smul, re_add, im_add, Complex.add_re, Complex.add_im] <;> module
  mul_smul c d x := by
    apply ext <;> simp only [re_smul, im_smul, Complex.mul_re, Complex.mul_im] <;> module
  one_smul x := by apply ext <;> simp
  zero_smul x := by apply ext <;> simp
  smul_zero c := by apply ext <;> simp

instance : Module ℝ (ComplexHilbert H) := Module.restrictScalars ℝ ℂ (ComplexHilbert H)

@[simp] theorem re_real_smul (r : ℝ) (x : ComplexHilbert H) : re (r • x) = r • re x := by
  change re ((r : ℂ) • x) = r • re x
  rw [re_smul]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_smul, sub_zero]

@[simp] theorem im_real_smul (r : ℝ) (x : ComplexHilbert H) : im (r • x) = r • im x := by
  change im ((r : ℂ) • x) = r • im x
  rw [im_smul]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_smul, zero_add]

instance : IsScalarTower ℝ ℂ (ComplexHilbert H) where
  smul_assoc r c x := by
    apply ext <;> simp only [re_real_smul, im_real_smul, re_smul, im_smul,
      Complex.real_smul, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, zero_add] <;> module

instance : SMulCommClass ℝ ℂ (ComplexHilbert H) where
  smul_comm r c x := by
    apply ext <;> simp only [re_real_smul, im_real_smul, re_smul, im_smul] <;> module

theorem norm_sq (x : ComplexHilbert H) : ‖x‖ ^ 2 = ‖re x‖ ^ 2 + ‖im x‖ ^ 2 :=
  WithLp.prod_norm_sq_eq_of_L2 x

end Module

section Inner
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem norm_smul_sq (c : ℂ) (x : ComplexHilbert H) : ‖c • x‖ ^ 2 = ‖c‖ ^ 2 * ‖x‖ ^ 2 := by
  rw [norm_sq, re_smul, im_smul, norm_sub_sq_real, norm_add_sq_real,
    norm_smul, norm_smul, norm_smul, norm_smul, inner_smul_left, inner_smul_right,
    inner_smul_left, inner_smul_right]
  simp only [conj_trivial, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [Complex.sq_norm, Complex.normSq_apply, norm_sq]
  ring

instance : NormedSpace ℂ (ComplexHilbert H) where
  norm_smul_le c x := by
    have hsq := norm_smul_sq c x
    have heq : ‖c • x‖ = ‖c‖ * ‖x‖ :=
      (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
        (by simpa only [mul_pow] using hsq)
    exact heq.le

instance : NormedSpace ℝ (ComplexHilbert H) := NormedSpace.restrictScalars ℝ ℂ (ComplexHilbert H)

def innerC (x y : ComplexHilbert H) : ℂ :=
  (inner ℝ (re x) (re y) + inner ℝ (im x) (im y) : ℝ) +
    Complex.I * (inner ℝ (re x) (im y) - inner ℝ (im x) (re y) : ℝ)

@[simp] theorem innerC_re (x y : ComplexHilbert H) :
    (innerC x y).re = inner ℝ (re x) (re y) + inner ℝ (im x) (im y) := by
  simp [innerC]

@[simp] theorem innerC_im (x y : ComplexHilbert H) :
    (innerC x y).im = inner ℝ (re x) (im y) - inner ℝ (im x) (re y) := by
  simp [innerC]

instance : InnerProductSpace ℂ (ComplexHilbert H) where
  inner := innerC
  norm_sq_eq_re_inner x := by
    change ‖x‖ ^ 2 = (innerC x x).re
    rw [innerC_re, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, norm_sq]
  conj_inner_symm x y := by
    apply Complex.ext <;> simp only [Complex.conj_re, Complex.conj_im, innerC_re, innerC_im,
      real_inner_comm] <;> ring
  add_left x y z := by
    apply Complex.ext <;> simp only [Complex.add_re, Complex.add_im, innerC_re, innerC_im,
      re_add, im_add, inner_add_left] <;> ring
  smul_left x y c := by
    apply Complex.ext <;> simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re,
      Complex.conj_im, innerC_re, innerC_im, re_smul, im_smul, inner_add_left, inner_sub_left,
      inner_smul_left, conj_trivial] <;> ring

theorem inner_apply (x y : ComplexHilbert H) : inner ℂ x y = innerC x y := rfl

end Inner
end ComplexHilbert
end Yau.NodeProofs.P06Aux
