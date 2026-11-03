import Yau.Proofs.V03LeviMatrix
import Yau.Proofs.V03Coordinates

/-! Native complex linearity and conjugate linearity in the actual
Wirtinger directions, and the full finite-coordinate Levi contraction. -/

open scoped Topology ContDiff Matrix

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem realLinear_complex_smul (A : E →L[ℝ] ℂ) (c : ℂ) (v : E) :
    A (c • v) = (c.re : ℂ) * A v + (c.im : ℂ) * A (Complex.I • v) := by
  have he : c • v = c.re • v + c.im • (Complex.I • v) := by
    calc
      c • v = ((c.re : ℂ) + (c.im : ℂ) * Complex.I) • v :=
        congrArg (fun t : ℂ => t • v) (Complex.re_add_im c).symm
      _ = _ := by
        rw [add_smul, mul_smul]
        exact congrArg₂ (· + ·) (algebraMap_smul ℂ c.re v)
          (algebraMap_smul ℂ c.im (Complex.I • v))
  rw [he, map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]

theorem wirt_add_direction (f : E → ℂ) (z v w : E) :
    wirt f z (v + w) = wirt f z v + wirt f z w := by
  simp only [wirt, map_add, smul_add]
  ring

theorem wirtBar_add_direction (f : E → ℂ) (z v w : E) :
    wirtBar f z (v + w) = wirtBar f z v + wirtBar f z w := by
  simp only [wirtBar, map_add, smul_add]
  ring

theorem wirt_smul_direction (f : E → ℂ) (z v : E) (c : ℂ) :
    wirt f z (c • v) = c * wirt f z v := by
  have he : Complex.I • (c • v) = (Complex.I * c) • v := (mul_smul _ _ _).symm
  unfold wirt
  rw [realLinear_complex_smul (fderiv ℝ f z) c v, he,
    realLinear_complex_smul (fderiv ℝ f z) (Complex.I * c) v]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

theorem wirtBar_smul_direction (f : E → ℂ) (z v : E) (c : ℂ) :
    wirtBar f z (c • v) = star c * wirtBar f z v := by
  have he : Complex.I • (c • v) = (Complex.I * c) • v := (mul_smul _ _ _).symm
  unfold wirtBar
  rw [realLinear_complex_smul (fderiv ℝ f z) c v, he,
    realLinear_complex_smul (fderiv ℝ f z) (Complex.I * c) v]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, Complex.star_def] <;> ring

theorem wirt_sum_direction {ι : Type*} (f : E → ℂ) (z : E)
    (s : Finset ι) (v : ι → E) :
    wirt f z (∑ i ∈ s, v i) = ∑ i ∈ s, wirt f z (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [wirt]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, wirt_add_direction, ih]

theorem wirtBar_sum_direction {ι : Type*} (f : E → ℂ) (z : E)
    (s : Finset ι) (v : ι → E) :
    wirtBar f z (∑ i ∈ s, v i) = ∑ i ∈ s, wirtBar f z (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [wirtBar]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, wirtBar_add_direction, ih]

theorem wirt_const_mul {f : E → ℂ} {z : E} (hf : DifferentiableAt ℝ f z)
    (c : ℂ) (v : E) :
    wirt (fun y => c * f y) z v = c * wirt f z v := by
  simp only [wirt, fderiv_const_mul hf, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem mixedWirt_smul_left {f : E → ℂ} {z : E} (hf : ContDiffAt ℝ 2 f z)
    (c : ℂ) (v w : E) :
    wirt (fun y => wirtBar f y (c • v)) z w =
      star c * wirt (fun y => wirtBar f y v) z w := by
  simp_rw [wirtBar_smul_direction]
  exact wirt_const_mul (wirtBar_differentiableAt hf v) (star c) w

theorem mixedWirt_sum_left {ι : Type*} {f : E → ℂ} {z : E} (hf : ContDiffAt ℝ 2 f z)
    (s : Finset ι) (v : ι → E) (w : E) :
    wirt (fun y => wirtBar f y (∑ i ∈ s, v i)) z w =
      ∑ i ∈ s, wirt (fun y => wirtBar f y (v i)) z w := by
  simp_rw [wirtBar_sum_direction]
  exact wirt_sum s _ z w (fun i _ => wirtBar_differentiableAt hf (v i))

theorem mixedWirt_coordinates {ι : Type*} [Fintype ι]
    {f : E → ℂ} {z : E} (hf : ContDiffAt ℝ 2 f z)
    (dir : ι → E) (u v : ι → ℂ) :
    wirt (fun y => wirtBar f y (∑ i, u i • dir i)) z (∑ j, v j • dir j) =
      ∑ i, ∑ j, star (u i) * wirt (fun y => wirtBar f y (dir i)) z (dir j) * v j := by
  rw [mixedWirt_sum_left hf]
  apply Finset.sum_congr rfl
  intro i _
  rw [mixedWirt_smul_left hf, wirt_sum_direction, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [wirt_smul_direction]
  ring

theorem cotangent_levi_contraction {n : ℕ} {f : CotangentCoord n → ℝ}
    {z : CotangentCoord n} (hf : ContDiffAt ℝ 2 f z)
    (u v : CotangentIndex n → ℂ) :
    wirt (fun y => wirtBar (fun x => (f x : ℂ)) y (cotangentVectorOfCoords u)) z
      (cotangentVectorOfCoords v) = star u ⬝ᵥ (leviMatrix f z cotangentDir *ᵥ v) := by
  have hF : ContDiffAt ℝ 2 (fun x => (f x : ℂ)) z :=
    hf.continuousLinearMap_comp Complex.ofRealCLM
  rw [cotangentVectorOfCoords_eq_sum, cotangentVectorOfCoords_eq_sum,
    mixedWirt_coordinates hF]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, leviMatrix]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end Yau.Blueprint.V03Proof
