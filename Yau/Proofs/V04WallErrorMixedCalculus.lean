import Yau.Proofs.V04WallErrorPullback

/-! Product and locality rules for complex-valued mixed derivatives of
the actual fiber quadratic expression. -/

open Filter
open scoped Topology ContDiff Matrix
noncomputable section
namespace Yau.Blueprint.V04Proof.WallErrorAux
open Yau Yau.Blueprint V03Proof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem mixedWirt_congr_of_eventuallyEq {f g : E → ℂ} {z : E}
    (heq : f =ᶠ[𝓝 z] g) (v w : E) :
    wirt (fun y => wirtBar f y v) z w = wirt (fun y => wirtBar g y v) z w := by
  have hbar : (fun y => wirtBar f y v) =ᶠ[𝓝 z] (fun y => wirtBar g y v) := by
    filter_upwards [heq.fderiv (𝕜 := ℝ)] with y hy
    simp only [wirtBar, hy]
  simp only [wirt, hbar.fderiv_eq (𝕜 := ℝ)]

theorem mixedWirt_mul {f g : E → ℂ} {z : E}
    (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z) (v w : E) :
    wirt (fun y => wirtBar (fun x => f x * g x) y v) z w =
      wirt (fun y => wirtBar f y v) z w * g z + wirtBar f z v * wirt g z w +
        wirt f z w * wirtBar g z v + f z * wirt (fun y => wirtBar g y v) z w := by
  have hfD := hf.differentiableAt (by norm_num : (2 : ℕ∞ω) ≠ 0)
  have hgD := hg.differentiableAt (by norm_num : (2 : ℕ∞ω) ≠ 0)
  have hfB := wirtBar_differentiableAt hf v
  have hgB := wirtBar_differentiableAt hg v
  have heq : (fun y => wirtBar (fun x => f x * g x) y v) =ᶠ[𝓝 z]
      (fun y => wirtBar f y v * g y + f y * wirtBar g y v) := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with y hfy hgy
    exact wirtBar_mul (hfy.differentiableAt (by norm_num)) (hgy.differentiableAt (by norm_num)) v
  have he : wirt (fun y => wirtBar (fun x => f x * g x) y v) z w =
      wirt (fun y => wirtBar f y v * g y + f y * wirtBar g y v) z w := by
    simp only [wirt, heq.fderiv_eq (𝕜 := ℝ)]
  rw [he, wirt_add (fun y => wirtBar f y v * g y) (fun y => f y * wirtBar g y v)
      z w (hfB.fun_mul hgD) (hfD.fun_mul hgB), wirt_mul hfB hgD w, wirt_mul hfD hgB w]
  ring

theorem mixedWirt_sum {κ : Type*} (s : Finset κ) (f : κ → E → ℂ) {z : E}
    (hf : ∀ i ∈ s, ContDiffAt ℝ 2 (f i) z) (v w : E) :
    wirt (fun y => wirtBar (fun x => ∑ i ∈ s, f i x) y v) z w =
      ∑ i ∈ s, wirt (fun y => wirtBar (f i) y v) z w := by
  have hnear : ∀ᶠ y in 𝓝 z, ∀ i ∈ s, ContDiffAt ℝ 2 (f i) y :=
    (s.eventually_all).2 fun i hi => (hf i hi).eventually (by norm_num)
  have heq : (fun y => wirtBar (fun x => ∑ i ∈ s, f i x) y v) =ᶠ[𝓝 z]
      (fun y => ∑ i ∈ s, wirtBar (f i) y v) := by
    filter_upwards [hnear] with y hy
    exact wirtBar_sum s f y v (fun i hi => (hy i hi).differentiableAt (by norm_num))
  have he : wirt (fun y => wirtBar (fun x => ∑ i ∈ s, f i x) y v) z w =
      wirt (fun y => ∑ i ∈ s, wirtBar (f i) y v) z w := by
    simp only [wirt, heq.fderiv_eq (𝕜 := ℝ)]
  rw [he, wirt_sum s (fun i y => wirtBar (f i) y v) z w
    (fun i hi => wirtBar_differentiableAt (hf i hi) v)]

theorem wirt_complexLinear (L : E →L[ℂ] ℂ) (z v : E) : wirt L z v = L v := by
  rw [wirt_holomorphic L.differentiableAt]
  exact congrArg (fun D : E →L[ℂ] ℂ => D v) L.hasFDerivAt.fderiv

theorem wirtBar_complexLinear (L : E →L[ℂ] ℂ) (z v : E) : wirtBar L z v = 0 :=
  wirtBar_holomorphic L.differentiableAt v

theorem wirt_star_complexLinear (L : E →L[ℂ] ℂ) (z v : E) :
    wirt (fun y => star (L y)) z v = 0 := by
  rw [wirt_conj, wirtBar_complexLinear, star_zero]

theorem wirtBar_star_complexLinear (L : E →L[ℂ] ℂ) (z v : E) :
    wirtBar (fun y => star (L y)) z v = star (L v) := by
  rw [wirtBar_conj, wirt_complexLinear]

theorem mixedWirt_complexLinear (L : E →L[ℂ] ℂ) (z v w : E) :
    wirt (fun y => wirtBar L y v) z w = 0 := by
  have he : (fun y => wirtBar L y v) = fun _ => (0 : ℂ) :=
    funext fun y => wirtBar_complexLinear L y v
  rw [he]
  simp [wirt]

theorem mixedWirt_star_complexLinear (L : E →L[ℂ] ℂ) (z v w : E) :
    wirt (fun y => wirtBar (fun x => star (L x)) y v) z w = 0 := by
  have he : (fun y => wirtBar (fun x => star (L x)) y v) = fun _ => star (L v) :=
    funext fun y => wirtBar_star_complexLinear L y v
  rw [he]
  have hconst := (hasFDerivAt_const (𝕜 := ℝ) (star (L v)) z).fderiv
  simp only [wirt, hconst, zero_apply, mul_zero, sub_zero]

end Yau.Blueprint.V04Proof.WallErrorAux
