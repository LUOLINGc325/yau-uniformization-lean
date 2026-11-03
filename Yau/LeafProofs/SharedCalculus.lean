import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/-! Shared entrywise matrix and bilinear-field calculus for citation-leaf proofs. -/

noncomputable section

open scoped ContDiff

namespace Yau.LeafProofs.SharedCalculus

theorem contDiffOn_matrix_det {E ι 𝔸 : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype ι] [DecidableEq ι] [NormedCommRing 𝔸] [NormedAlgebra ℝ 𝔸]
    {A : E → Matrix ι ι 𝔸} {s : Set E}
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun z => A z i j) s) :
    ContDiffOn ℝ ∞ (fun z => (A z).det) s := by
  simp_rw [Matrix.det_apply']
  exact ContDiffOn.sum fun σ _ => contDiffOn_const.mul
    (contDiffOn_prod fun i _ => hA (σ i) i)

theorem contDiffOn_matrix_inv {E ι 𝕜 : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype ι] [DecidableEq ι] [RCLike 𝕜]
    {A : E → Matrix ι ι 𝕜} {s : Set E}
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun z => A z i j) s)
    (hdet : ∀ z ∈ s, (A z).det ≠ 0) (i j : ι) :
    ContDiffOn ℝ ∞ (fun z => (A z)⁻¹ i j) s := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply,
    smul_eq_mul, Matrix.adjugate_apply]
  apply ((contDiffOn_matrix_det hA).inv hdet).mul
  apply contDiffOn_matrix_det
  intro k l
  simp only [Matrix.updateRow_apply]
  by_cases hkj : k = j
  · simp only [hkj, ↓reduceIte]
    exact contDiffOn_const
  · simp only [hkj, ↓reduceIte]
    exact hA k l

theorem fderiv_pullback_bilin {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {B : F → F →L[ℝ] F →L[ℝ] ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hB : DifferentiableAt ℝ B (f x)) (u v w : E) :
    fderiv ℝ (fun y => B (f y) (fderiv ℝ f y u) (fderiv ℝ f y v)) x w =
      fderiv ℝ B (f x) (fderiv ℝ f x w) (fderiv ℝ f x u) (fderiv ℝ f x v) +
        B (f x) (fderiv ℝ (fderiv ℝ f) x w u) (fderiv ℝ f x v) +
          B (f x) (fderiv ℝ f x u) (fderiv ℝ (fderiv ℝ f) x w v) := by
  have hfd : DifferentiableAt ℝ f x := hf.differentiableAt (by norm_num)
  have hfdd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hcomp : DifferentiableAt ℝ (fun y => B (f y)) x := DifferentiableAt.comp (g := B) (f := f) x hB hfd
  have hdc : fderiv ℝ (fun y => B (f y)) x =
      (fderiv ℝ B (f x)).comp (fderiv ℝ f x) :=
    fderiv_comp (g := B) x hB hfd
  have happ (a : E) : DifferentiableAt ℝ (fun y => fderiv ℝ f y a) x :=
    hfdd.clm_apply (differentiableAt_const a)
  rw [fderiv_clm_apply (hcomp.clm_apply (happ u)) (happ v)]
  rw [fderiv_clm_apply hcomp (happ u)]
  rw [fderiv_clm_apply hfdd (differentiableAt_const u),
    fderiv_clm_apply hfdd (differentiableAt_const v), hdc]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, fderiv_const_apply, ContinuousLinearMap.zero_apply,
    map_zero, add_zero, zero_add]
  ring

theorem cyclic_derivative_pullback_bilin {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {B : F → F →L[ℝ] F →L[ℝ] ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hB : DifferentiableAt ℝ B (f x))
    (hskew : ∀ p q, B (f x) p q = -B (f x) q p) (u v w : E) :
    fderiv ℝ (fun y => B (f y) (fderiv ℝ f y v) (fderiv ℝ f y w)) x u +
      fderiv ℝ (fun y => B (f y) (fderiv ℝ f y w) (fderiv ℝ f y u)) x v +
      fderiv ℝ (fun y => B (f y) (fderiv ℝ f y u) (fderiv ℝ f y v)) x w =
    fderiv ℝ B (f x) (fderiv ℝ f x u) (fderiv ℝ f x v) (fderiv ℝ f x w) +
      fderiv ℝ B (f x) (fderiv ℝ f x v) (fderiv ℝ f x w) (fderiv ℝ f x u) +
      fderiv ℝ B (f x) (fderiv ℝ f x w) (fderiv ℝ f x u) (fderiv ℝ f x v) := by
  have hs := hf.isSymmSndFDerivAt (by norm_num)
  have hcancel (a b c : E) :
      B (f x) (fderiv ℝ (fderiv ℝ f) x a b) (fderiv ℝ f x c) +
        B (f x) (fderiv ℝ f x c) (fderiv ℝ (fderiv ℝ f) x b a) = 0 := by
    rw [hs b a, hskew (fderiv ℝ f x c)]
    ring
  rw [fderiv_pullback_bilin hf hB v w u, fderiv_pullback_bilin hf hB w u v,
    fderiv_pullback_bilin hf hB u v w]
  linarith [hcancel u v w, hcancel v w u, hcancel w u v]

theorem fderiv_bilin_apply_const {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {B : E → F →L[ℝ] F →L[ℝ] ℝ} {x : E}
    (hB : DifferentiableAt ℝ B x) (u : E) (v w : F) :
    fderiv ℝ (fun y => B y v w) x u = fderiv ℝ B x u v w := by
  rw [fderiv_clm_apply (hB.clm_apply (differentiableAt_const v))
    (differentiableAt_const w), fderiv_clm_apply hB (differentiableAt_const v)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, fderiv_const_apply, ContinuousLinearMap.zero_apply,
    map_zero, zero_add]

theorem cyclic_trilinear_zero_of_basis {E ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (e : Module.Basis ι ℝ E)
    (D : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (h : ∀ i j k, D (e i) (e j) (e k) + D (e j) (e k) (e i) +
      D (e k) (e i) (e j) = 0) (u v w : E) :
    D u v w + D v w u + D w u v = 0 := by
  have hthird (i j : ι) (q : E) :
      D (e i) (e j) q + D (e j) q (e i) + D q (e i) (e j) = 0 := by
    let L : E →L[ℝ] ℝ := D (e i) (e j) + (D (e j)).flip (e i) + (D.flip (e i)).flip (e j)
    have hL : L.toLinearMap = 0 := by
      apply e.ext
      intro k
      change D (e i) (e j) (e k) + D (e j) (e k) (e i) + D (e k) (e i) (e j) = 0
      exact h i j k
    exact congrArg (fun A : E →ₗ[ℝ] ℝ => A q) hL
  have hsecond (i : ι) (p q : E) :
      D (e i) p q + D p q (e i) + D q (e i) p = 0 := by
    let L : E →L[ℝ] ℝ := (D (e i)).flip q + (D.flip q).flip (e i) + D q (e i)
    have hL : L.toLinearMap = 0 := by
      apply e.ext
      intro j
      exact hthird i j q
    exact congrArg (fun A : E →ₗ[ℝ] ℝ => A p) hL
  let L : E →L[ℝ] ℝ := (D.flip v).flip w + D v w + (D w).flip v
  have hL : L.toLinearMap = 0 := by
    apply e.ext
    intro i
    exact hsecond i v w
  exact congrArg (fun A : E →ₗ[ℝ] ℝ => A u) hL

end Yau.LeafProofs.SharedCalculus
