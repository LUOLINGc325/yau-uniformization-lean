import Yau.Proofs.V03LeviChain

/-! Native differentiation of the four first-order coefficient equations
of a closed invariant two-form gives the exact Laplacian exchange. -/

open scoped Topology ContDiff
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem secondFDeriv_of_directional_linear_identity {f g h : E → ℝ} {p : E}
    (hf : ContDiffAt ℝ 2 f p) (hg : ContDiffAt ℝ 2 g p) (hh : ContDiffAt ℝ 2 h p)
    (v r s w : E) (a b : ℝ)
    (heq : (fun x => fderiv ℝ f x v) =ᶠ[𝓝 p]
      (fun x => a * fderiv ℝ g x r + b * fderiv ℝ h x s)) :
    fderiv ℝ (fderiv ℝ f) p w v =
      a * fderiv ℝ (fderiv ℝ g) p w r + b * fderiv ℝ (fderiv ℝ h) p w s := by
  have hdf := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hdg := (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hdh := (hh.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hgr := hdg.clm_apply (differentiableAt_const r)
  have hhs := hdh.clm_apply (differentiableAt_const s)
  have hder := congrArg (fun A : E →L[ℝ] ℝ => A w) heq.fderiv_eq
  rw [fderiv_clm_apply hdf (differentiableAt_const v),
    fderiv_fun_add (hgr.const_mul a) (hhs.const_mul b),
    fderiv_const_mul hgr, fderiv_const_mul hhs,
    fderiv_clm_apply hdg (differentiableAt_const r),
    fderiv_clm_apply hdh (differentiableAt_const s)] at hder
  simpa using hder

theorem laplacian_exchange_of_closed_coefficients {U : Set E} (hU : IsOpen U)
    {A B C D : E → ℝ} (hA : ContDiffOn ℝ ∞ A U) (hB : ContDiffOn ℝ ∞ B U)
    (hC : ContDiffOn ℝ ∞ C U) (hD : ContDiffOn ℝ ∞ D U)
    (x y z w : E)
    (h₁ : ∀ p ∈ U, fderiv ℝ A p x = fderiv ℝ D p z - fderiv ℝ C p w)
    (h₂ : ∀ p ∈ U, fderiv ℝ A p y = fderiv ℝ C p z + fderiv ℝ D p w)
    (h₃ : ∀ p ∈ U, fderiv ℝ B p z = fderiv ℝ D p x + fderiv ℝ C p y)
    (h₄ : ∀ p ∈ U, fderiv ℝ B p w = fderiv ℝ D p y - fderiv ℝ C p x)
    {p : E} (hp : p ∈ U) :
    fderiv ℝ (fderiv ℝ A) p x x + fderiv ℝ (fderiv ℝ A) p y y =
      fderiv ℝ (fderiv ℝ B) p z z + fderiv ℝ (fderiv ℝ B) p w w := by
  have hAp : ContDiffAt ℝ 2 A p := (hA.contDiffAt (hU.mem_nhds hp)).of_le (by simp)
  have hBp : ContDiffAt ℝ 2 B p := (hB.contDiffAt (hU.mem_nhds hp)).of_le (by simp)
  have hCp : ContDiffAt ℝ 2 C p := (hC.contDiffAt (hU.mem_nhds hp)).of_le (by simp)
  have hDp : ContDiffAt ℝ 2 D p := (hD.contDiffAt (hU.mem_nhds hp)).of_le (by simp)
  have he₁ : (fun q => fderiv ℝ A q x) =ᶠ[𝓝 p]
      (fun q => 1 * fderiv ℝ D q z + (-1) * fderiv ℝ C q w) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    simpa only [one_mul, neg_one_mul, sub_eq_add_neg] using h₁ q hq
  have he₂ : (fun q => fderiv ℝ A q y) =ᶠ[𝓝 p]
      (fun q => 1 * fderiv ℝ C q z + 1 * fderiv ℝ D q w) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    simpa only [one_mul] using h₂ q hq
  have he₃ : (fun q => fderiv ℝ B q z) =ᶠ[𝓝 p]
      (fun q => 1 * fderiv ℝ D q x + 1 * fderiv ℝ C q y) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    simpa only [one_mul] using h₃ q hq
  have he₄ : (fun q => fderiv ℝ B q w) =ᶠ[𝓝 p]
      (fun q => 1 * fderiv ℝ D q y + (-1) * fderiv ℝ C q x) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    simpa only [one_mul, neg_one_mul, sub_eq_add_neg] using h₄ q hq
  have h₁' := secondFDeriv_of_directional_linear_identity hAp hDp hCp x z w x 1 (-1) he₁
  have h₂' := secondFDeriv_of_directional_linear_identity hAp hCp hDp y z w y 1 1 he₂
  have h₃' := secondFDeriv_of_directional_linear_identity hBp hDp hCp z x y z 1 1 he₃
  have h₄' := secondFDeriv_of_directional_linear_identity hBp hDp hCp w y x w 1 (-1) he₄
  have hCs := hCp.isSymmSndFDerivAt (by norm_num)
  have hDs := hDp.isSymmSndFDerivAt (by norm_num)
  rw [hDs x z, hCs x w] at h₁'
  rw [hCs y z, hDs y w] at h₂'
  linarith

end Yau.Blueprint.V03Proof
