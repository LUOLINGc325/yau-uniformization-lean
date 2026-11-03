import Yau.Proofs.U02AnalyticBounds
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

open scoped ContDiff Topology
open Set Metric

namespace U02AnalyticAux

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem iteratedFDeriv_comp_affine_on
    {s : Set E} (hs : IsOpen s) {f : E → F}
    (hf : ContDiffOn ℂ ∞ f s) (a : ℂ →ᴬ[ℂ] E)
    {z : ℂ} (hz : a z ∈ s) (k : ℕ) :
    iteratedFDeriv ℂ k (f ∘ a) z =
      (iteratedFDeriv ℂ k f (a z)).compContinuousLinearMap
        (fun _ ↦ a.contLinear) := by
  have ht : IsOpen (a ⁻¹' s) := hs.preimage a.continuous
  have hseries := (hf.ftaylorSeriesWithin hs.uniqueDiffOn).comp_continuousAffineMap a
  have heq := hseries.eq_iteratedFDerivWithin_of_uniqueDiffOn
    (m := k) (by exact_mod_cast le_top : (k : ℕ∞ω) ≤ ∞) ht.uniqueDiffOn hz
  change (iteratedFDerivWithin ℂ k f s (a z)).compContinuousLinearMap
    (fun _ ↦ a.contLinear) = iteratedFDerivWithin ℂ k (f ∘ a) (a ⁻¹' s) z at heq
  rw [iteratedFDerivWithin_of_isOpen k hs hz,
    iteratedFDerivWithin_of_isOpen k ht hz] at heq
  exact heq.symm

theorem iteratedDeriv_complex_line_zero
    {s : Set E} (hs : IsOpen s) {f : E → F}
    (hf : ContDiffOn ℂ ∞ f s) {x : E} (hx : x ∈ s)
    (v : E) (k : ℕ) :
    iteratedDeriv k (fun z : ℂ ↦ f (x + z • v)) 0 =
      iteratedFDeriv ℂ k f x (fun _ ↦ v) := by
  let a : ℂ →ᴬ[ℂ] E := ContinuousAffineMap.lineMap x (x + v)
  have ha (z : ℂ) : a z = x + z • v := by
    simp [a, ContinuousAffineMap.coe_lineMap_eq, AffineMap.lineMap_apply_module', add_comm]
  have ha0 : a 0 = x := by simp [ha]
  have hal : a.contLinear 1 = v := by
    have h := a.contLinear_apply_vsub (1 : ℂ) 0
    simpa [ha] using h
  have heq := iteratedFDeriv_comp_affine_on hs hf a (z := 0) (by simpa [ha0] using hx) k
  have hfun : f ∘ a = fun z : ℂ ↦ f (x + z • v) := by ext z; simp [ha]
  rw [hfun, ha0] at heq
  rw [iteratedDeriv_eq_iteratedFDeriv, heq]
  simp [ContinuousMultilinearMap.compContinuousLinearMap_apply, hal]

end U02AnalyticAux
