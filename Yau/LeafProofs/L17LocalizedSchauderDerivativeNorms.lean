import Yau.LeafProofs.L17LocalizedSchauderUnitJets
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries

open Set Filter
open scoped Topology
noncomputable section
namespace Yau.LeafProofs.L17LocalizedSchauderAux

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem norm_iteratedFDeriv_succ_sub (k : ℕ) (f g : E → F) (x y : E) :
    ‖iteratedFDeriv ℝ (k+1) f x-iteratedFDeriv ℝ (k+1) g y‖ =
      ‖iteratedFDeriv ℝ k (fderiv ℝ f) x-iteratedFDeriv ℝ k (fderiv ℝ g) y‖ := by
  rw [iteratedFDeriv_succ_eq_comp_right,iteratedFDeriv_succ_eq_comp_right]
  simpa only [Function.comp_apply,dist_eq_norm] using
    (continuousMultilinearCurryRightEquiv' ℝ k E F).symm.isometry.dist_eq
      (iteratedFDeriv ℝ k (fderiv ℝ f) x) (iteratedFDeriv ℝ k (fderiv ℝ g) y)

theorem norm_iteratedFDeriv_zero_sub (f g : E → F) (x y : E) :
    ‖iteratedFDeriv ℝ 0 f x-iteratedFDeriv ℝ 0 g y‖ = ‖f x-g y‖ := by
  rw [iteratedFDeriv_zero_eq_comp,iteratedFDeriv_zero_eq_comp]
  simp only [Function.comp_apply,← map_sub,LinearIsometryEquiv.norm_map]

theorem norm_iteratedFDeriv_one_sub (f g : E → F) (x y : E) :
    ‖iteratedFDeriv ℝ 1 f x-iteratedFDeriv ℝ 1 g y‖ = ‖fderiv ℝ f x-fderiv ℝ g y‖ := by
  exact (norm_iteratedFDeriv_succ_sub 0 f g x y).trans (norm_iteratedFDeriv_zero_sub _ _ x y)

theorem norm_iteratedFDeriv_two_sub (f g : E → F) (x y : E) :
    ‖iteratedFDeriv ℝ 2 f x-iteratedFDeriv ℝ 2 g y‖ =
      ‖fderiv ℝ (fderiv ℝ f) x-fderiv ℝ (fderiv ℝ g) y‖ := by
  exact (norm_iteratedFDeriv_succ_sub 1 f g x y).trans (norm_iteratedFDeriv_one_sub _ _ x y)

theorem fderiv_fderiv_eq_of_true_jets {U : Set E} (hU : IsOpen U)
    (f : E → F) (D : E → E →L[ℝ] F) (H : E → E →L[ℝ] E →L[ℝ] F)
    (hf : ∀ z ∈ U, HasFDerivAt f (D z) z) (hD : ∀ z ∈ U, HasFDerivAt D (H z) z)
    {x : E} (hx : x ∈ U) : fderiv ℝ (fderiv ℝ f) x = H x := by
  have heq : (fderiv ℝ f) =ᶠ[𝓝 x] D := by
    filter_upwards [hU.mem_nhds hx] with z hz
    exact (hf z hz).fderiv
  exact heq.fderiv_eq.trans (hD x hx).fderiv

theorem norm_iteratedFDeriv_le_two_of_true_jets {U : Set E} (hU : IsOpen U)
    (f : E → F) (D : E → E →L[ℝ] F) (H : E → E →L[ℝ] E →L[ℝ] F)
    (hf : ∀ z ∈ U, HasFDerivAt f (D z) z) (hD : ∀ z ∈ U, HasFDerivAt D (H z) z)
    {x : E} (hx : x ∈ U) {C : ℝ} (h0 : ‖f x‖ ≤ C) (h1 : ‖D x‖ ≤ C) (h2 : ‖H x‖ ≤ C) :
    ∀ j : ℕ, j ≤ 2 → ‖iteratedFDeriv ℝ j f x‖ ≤ C := by
  intro j hj
  interval_cases j
  · simpa only [norm_iteratedFDeriv_zero] using h0
  · simpa only [norm_iteratedFDeriv_one,(hf x hx).fderiv] using h1
  · rw [← norm_iteratedFDeriv_fderiv (n := 1),norm_iteratedFDeriv_one,
      fderiv_fderiv_eq_of_true_jets hU f D H hf hD hx]
    exact h2

theorem norm_iteratedFDeriv_sub_le_two_of_true_jets {U : Set E} (hU : IsOpen U)
    (f g : E → F) (D J : E → E →L[ℝ] F) (H K : E → E →L[ℝ] E →L[ℝ] F)
    (hf : ∀ z ∈ U, HasFDerivAt f (D z) z) (hD : ∀ z ∈ U, HasFDerivAt D (H z) z)
    (hg : ∀ z ∈ U, HasFDerivAt g (J z) z) (hJ : ∀ z ∈ U, HasFDerivAt J (K z) z)
    {x y : E} (hx : x ∈ U) (hy : y ∈ U) {C : ℝ}
    (h0 : ‖f x-g y‖ ≤ C) (h1 : ‖D x-J y‖ ≤ C) (h2 : ‖H x-K y‖ ≤ C) :
    ∀ j : ℕ, j ≤ 2 → ‖iteratedFDeriv ℝ j f x-iteratedFDeriv ℝ j g y‖ ≤ C := by
  intro j hj
  interval_cases j
  · simpa only [norm_iteratedFDeriv_zero_sub] using h0
  · simpa only [norm_iteratedFDeriv_one_sub,(hf x hx).fderiv,(hg y hy).fderiv] using h1
  · rw [norm_iteratedFDeriv_two_sub,fderiv_fderiv_eq_of_true_jets hU f D H hf hD hx,
      fderiv_fderiv_eq_of_true_jets hU g J K hg hJ hy]
    exact h2

end Yau.LeafProofs.L17LocalizedSchauderAux
