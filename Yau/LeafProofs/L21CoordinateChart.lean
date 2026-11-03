import Yau.LeafProofs.L21GraphIntertwining
import Yau.LeafProofs.L21LocalChart

/-! Scalar graph equations give the original vector-valued differential
identity for the actual smooth chart supplied by the inverse function theorem. -/

open scoped ContDiff
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

theorem vector_intertwines_of_dbarA_eq_zero
    (J : X n → X n →L[ℝ] X n) (x : X n)
    (hJ2 : ∀ v, J x (J x v) = -v) (hi : (J x + stdComplex n).IsInvertible)
    (F : X n → X n) (hF : DifferentiableAt ℝ F x)
    (hD : ∀ i k, dbarA (graphMatrix (fun y => cayleyMap (J y))) i (fun y => F y k) x = 0)
    (v : X n) :
    fderiv ℝ F x (J x v) = Complex.I • fderiv ℝ F x v := by
  ext k
  have hk := (dbarA_cayley_eq_zero_iff J x hJ2 hi (fun y => F y k)).mp (fun i => hD i k) v
  let pr : X n →L[ℝ] ℂ := (EuclideanSpace.proj k).restrictScalars ℝ
  have hd : fderiv ℝ (fun y => F y k) x = pr.comp (fderiv ℝ F x) :=
    (pr.hasFDerivAt.comp x hF.hasFDerivAt).fderiv
  rw [hd] at hk
  change (fderiv ℝ F x (J x v)) k = Complex.I * (fderiv ℝ F x v) k at hk
  exact hk

theorem normalized_chart_of_coordinates
    (J : X n → X n →L[ℝ] X n)
    (hJ2 : ∀ x ∈ Metric.ball (0 : X n) 2, ∀ v, J x (J x v) = -v)
    (hi : ∀ x ∈ Metric.ball (0 : X n) 2, (J x + stdComplex n).IsInvertible)
    (F : X n → X n) (hF : ContDiff ℝ ∞ F)
    (hD : ∀ x ∈ Metric.ball (0 : X n) (1 / 2 : ℝ), ∀ i k,
      dbarA (graphMatrix (fun y => cayleyMap (J y))) i (fun y => F y k) x = 0)
    (hclose : ∀ x ∈ Metric.ball (0 : X n) (1 / 2 : ℝ),
      ‖fderiv ℝ F x - ContinuousLinearMap.id ℝ (X n)‖ ≤ (1 / 4 : ℝ)) :
    ∃ e : OpenPartialHomeomorph (X n) (X n),
      0 ∈ e.source ∧ e.source ⊆ Metric.ball 0 (1 / 2 : ℝ) ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      ∀ x ∈ e.source, ∀ v,
        fderiv ℝ e x (J x v) = Complex.I • fderiv ℝ e x v := by
  obtain ⟨e, hzero, hsource, hcoe, he, heinv⟩ := local_chart_of_small_derivative F hF hclose
  refine ⟨e, hzero, hsource, he, heinv, ?_⟩
  intro x hx v
  rw [hcoe]
  have hx2 : x ∈ Metric.ball (0 : X n) 2 :=
    Metric.ball_subset_ball (by norm_num) (hsource hx)
  exact vector_intertwines_of_dbarA_eq_zero J x (hJ2 x hx2) (hi x hx2)
    F (hF.differentiable (by simp) x) (hD x (hsource hx)) v

end Yau.LeafProofs.L21Aux
