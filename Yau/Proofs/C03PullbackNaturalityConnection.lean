import Yau.Proofs.C03PullbackNaturalityAlgebra

/-! Local coordinate connection naturality follows by differentiating the
actual metric pullback, without any global Kähler assumption on the source. -/

noncomputable section

namespace Yau.Proofs.C03Aux.PullbackNaturality

set_option backward.isDefEq.respectTransparency false

open Filter
open scoped Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem metric_pullback_scalar_derivative
    (g : E → E →L[ℝ] E →L[ℝ] ℝ) (f : E → E) (z u v w : E)
    (hg : DifferentiableAt ℝ g (f z)) (hf : ContDiffAt ℝ 2 f z) :
    fderiv ℝ (fun p => g (f p) (fderiv ℝ f p v) (fderiv ℝ f p w)) z u =
      (fderiv ℝ g (f z) (fderiv ℝ f z u)) (fderiv ℝ f z v) (fderiv ℝ f z w) +
      g (f z) (fderiv ℝ (fderiv ℝ f) z u v) (fderiv ℝ f z w) +
      g (f z) (fderiv ℝ f z v) (fderiv ℝ (fderiv ℝ f) z u w) := by
  have hfD := hf.differentiableAt (by norm_num)
  have hJ := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hgfD := (hg.hasFDerivAt).comp (g := g) (f := f) z hfD.hasFDerivAt
  have hgf := hgfD.differentiableAt
  have hJv := hJ.clm_apply (differentiableAt_const v)
  have hJw := hJ.clm_apply (differentiableAt_const w)
  have hC := hgf.clm_apply hJv
  simp only [Function.comp_def] at hgfD hgf hC
  rw [fderiv_clm_apply hC hJw]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply]
  rw [fderiv_clm_apply hgf hJv]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply]
  rw [hgfD.fderiv, fderiv_clm_apply hJ (differentiableAt_const v),
    fderiv_clm_apply hJ (differentiableAt_const w)]
  simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add, add_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.comp_apply]
  ring

theorem connection_chain_of_metric_pullback
    (g₀ g₁ : E → E →L[ℝ] E →L[ℝ] ℝ)
    (Γ₀ Γ₁ : E → E →L[ℝ] E →L[ℝ] E)
    (f : E → E) (z : E)
    (hf : ContDiffAt ℝ 2 f z)
    (hg₀ : DifferentiableAt ℝ g₀ z) (hg₁ : DifferentiableAt ℝ g₁ (f z))
    (hgSymm : ∀ u v, g₁ (f z) u v = g₁ (f z) v u)
    (hgPos : ∀ u, g₁ (f z) u u = 0 → u = 0)
    (hJ : Function.Surjective (fderiv ℝ f z))
    (hΓ₀ : ∀ u v, Γ₀ z u v = Γ₀ z v u)
    (hΓ₁ : ∀ u v, Γ₁ (f z) u v = Γ₁ (f z) v u)
    (hcompat₀ : ∀ u v w, (fderiv ℝ g₀ z u) v w =
      g₀ z (Γ₀ z u v) w + g₀ z v (Γ₀ z u w))
    (hcompat₁ : ∀ u v w, (fderiv ℝ g₁ (f z) u) v w =
      g₁ (f z) (Γ₁ (f z) u v) w + g₁ (f z) v (Γ₁ (f z) u w))
    (hpull : ∀ᶠ p in 𝓝 z, ∀ u v, g₀ p u v =
      g₁ (f p) (fderiv ℝ f p u) (fderiv ℝ f p v)) :
    ∀ u v, fderiv ℝ f z (Γ₀ z u v) =
      fderiv ℝ (fderiv ℝ f) z u v +
        Γ₁ (f z) (fderiv ℝ f z u) (fderiv ℝ f z v) := by
  let J := fderiv ℝ f z
  let H := fderiv ℝ (fderiv ℝ f) z
  let D := fun u v => J (Γ₀ z u v) - (H u v + Γ₁ (f z) (J u) (J v))
  have hH : ∀ u v, H u v = H v u := hf.isSymmSndFDerivAt (by norm_num)
  have hD : ∀ u v, D u v = D v u := by
    intro u v
    dsimp only [D]
    rw [hΓ₀ u v, hH u v, hΓ₁ (J u) (J v)]
  have hcomp : ∀ u v w, g₁ (f z) (D u v) (J w) + g₁ (f z) (J v) (D u w) = 0 := by
    intro u v w
    have heq : (fun p => g₀ p v w) =ᶠ[𝓝 z]
        (fun p => g₁ (f p) (fderiv ℝ f p v) (fderiv ℝ f p w)) :=
      hpull.mono (fun p h => h v w)
    have hd := congrArg (fun L : E →L[ℝ] ℝ => L u) heq.fderiv_eq
    rw [Yau.LeafProofs.L12Aux.fderiv_bilin_apply_const hg₀ u v w,
      metric_pullback_scalar_derivative g₁ f z u v w hg₁ hf] at hd
    rw [hcompat₀, hcompat₁] at hd
    rw [hpull.self_of_nhds (Γ₀ z u v) w, hpull.self_of_nhds v (Γ₀ z u w)] at hd
    dsimp only [D]
    simp only [map_sub, map_add, sub_apply,
      add_apply]
    dsimp only [J, H] at *
    linarith
  intro u v
  exact sub_eq_zero.mp
    (symmetric_metric_skew_vanish (g₁ (f z)) J D hgSymm hgPos hJ hD hcomp u v)

end Yau.Proofs.C03Aux.PullbackNaturality

