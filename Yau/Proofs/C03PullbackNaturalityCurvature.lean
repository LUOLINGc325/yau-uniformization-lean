import Yau.LeafProofs.L23DistanceEnergyCovariant

/-! Curvature transport follows from the actual local connection chain rule,
using the commutator of two covariant derivatives. -/

noncomputable section

namespace Yau.Proofs.C03Aux.PullbackNaturality

open Filter Yau.LeafProofs.L23Aux
open scoped Topology ContDiff
set_option backward.isDefEq.respectTransparency false

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem push_covariant_derivative
    (Γ₀ Γ₁ : E → E →L[ℝ] E →L[ℝ] E) (f W : E → E) (z a : E)
    (hf : ContDiffAt ℝ 2 f z) (hW : DifferentiableAt ℝ W z)
    (hchain : ∀ u v, fderiv ℝ f z (Γ₀ z u v) =
      fderiv ℝ (fderiv ℝ f) z u v +
        Γ₁ (f z) (fderiv ℝ f z u) (fderiv ℝ f z v)) :
    mapCovariantD Γ₁ f a (fun p => fderiv ℝ f p (W p)) z =
      fderiv ℝ f z (fderiv ℝ W z a + Γ₀ z a (W z)) := by
  have hJ := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt_one
  simp only [mapCovariantD, mapDirection, fderiv_clm_apply hJ hW,
    add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply, map_add]
  rw [hchain a (W z)]
  abel

theorem mapCovariantD_congr_germ
    (Γ : E → E →L[ℝ] E →L[ℝ] E) (f W V : E → E) (z a : E)
    (h : W =ᶠ[𝓝 z] V) :
    mapCovariantD Γ f a W z = mapCovariantD Γ f a V z := by
  simp only [mapCovariantD, mapDirection, h.fderiv_eq, h.self_of_nhds]

theorem curvature_chain_of_connection_chain
    (O : Set E) (hO : IsOpen O)
    (Γ₀ Γ₁ : E → E →L[ℝ] E →L[ℝ] E) (f : E → E)
    (hf : ContDiffOn ℝ ∞ f O) (hΓ₀ : ContDiffOn ℝ ∞ Γ₀ O)
    (hΓ₁ : ∀ z ∈ O, DifferentiableAt ℝ Γ₁ (f z))
    (hchain : ∀ z ∈ O, ∀ u v, fderiv ℝ f z (Γ₀ z u v) =
      fderiv ℝ (fderiv ℝ f) z u v +
        Γ₁ (f z) (fderiv ℝ f z u) (fderiv ℝ f z v))
    {z : E} (hz : z ∈ O) (u v w : E) :
    fderiv ℝ f z (connectionCurvature Γ₀ z u v w) =
      connectionCurvature Γ₁ (f z)
        (fderiv ℝ f z u) (fderiv ℝ f z v) (fderiv ℝ f z w) := by
  have hfz := hf.contDiffAt (hO.mem_nhds hz)
  have hΓz := hΓ₀.contDiffAt (hO.mem_nhds hz)
  have hfield : ContDiffAt ℝ 2 (fun p => fderiv ℝ f p w) z :=
    (hfz.fderiv_right (m := 2) (by simp)).clm_apply contDiffAt_const
  have hinner (a : E) :
      mapCovariantD Γ₁ f a (fun p => fderiv ℝ f p w) =ᶠ[𝓝 z]
        (fun p => fderiv ℝ f p (Γ₀ p a w)) := by
    filter_upwards [hO.mem_nhds hz] with p hp
    simpa only [fderiv_const_apply, zero_apply, zero_add] using
      push_covariant_derivative Γ₀ Γ₁ f (fun _ => w) p a
        ((hf.contDiffAt (hO.mem_nhds hp)).of_le (by simp))
        (differentiableAt_const w) (hchain p hp)
  have hΓaw (a : E) : DifferentiableAt ℝ (fun p => Γ₀ p a w) z :=
    ((hΓz.differentiableAt (by simp)).clm_apply (differentiableAt_const a)).clm_apply
      (differentiableAt_const w)
  have hdΓ (a b r : E) : fderiv ℝ (fun p => Γ₀ p a b) z r =
      fderiv ℝ Γ₀ z r a b := by
    have HD := ((hΓz.differentiableAt (by simp)).hasFDerivAt.clm_apply
      (hasFDerivAt_const a z)).clm_apply (hasFDerivAt_const b z)
    rw [HD.fderiv]
    simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
      zero_apply, map_zero, zero_add]
  have houter (a b : E) :
      mapCovariantD Γ₁ f a
          (mapCovariantD Γ₁ f b (fun p => fderiv ℝ f p w)) z =
        fderiv ℝ f z (fderiv ℝ Γ₀ z a b w + Γ₀ z a (Γ₀ z b w)) := by
    rw [mapCovariantD_congr_germ Γ₁ f _ _ z a (hinner b),
      push_covariant_derivative Γ₀ Γ₁ f _ z a (hfz.of_le (by simp))
        (hΓaw b) (hchain z hz)]
    congr 1
    rw [hdΓ b w a]
  have hc := mapCovariantD_commutator Γ₁ f (fun p => fderiv ℝ f p w)
    (hΓ₁ z hz) (hfz.of_le (by simp)) hfield u v
  rw [houter u v, houter v u] at hc
  rw [← map_sub] at hc
  rw [show (fderiv ℝ Γ₀ z u v w + Γ₀ z u (Γ₀ z v w)) -
      (fderiv ℝ Γ₀ z v u w + Γ₀ z v (Γ₀ z u w)) =
      connectionCurvature Γ₀ z u v w by
    simp only [connectionCurvature]
    abel] at hc
  exact hc

end Yau.Proofs.C03Aux.PullbackNaturality
