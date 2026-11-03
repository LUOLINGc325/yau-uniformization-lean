import spec.CHAIN.CONTRACTS
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

/-! Actual derivative coherence survives uniform jet limits on convex
sets, including closed time faces. No open time extension is assumed. -/
noncomputable section
open Set Filter
open scoped Topology
namespace Yau.NodeProofs.F01Aux
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem convex_limit_remainder_bound
    {S : Set E} (hS : Convex ℝ S) (f : ℕ → E → F)
    (f' : ℕ → E → E →L[ℝ] F) (g : E → F)
    (hf : ∀ m z, z ∈ S → HasFDerivWithinAt (f m) (f' m z) S z)
    (hpoint : ∀ z ∈ S, Tendsto (fun m => f m z) atTop (𝓝 (g z)))
    (L : E →L[ℝ] F) {C : ℝ}
    (hbound : ∀ᶠ m in atTop, ∀ z ∈ S, ‖f' m z - L‖ ≤ C)
    {x y : E} (hx : x ∈ S) (hy : y ∈ S) :
    ‖g y - g x - L (y - x)‖ ≤ C * ‖y - x‖ := by
  have hlim : Tendsto (fun m => ‖f m y - f m x - L (y - x)‖) atTop
      (𝓝 ‖g y - g x - L (y - x)‖) :=
    (((hpoint y hy).sub (hpoint x hx)).sub_const _).norm
  apply le_of_tendsto hlim
  filter_upwards [hbound] with m hm
  have hjet (z : E) (hz : z ∈ S) :
      HasFDerivWithinAt (fun w => f m w - L w) (f' m z - L) S z :=
    (hf m z hz).sub L.hasFDerivAt.hasFDerivWithinAt
  have hh := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le hjet hm hS hx hy
  have he : (f m y - L y) - (f m x - L x) = f m y - f m x - L (y - x) := by
    rw [map_sub]
    abel
  rw [he] at hh
  exact hh

theorem hasFDerivWithinAt_of_uniform_jet_limit
    {S : Set E} (hS : Convex ℝ S) (f : ℕ → E → F)
    (f' : ℕ → E → E →L[ℝ] F) (g : E → F) (g' : E → E →L[ℝ] F)
    (hf : ∀ m z, z ∈ S → HasFDerivWithinAt (f m) (f' m z) S z)
    (hpoint : ∀ z ∈ S, Tendsto (fun m => f m z) atTop (𝓝 (g z)))
    (huniform : TendstoUniformlyOn f' g' atTop S) (hg' : ContinuousOn g' S)
    {x : E} (hx : x ∈ S) : HasFDerivWithinAt g (g' x) S x := by
  rw [hasFDerivWithinAt_iff_isLittleO]
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  obtain ⟨δ, hδ, hclose⟩ := (Metric.continuousWithinAt_iff.mp (hg' x hx)) (ε / 2) (half_pos hε)
  have hUniform := (Metric.tendstoUniformlyOn_iff.mp huniform) (ε / 2) (half_pos hε)
  have hbound : ∀ᶠ m in atTop, ∀ z ∈ S ∩ Metric.ball x δ,
      ‖f' m z - g' x‖ ≤ ε := by
    filter_upwards [hUniform] with m hm
    intro z hz
    have h1 : ‖f' m z - g' z‖ ≤ ε / 2 := by
      simpa only [dist_eq_norm, norm_sub_rev] using (hm z hz.1).le
    have h2 : ‖g' z - g' x‖ ≤ ε / 2 := by
      simpa only [dist_eq_norm] using (hclose hz.1 (Metric.mem_ball.mp hz.2)).le
    calc
      _ = ‖(f' m z - g' z) + (g' z - g' x)‖ := by congr 1; abel
      _ ≤ ‖f' m z - g' z‖ + ‖g' z - g' x‖ := norm_add_le _ _
      _ ≤ ε := by linarith
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds x hδ)] with y hy hyball
  exact convex_limit_remainder_bound (hS.inter (convex_ball x δ)) f f' g
    (fun m z hz => (hf m z hz.1).mono inter_subset_left)
    (fun z hz => hpoint z hz.1) (g' x) hbound
    ⟨hx, Metric.mem_ball_self hδ⟩ ⟨hy, hyball⟩

end Yau.NodeProofs.F01Aux
