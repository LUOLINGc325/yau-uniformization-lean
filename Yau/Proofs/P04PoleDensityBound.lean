import Yau.Proofs.P04PoleAnnulusBounds
import Yau.Proofs.P04PoleChartValues

noncomputable section
open Set
open scoped Topology Manifold ContDiff

namespace Yau.Proofs.P04Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

/-- The density of every regularized weight has ONE bound on the fixed
annulus. The continuous parameter includes epsilon zero away from the pole. -/
theorem pole_annulus_density_uniform_bound (p : M.Carrier)
    {χ : ComplexVector n → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (c k : ℝ) {ψ : M.Carrier → ℝ} (hψ : SmoothFn ψ)
    {ρ : ℝ} (hρ : 0 < ρ) (hs : poleAnnulus (chartPt p p) ρ ⊆ chartTarget p) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ ε ∈ Icc (0 : ℝ) ρ, ∀ z ∈ poleAnnulus (chartPt p p) ρ,
      Real.exp (-(k*inChart p ψ z+regularizedPoleModel χ (chartPt p p) c ε z)) ≤ D := by
  let K : Set (ℝ × ComplexVector n) := Icc (0 : ℝ) ρ ×ˢ poleAnnulus (chartPt p p) ρ
  have hK : IsCompact K := isCompact_Icc.prod (poleAnnulus_isCompact _ _)
  let F : ℝ × ComplexVector n → ℝ :=
    fun q => Real.exp (-(k*inChart p ψ q.2+regularizedPoleModel χ (chartPt p p) c q.1 q.2))
  have hF : ContinuousOn F K := by
    intro q hq
    have hbase : ContDiffAt ℝ ∞ (fun w : ℝ × ComplexVector n => inChart p ψ w.2) q :=
      ((hψ p).contDiffAt ((isOpen_extChartAt_target p).mem_nhds (hs hq.2))).comp q contDiffAt_snd
    have hpole := regularizedPoleModel_joint_off_center hχ (chartPt p p) c q
      (poleAnnulus_ne_center _ hρ hq.2)
    exact (((contDiffAt_const.mul hbase).add hpole).neg.exp).continuousAt.continuousWithinAt
  obtain ⟨D,hD⟩ := hK.exists_bound_of_continuousOn hF
  refine ⟨max D 0,le_max_right _ _,fun ε hε z hz => ?_⟩
  have H := hD (ε,z) ⟨hε,hz⟩
  change ‖Real.exp (-(k*inChart p ψ z+regularizedPoleModel χ (chartPt p p) c ε z))‖ ≤ D at H
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] at H
  exact H.trans (le_max_left _ _)

end Yau.Proofs.P04Aux
