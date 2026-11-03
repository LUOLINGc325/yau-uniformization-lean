import Yau.Proofs.F03DirectionalJets

/-! Local source linearity and sharp support of actual directional jets. -/
noncomputable section
open Filter Set
open scoped Topology ContDiff
namespace Yau.Proofs.F03Aux
open Yau
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem directionalWordDerivative_tsupport_subset (f : E → ℝ) (w : List E) :
    tsupport (directionalWordDerivative f w) ⊆ tsupport f := by
  induction w with
  | nil => exact subset_rfl
  | cons v w ih => exact (tsupport_fderiv_apply_subset ℝ v).trans ih

theorem directionalWordDerivative_add_on {Q : Set E} (hQ : IsOpen Q)
    {f k : E → ℝ} (hf : ContDiffOn ℝ ∞ f Q) (hk : ContDiffOn ℝ ∞ k Q) (w : List E) :
    EqOn (directionalWordDerivative (fun x => f x+k x) w)
      (fun x => directionalWordDerivative f w x + directionalWordDerivative k w x) Q := by
  induction w with
  | nil => intro x hx; rfl
  | cons v w ih =>
    intro x hx
    have heq : directionalWordDerivative (fun y => f y+k y) w =ᶠ[𝓝 x]
        (fun y => directionalWordDerivative f w y + directionalWordDerivative k w y) := by
      filter_upwards [hQ.mem_nhds hx] with y hy
      exact ih hy
    have hdf := ((directionalWordDerivative_contDiffOn hQ hf w).contDiffAt
      (hQ.mem_nhds hx)).differentiableAt (by simp)
    have hdk := ((directionalWordDerivative_contDiffOn hQ hk w).contDiffAt
      (hQ.mem_nhds hx)).differentiableAt (by simp)
    change fderiv ℝ (directionalWordDerivative (fun y => f y+k y) w) x v = _
    rw [heq.fderiv_eq]
    change (fderiv ℝ (directionalWordDerivative f w + directionalWordDerivative k w) x) v = _
    rw [fderiv_add hdf hdk]
    rfl

theorem directionalWordDerivative_const_mul (f : E → ℝ) (c : ℝ) (w : List E) :
    directionalWordDerivative (fun x => c*f x) w =
      (fun x => c*directionalWordDerivative f w x) := by
  induction w with
  | nil => rfl
  | cons v w ih =>
    funext x
    change fderiv ℝ (directionalWordDerivative (fun y => c*f y) w) x v = _
    rw [ih]
    change fderiv ℝ (c • directionalWordDerivative f w) x v = _
    rw [fderiv_const_smul_field]
    rfl

end Yau.Proofs.F03Aux
