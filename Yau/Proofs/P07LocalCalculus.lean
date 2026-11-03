import Yau.Proofs.P07Affine
import Yau.Proofs.P07DistanceLeviCalculus
import Yau.LeafProofs.L22Locality

/-! Locality and affine formulas for the finite local dyadic expression. -/
noncomputable section
open Filter
open scoped Topology ContDiff Manifold
namespace Yau.NodeProofs.P07Aux
open Yau Yau.Blueprint Yau.LeafProofs.L18Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem smoothFn_of_locally_smooth {u : M.Carrier → ℝ}
    (hu : ∀ x, ∃ f : M.Carrier → ℝ, SmoothFn f ∧ u =ᶠ[𝓝 x] f) : SmoothFn u := by
  apply smoothFn_of_contMDiff_real
  intro x
  obtain ⟨f, hf, heq⟩ := hu x
  exact (contMDiff_real_of_smoothFn hf x).congr_of_eventuallyEq heq

theorem gradNormSq_congr_of_eventuallyEq (h : HermitianField M)
    {f g : M.Carrier → ℝ} {x : M.Carrier} (heq : f =ᶠ[𝓝 x] g) :
    gradNormSq h f x = gradNormSq h g x := by
  have hh : (fun z => Complex.ofReal (inChart x f z)) =ᶠ[𝓝 (chartPt x x)]
      (fun z => Complex.ofReal (inChart x g z)) := by
    filter_upwards [inChart_eventuallyEq heq] with z hz
    exact congrArg Complex.ofReal hz
  simp only [gradNormSq, wirt, hh.fderiv_eq]

theorem leviDirection_affine {f : M.Carrier → ℝ} (hf : SmoothFn f)
    (a b : ℝ) (x : M.Carrier) (v : ComplexVector n) :
    leviDirection (levi (fun y => a * f y + b) x) v = a * leviDirection (levi f x) v := by
  have hz : chartPt x x ∈ chartTarget x := mem_extChartAt_target x
  have hd : deriv (fun s : ℝ => a * s + b) = fun _ => a := by
    funext s
    simpa using (((hasDerivAt_id s).const_mul a).add_const b).deriv
  have hh := P07DistanceLevi.leviDirection_scalar_comp
    ((contDiffAt_inChart hf x hz).of_le (by simp))
    (show ContDiffAt ℝ 2 (fun s : ℝ => a * s + b) (inChart x f (chartPt x x)) from
      (contDiffAt_const.mul contDiffAt_id).add contDiffAt_const) v
  rw [hd] at hh
  change leviDirection (levi (fun y => a * f y + b) x) v =
    a * leviDirection (levi f x) v +
      deriv (fun _ : ℝ => a) (inChart x f (chartPt x x)) *
        P07DistanceLevi.directionalRankOne (inChart x f) (chartPt x x) v at hh
  simpa only [deriv_const, zero_mul, add_zero] using hh

end Yau.NodeProofs.P07Aux
