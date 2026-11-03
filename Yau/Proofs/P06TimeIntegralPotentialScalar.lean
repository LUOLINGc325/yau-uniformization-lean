import Yau.Proofs.P06TimeIntegralPotentialLevi

/-! The original bounded scalar heat class supplies every hypothesis of the
local integral calculus. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold
namespace Yau.NodeProofs.P06Aux.TimePotential
open Yau Yau.Blueprint
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {M : ComplexManifold n}

theorem boundedScalarHeat_intervalIntegrable {g : HermitianField M}
    {f : M.Carrier → ℝ} {u : ℝ → M.Carrier → ℝ}
    (hu : IsBoundedScalarHeat g f u) {T : ℝ} (hT : 0 < T) (x : M.Carrier) :
    IntervalIntegrable (fun s => u s x) volume 0 T := by
  obtain ⟨B, _, hb⟩ := hu.2.2.1 T hT
  exact intervalIntegrable_of_positive_continuous_bound
    (fun s hs => (hu.2.2.2 x s hs).continuousAt.continuousWithinAt) hT
    (fun s hs hsT => by simpa only [Real.norm_eq_abs] using hb x s hs hsT)

theorem boundedScalarHeat_integral_smooth {g : HermitianField M}
    {f : M.Carrier → ℝ} {u : ℝ → M.Carrier → ℝ}
    (hf : SmoothFn f) (hu : IsBoundedScalarHeat g f u) {T : ℝ} (hT : 0 < T) :
    SmoothFn (fun y => ∫ s in (0 : ℝ)..T, u s y) := by
  intro x
  exact integral_contDiffOn (isOpen_extChartAt_target (I := ComplexModel n) x)
    (hu.1 x) (hf x) (hu.2.1.2 x) hT

theorem boundedScalarHeat_levi_intervalIntegrable {g : HermitianField M}
    {f : M.Carrier → ℝ} {u : ℝ → M.Carrier → ℝ}
    (hf : SmoothFn f) (hu : IsBoundedScalarHeat g f u) {T : ℝ} (hT : 0 < T)
    (x : M.Carrier) (a b : Fin n) :
    IntervalIntegrable (fun s => levi (u s) x a b) volume 0 T := by
  exact leviC_intervalIntegrable (isOpen_extChartAt_target (I := ComplexModel n) x)
    (hu.1 x) (hf x) (hu.2.1.2 x) (mem_extChartAt_target x) hT a b

theorem boundedScalarHeat_levi_integral {g : HermitianField M}
    {f : M.Carrier → ℝ} {u : ℝ → M.Carrier → ℝ}
    (hf : SmoothFn f) (hu : IsBoundedScalarHeat g f u) {T : ℝ} (hT : 0 < T)
    (x : M.Carrier) (a b : Fin n) :
    levi (fun y => ∫ s in (0 : ℝ)..T, u s y) x a b =
      ∫ s in (0 : ℝ)..T, levi (u s) x a b := by
  exact leviC_integral (isOpen_extChartAt_target (I := ComplexModel n) x)
    (hu.1 x) (hf x) (hu.2.1.2 x) (mem_extChartAt_target x) hT a b

end Yau.NodeProofs.P06Aux.TimePotential
