import Yau.Proofs.C07HomotopyLift
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-! Original simple connectivity supplies a continuous fixed-endpoint square for the same curves. -/

open scoped Manifold Topology

noncomputable section

namespace Yau.Proofs.C07Aux

open Yau

variable {n : ℕ} {M : ComplexManifold n}

theorem curve_homotopy_square (hsimply : SimplyConnectedSpace M.Carrier)
    {o x : M.Carrier} (γ η : PiecewiseC1Curve o x) :
    ∃ H : C(unitInterval × unitInterval, M.Carrier),
      (∀ s, H (0, s) = o) ∧ (∀ s, H (1, s) = x) ∧
      (∀ u, H (u, 0) = γ u) ∧ (∀ u, H (u, 1) = η u) := by
  letI : SimplyConnectedSpace M.Carrier := hsimply
  let p : Path o x :=
    { toFun := fun u => γ u
      continuous_toFun := γ.continuous_on.comp_continuous continuous_subtype_val (fun u => u.2)
      source' := by simpa using γ.start_eq
      target' := by simpa using γ.finish_eq }
  let q : Path o x :=
    { toFun := fun u => η u
      continuous_toFun := η.continuous_on.comp_continuous continuous_subtype_val (fun u => u.2)
      source' := by simpa using η.start_eq
      target' := by simpa using η.finish_eq }
  obtain ⟨G⟩ := SimplyConnectedSpace.paths_homotopic p q
  let H : C(unitInterval × unitInterval, M.Carrier) :=
    ⟨fun z => G (z.2, z.1), G.continuous.comp continuous_swap⟩
  refine ⟨H, fun s => G.source s, fun s => G.target s, ?_, ?_⟩
  · intro u
    exact G.map_zero_left u
  · intro u
    exact G.map_one_left u

end Yau.Proofs.C07Aux
