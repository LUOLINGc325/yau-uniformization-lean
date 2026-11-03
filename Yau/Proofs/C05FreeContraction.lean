import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps

/-! A finite-time flow homotopy transports null-homotopy even when its base point moves. -/

noncomputable section

namespace Yau.Proofs.C05Aux

variable {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]

theorem loop_nullhomotopic_of_map_homotopy
    {f g : C(A, B)} (H : f.Homotopy g) {x : A} (γ : Path x x)
    (hg : (γ.map g.continuous).Homotopic (Path.refl (g x))) :
    (γ.map f.continuous).Homotopic (Path.refl (f x)) := by
  have hq := Path.Homotopic.Quotient.eq.mpr (Path.Homotopic.map_trans_evalAt H γ)
  simp only [Path.Homotopic.Quotient.mk_trans] at hq
  rw [Path.Homotopic.Quotient.eq.mpr hg,
    Path.Homotopic.Quotient.mk_refl, Path.Homotopic.Quotient.trans_refl] at hq
  apply Path.Homotopic.Quotient.eq.mp
  have hc := congrArg (fun q : Path.Homotopic.Quotient (f x) (g x) =>
    Path.Homotopic.Quotient.trans q
      (Path.Homotopic.Quotient.symm (Path.Homotopic.Quotient.mk (H.evalAt x)))) hq
  simpa only [Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.trans_symm,
    Path.Homotopic.Quotient.trans_refl, Path.Homotopic.Quotient.mk_refl] using hc

end Yau.Proofs.C05Aux
