import Mathlib.Topology.Homotopy.Lifting

/-! The same pointwise path lifts depend continuously on their parameters. -/
noncomputable section
open scoped Topology
open unitInterval
namespace Yau.Proofs.C03Aux.ShortLift

theorem continuous_lift_endpoints
    {E X A : Type*} [TopologicalSpace E] [T2Space E]
    [TopologicalSpace X] [TopologicalSpace A]
    {p : E → X} (hp : IsLocalHomeomorph p)
    (f : C(I × A, X)) (g : I × A → E) (hg : p ∘ g = f)
    (hstart : Continuous (fun a => g (0, a)))
    (hpaths : ∀ a, Continuous (fun t => g (t, a))) :
    Continuous (fun a => g (1, a)) :=
  (hp.continuous_lift (T2Space.isSeparatedMap p) f hg hstart hpaths).comp
    (continuous_const.prodMk continuous_id)

theorem path_lift_unique
    {E X : Type*} [TopologicalSpace E] [T2Space E] [TopologicalSpace X]
    {p : E → X} (hp : IsLocalHomeomorph p)
    {g h : I → E} (hg : Continuous g) (hh : Continuous h)
    (hlift : p ∘ g = p ∘ h) (hstart : g 0 = h 0) : g = h :=
  (T2Space.isSeparatedMap p).eq_of_comp_eq hp.isLocallyInjective hg hh hlift 0 hstart

end Yau.Proofs.C03Aux.ShortLift
