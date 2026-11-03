import Yau.Proofs.F05BootstrapDefinitions

/-! The actual inequalities defining a Hölder bound pass to pointwise
limits with their original exponent and constant. -/

open Set Filter
open scoped Topology
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic

theorem F05_holderBound_pointwise_limit {n : ℕ} {V : Type*} [NormedAddCommGroup V]
    {α C : ℝ} {Q : Set (Point n)} {f : ℕ → Point n → V} {g : Point n → V}
    (hf : ∀ k, HolderBound α Q (f k) C)
    (hLim : ∀ z ∈ Q, Tendsto (fun k => f k z) atTop (𝓝 (g z))) :
    HolderBound α Q g C := by
  refine ⟨(hf 0).1,?_,?_⟩
  · intro z hz
    exact le_of_tendsto (hLim z hz).norm (Eventually.of_forall (fun k => (hf k).2.1 z hz))
  · intro z hz w hw
    exact le_of_tendsto ((hLim z hz).sub (hLim w hw)).norm
      (Eventually.of_forall (fun k => (hf k).2.2 z hz w hw))

end Yau.Proofs.F05Aux
