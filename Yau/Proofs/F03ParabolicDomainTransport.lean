import Yau.Proofs.F03BoundedHeatEquation

/-! The actual parabolic operator is unchanged by domains containing a neighborhood of the point. -/
noncomputable section
open Filter Set
open scoped Topology
namespace Yau.Proofs.F03Aux
open Yau Parabolic LeafProofs.L16Aux

theorem timeD_eq_deriv_of_mem_nhds {n : ℕ} {Q : Set (Point n)} {u : Point n → ℝ}
    {p : Point n} (hQ : Q ∈ 𝓝 p) :
    timeD Q u p=deriv (fun t => u (p.1,t)) p.2 := by
  exact derivWithin_of_mem_nhds
    ((continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds hQ)

theorem linearOp_congr_of_mem_nhds {n : ℕ} {Q R : Set (Point n)}
    {u v : Point n → ℝ} (a : Point n → Mat n) (b : Point n → RIdx n → ℝ)
    {p : Point n} (hQ : Q ∈ 𝓝 p) (hR : R ∈ 𝓝 p) (heq : u =ᶠ[𝓝 p] v) :
    linearOp Q a b u p=linearOp R a b v p := by
  have hX : (fun x => u (x,p.2)) =ᶠ[𝓝 p.1] (fun x => v (x,p.2)) :=
    heq.comp_tendsto (continuous_id.prodMk continuous_const).continuousAt
  have hS : spatialD u p=spatialD v p := hX.fderiv_eq
  have hSS : spatialDD u p=spatialDD v p := hX.fderiv.fderiv_eq
  have hTime : (fun t => u (p.1,t)) =ᶠ[𝓝 p.2] (fun t => v (p.1,t)) :=
    heq.comp_tendsto (continuous_const.prodMk continuous_id).continuousAt
  simp only [linearOp,timeD_eq_deriv_of_mem_nhds hQ,timeD_eq_deriv_of_mem_nhds hR,
    hTime.deriv_eq,hS,hSS]

end Yau.Proofs.F03Aux
