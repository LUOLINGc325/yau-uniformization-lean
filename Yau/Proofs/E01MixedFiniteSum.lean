import Yau.Proofs.V03LeviCalculus

/-! Finite sums commute with the actual totalized mixed Wirtinger derivative at C2 data. -/

noncomputable section
open scoped Topology
open Filter

namespace Yau.NodeProofs.E01Aux
open Yau
open Yau.Blueprint.V03Proof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem mixedWirt_fintype_sum {ι : Type*} [Fintype ι]
    (F : ι → E → ℂ) (z v : E) (hF : ∀ i, ContDiffAt ℝ 2 (F i) z) :
    wirt (fun y => wirtBar (fun x => ∑ i, F i x) y v) z v =
      ∑ i, wirt (fun y => wirtBar (F i) y v) z v := by
  have hnear : ∀ᶠ y in 𝓝 z, ∀ i, ContDiffAt ℝ 2 (F i) y :=
    eventually_all.mpr (fun i => (hF i).eventually (by norm_num))
  have heq : (fun y => wirtBar (fun x => ∑ i, F i x) y v) =ᶠ[𝓝 z]
      (fun y => ∑ i, wirtBar (F i) y v) := by
    filter_upwards [hnear] with y hy
    exact wirtBar_sum Finset.univ F y v (fun i _ => (hy i).differentiableAt (by norm_num))
  have hg : wirt (fun y => wirtBar (fun x => ∑ i, F i x) y v) z v =
      wirt (fun y => ∑ i, wirtBar (F i) y v) z v := by
    unfold wirt
    rw [heq.fderiv_eq]
  rw [hg]
  exact wirt_sum Finset.univ (fun i y => wirtBar (F i) y v) z v
    (fun i _ => wirtBar_differentiableAt (hF i) v)

end Yau.NodeProofs.E01Aux
