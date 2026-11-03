import Yau.Proofs.P02BusemannConvergence
import Yau.LeafProofs.L22Complete

noncomputable section
open Filter
open scoped Topology ContDiff Manifold Matrix ComplexOrder NNReal

namespace Yau.NodeProofs.P02Aux
open Yau Yau.Blueprint Yau.LeafProofs

/-- The constructive Richberg leaf also provides positivity of the computed
Levi matrix, before its result is repackaged in the classical definition. -/
theorem richberg_actual_levi {n : ℕ} {M : ComplexManifold n}
    (u ε : M.Carrier → ℝ) (hu : LeafCandidates.ClassicalStrictPsh u)
    (hε : Continuous ε) (hεpos : ∀ x, 0 < ε x) :
    ∃ ψ : M.Carrier → ℝ, IsSmoothStrictPsh ψ ∧ ∀ x, |ψ x-u x| < ε x := by
  obtain ⟨ι,χ,δ,g,W,hχ,hδ,hW,hsupp,hcover,hgs,hgpos,hcore,hzero,hupper⟩ :=
    L22Aux.exists_strict_branch_cover u ε hu hε hεpos
  classical
  let ψ := L22Aux.patchedRegularizedMax χ hχ δ g
  have hψs : SmoothFn ψ :=
    L22Aux.patchedRegularizedMax_smoothFn χ hχ δ hδ g u W hW hsupp hcover hcore hzero hgs
  have hψpos : ∀ x, (levi ψ x).PosDef :=
    L22Aux.patchedRegularizedMax_levi_posDef χ hχ δ hδ g u W hW hsupp hcover hcore hzero hgs hgpos
  refine ⟨ψ,⟨hψs,hψpos⟩,?_⟩
  intro x
  have hb := L22Aux.patchedRegularizedMax_error χ hχ δ hδ g u ε W hsupp hcover hcore hupper x
  rw [abs_of_pos (sub_pos.mpr hb.1)]
  linarith [hb.2]

theorem strictPshWeight_of_classical_busemann {n : ℕ}
    (X : KahlerManifold n) (o : Pt X) (ray : ℝ≥0 → Pt X) (b : Pt X → ℝ)
    (hlim : ∀ x, Tendsto (fun j : ℕ => signedDistanceSeq X o ray j x) atTop (𝓝 (b x)))
    (hlip : ∀ x y, |b x-b y| ≤ distFrom X.metric.form x y)
    (hclass : LeafCandidates.ClassicalStrictPsh b) : StrictPshWeight X o := by
  obtain ⟨ψ,hψ,herr⟩ := richberg_actual_levi b (fun _ => 1) hclass continuous_const
    (fun _ => by norm_num)
  refine ⟨ψ,hψ,1,?_⟩
  intro x
  have H := (abs_lt.mp (herr x)).2
  have hb := (busemann_le_distance X o ray b hlim hlip).2 x
  simp only [one_mul]
  linarith

end Yau.NodeProofs.P02Aux
