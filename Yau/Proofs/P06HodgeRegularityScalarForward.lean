import Yau.Proofs.P06HodgeRegularityForwardRestriction

/-! The actual scalar finite system and computed forward expression agree. -/
noncomputable section
open scoped Topology ContDiff
namespace Yau.NodeProofs.P06Aux
open Yau.LeafProofs.L03

variable {E ι α : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype ι] [Fintype α] [DecidableEq α]

theorem regularityScalarSystem_eq_forwardPrincipal
    (v : ι → E) (q : ι → ι → E → ℝ)
    (e1 : α → α → ι → E → ℝ) (e0 : α → α → E → ℝ) (U : E → α → ℝ)
    (hq : ∀ i j, ContDiff ℝ ∞ (q i j)) (he1 : ∀ r c i, ContDiff ℝ ∞ (e1 r c i))
    (hU : ∀ c, ContDiff ℝ ∞ (fun z => U z c)) (z : E) (r : α) :
    regularityScalarSystem v q (regularityScalarBeta v q e1) e0 U z r =
      hodgeForwardPrincipal v (regularityScalarSystemA q) e1 e0 U z r := by
  have ha (r c : α) (i j : ι) : ContDiff ℝ ∞ (regularityScalarSystemA q r c i j) := by
    by_cases hrc : r = c
    · simpa only [regularityScalarSystemA,hrc,ite_true] using hq i j
    · simp only [regularityScalarSystemA,hrc,ite_false]
      exact contDiff_const
  have hβ := regularityScalarBeta_contDiff v q e1 hq he1
  rw [← regularityScalarSystem_divergence v q (regularityScalarBeta v q e1) e0 U hβ hU,
    regularityScalarBeta_eq_forward]
  change divergenceSystemApply v (regularityScalarSystemA q)
    (hodgeForwardB v (regularityScalarSystemA q) e1)
    (hodgeForwardC v (regularityScalarSystemA q) e1 e0) U z r = _
  exact hodgeForward_divergence_eq v _ e1 e0 U ha he1 hU z r

end Yau.NodeProofs.P06Aux
