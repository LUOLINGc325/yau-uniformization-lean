import Yau.Proofs.P06HodgeRegularityForwardRestriction

/-! Genuine compact support of the forward divergence coefficients.
No global ellipticity of these compact extensions is asserted. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux

variable {E ι α : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [Fintype ι] [Fintype α]

theorem regularityScalarSystemA_hasCompactSupport [DecidableEq α]
    (q : ι → ι → E → ℝ) (hcq : ∀ i j, HasCompactSupport (q i j))
    (r c : α) (i j : ι) : HasCompactSupport (regularityScalarSystemA q r c i j) := by
  unfold regularityScalarSystemA
  split_ifs
  · exact hcq i j
  · exact HasCompactSupport.zero

theorem hodgeForwardB_hasCompactSupport
    (v : ι → E) (a : α → α → ι → ι → E → ℝ) (e1 : α → α → ι → E → ℝ)
    (hca : ∀ r c i j, HasCompactSupport (a r c i j))
    (hce1 : ∀ r c i, HasCompactSupport (e1 r c i)) (r c : α) (i : ι) :
    HasCompactSupport (hodgeForwardB v a e1 r c i) := by
  have hs := HasCompactSupport.finset_sum (fun j (_ : j ∈ Finset.univ) =>
    (hca r c j i).fderiv_apply ℝ (v j))
  have hs' : HasCompactSupport (fun z => ∑ j, fderiv ℝ (a r c j i) z (v j)) := by
    convert hs using 1
    funext z
    simp only [Finset.sum_apply]
  exact (hce1 r c i).add hs'

theorem hodgeForwardC_hasCompactSupport
    (v : ι → E) (a : α → α → ι → ι → E → ℝ)
    (e1 : α → α → ι → E → ℝ) (e0 : α → α → E → ℝ)
    (hca : ∀ r c i j, HasCompactSupport (a r c i j))
    (hce1 : ∀ r c i, HasCompactSupport (e1 r c i))
    (hce0 : ∀ r c, HasCompactSupport (e0 r c)) (r c : α) :
    HasCompactSupport (hodgeForwardC v a e1 e0 r c) := by
  have hs := HasCompactSupport.finset_sum (fun i (_ : i ∈ Finset.univ) =>
    (hodgeForwardB_hasCompactSupport v a e1 hca hce1 r c i).fderiv_apply ℝ (v i))
  have hs' : HasCompactSupport (fun z => ∑ i, fderiv ℝ (hodgeForwardB v a e1 r c i) z (v i)) := by
    convert hs using 1
    funext z
    simp only [Finset.sum_apply]
  exact (hce0 r c).sub hs'

end Yau.NodeProofs.P06Aux
