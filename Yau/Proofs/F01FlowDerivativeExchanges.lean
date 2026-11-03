import Yau.Proofs.F01PotentialChartIdentity
import Yau.Proofs.F01PotentialMixedExchange

/-! The original native flow-potential identity gives the paper's exact
first and second derivative exchanges for actual holomorphic chart coefficients. -/
noncomputable section
open Set
open scoped Manifold ContDiff Matrix
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem metric_potential_first_jet_exchange (α k : HermitianField M)
    (hα : MetricSmooth α) (hk : MetricSmooth k)
    (u : M.Carrier → ℝ) (hu : SmoothFn u) (t : ℝ)
    (hpot : ∀ x, gMat k x = gMat α x - (t : ℂ) • ricci α x + levi u x)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    {z : ComplexVector n} (hz : z ∈ e.source) (i j l : Fin n) :
    wirt (fun w => pullbackMatrix k e w i j) z (stdVec l) -
        wirt (fun w => pullbackMatrix k e w i l) z (stdVec j) =
      wirt (fun w => pullbackMatrix α e w i j) z (stdVec l) -
        wirt (fun w => pullbackMatrix α e w i l) z (stdVec j) := by
  have hdα (p q : Fin n) := (pullbackMatrix_entry_contDiffAt α hα e he hz p q).differentiableAt (by simp)
  have hdk (p q : Fin n) := (pullbackMatrix_entry_contDiffAt k hk e he hz p q).differentiableAt (by simp)
  have hh := potential_difference_wirt_closed (pullbackMatrix α e) (pullbackMatrix k e)
    (localFlowPotential α u t e) e.open_source
    (localFlowPotential_contDiffOn α hα u hu t e he hei)
    (fun w hw => metric_potential_identity_in_chart α k hα u hu t hpot e he hei hw) hz i j l
  change wirt (fun w => pullbackMatrix k e w i j - pullbackMatrix α e w i j) z (stdVec l) =
    wirt (fun w => pullbackMatrix k e w i l - pullbackMatrix α e w i l) z (stdVec j) at hh
  rw [wirt_sub_rule _ _ z _ (hdk i j) (hdα i j),
    wirt_sub_rule _ _ z _ (hdk i l) (hdα i l)] at hh
  linear_combination hh

theorem metric_potential_second_jet_exchange (α k : HermitianField M)
    (hα : MetricSmooth α) (hk : MetricSmooth k)
    (u : M.Carrier → ℝ) (hu : SmoothFn u) (t : ℝ)
    (hpot : ∀ x, gMat k x = gMat α x - (t : ℂ) • ricci α x + levi u x)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    {z : ComplexVector n} (hz : z ∈ e.source) (i a : Fin n) :
    wirt (fun w => wirtBar (fun y => pullbackMatrix k e y i i) w (stdVec a)) z (stdVec a) -
        wirt (fun w => wirtBar (fun y => pullbackMatrix k e y a a) w (stdVec i)) z (stdVec i) =
      wirt (fun w => wirtBar (fun y => pullbackMatrix α e y i i) w (stdVec a)) z (stdVec a) -
        wirt (fun w => wirtBar (fun y => pullbackMatrix α e y a a) w (stdVec i)) z (stdVec i) := by
  exact potential_difference_diagonal_mixed_exchange (pullbackMatrix α e) (pullbackMatrix k e)
    (fun w => pullbackMatrix_isHermitian α e w) (fun w => pullbackMatrix_isHermitian k e w)
    (localFlowPotential α u t e) e.open_source
    (fun p q => pullbackMatrix_entry_contDiffOn α hα e he p q)
    (fun p q => pullbackMatrix_entry_contDiffOn k hk e he p q)
    (localFlowPotential_contDiffOn α hα u hu t e he hei)
    (fun w hw => metric_potential_identity_in_chart α k hα u hu t hpot e he hei hw) hz i a

end Yau.NodeProofs.F01Aux
