import Yau.Proofs.F03DirichletCompactInitial
import Yau.Proofs.F03DirichletEvaluation
import Yau.Proofs.F03DirichletRieszKernel

/-! Actual nonzero evaluations and strictly positive diagonal values. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace
namespace Yau.Proofs.F03Aux
open Yau LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

theorem dirichletHeatEvaluationVector_ne_zero (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : Set M.Carrier) (hO : IsOpen O) (x : M.Carrier) (hx : x ∈ O)
    (t : ℝ) (ht : 0 < t) :
    dirichletHeatEvaluationVector g hK μ hμ O hO x hx t ht ≠ 0 := by
  let : LocallyCompactSpace M.Carrier := manifold_locallyCompact M
  obtain ⟨φ,hφone,hφcompact,hφO,hφrange⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen
    isCompact_singleton hO (singleton_subset_iff.mpr hx)
  have hφx : φ x=1 := hφone (mem_singleton x)
  let hfL := continuous_compact_scalarL2 g μ hμ O φ.continuous hφcompact
  obtain ⟨δ,hδ,hclose⟩ := dirichletClassicalHeat_uniform_compact_initial g hK μ hμ O hO φ
    φ.continuous hφcompact hφO hfL (1/2) (by norm_num)
  let s := min (t/2) (δ/2)
  have hs : 0 < s := lt_min (half_pos ht) (half_pos hδ)
  have hst : s < t := (min_le_left _ _).trans_lt (half_lt_self ht)
  have hsδ : s < δ := (min_le_right _ _).trans_lt (half_lt_self hδ)
  have hu : 0 < dirichletClassicalHeat g hK μ hμ O hO (scalarToLp hfL) x s := by
    have hc := hclose s hs hsδ x hx
    rw [hφx] at hc
    have hl := neg_abs_le (dirichletClassicalHeat g hK μ hμ O hO (scalarToLp hfL) x s-1)
    linarith only [hc,hl]
  have hv : dirichletHeatEvaluationVector g hK μ hμ O hO x hx s hs ≠ 0 := by
    intro hz
    have heq := dirichletHeatEvaluationVector_inner g hK μ hμ O hO x hx s hs (scalarToLp hfL)
    rw [hz,inner_zero_left] at heq
    exact hu.ne' heq.symm
  have hts : 0 < t-s := sub_pos.mpr hst
  have hprop := dirichletHeatEvaluationVector_semigroup g hK μ hμ O hO x hx hs hts.le
  have htime : s+(t-s)=t := by ring
  have hprop' : dirichletHeatEvaluationVector g hK μ hμ O hO x hx t ht =
      dirichletHeat g μ hμ O (t-s)
        (dirichletHeatEvaluationVector g hK μ hμ O hO x hx s hs) := by
    simpa only [htime] using hprop
  intro hz
  exact hv ((dirichletHeat_zero_iff g μ hμ O hO hts _).mp (hprop'.symm.trans hz))

theorem dirichletKernelCandidate_diagonal_pos (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : Set M.Carrier) (hO : IsOpen O) (x : M.Carrier) (hx : x ∈ O)
    {t : ℝ} (ht : 0 < t) : 0 < dirichletKernelCandidate g hK μ hμ O hO t x x := by
  rw [dirichletKernelCandidate_of_members g hK μ hμ O hO ht x x hx hx]
  exact real_inner_self_pos.mpr
    (dirichletHeatEvaluationVector_ne_zero g hK μ hμ O hO x hx (t/2) (half_pos ht))

end Yau.Proofs.F03Aux
