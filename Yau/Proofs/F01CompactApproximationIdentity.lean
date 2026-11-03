import Yau.Proofs.F01ConformalCoreGerm
import Yau.Proofs.F01ControlledConformalBounds

/-! Every actual compact set is eventually in the base-point component,
where the actual conformal approximating metric and its Ricci tensor equal
the ambient tensors exactly. The level is chosen before the point. -/
noncomputable section
open Set
open scoped Topology Manifold
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Blueprint
variable {n : ℕ}

theorem compact_approximation_identity (X : KahlerManifold n) (o : Pt X)
    (u : Pt X → ℝ) (hu : ControlledExhaustion X o u)
    {K : Set (Pt X)} (hK : IsCompact K) :
    ∃ L0 : ℝ, 0 < L0 ∧ ∀ L : ℝ, L0 ≤ L → ∀ ho : u o < L,
      K ⊆ sublevelComponent u o L ∧
      ∀ x : (sublevelManifold X.manifold u hu.1 o L ho).Carrier, x.val ∈ K →
        approximatingScalar X.manifold u hu.1 o L ho x = 0 ∧
        gMat (approximatingMetric X.manifold X.metric.form u hu.1 o L ho) x = gMat X.metric.form x.val ∧
        ricci (approximatingMetric X.manifold X.metric.form u hu.1 o L ho) x = ricci X.metric.form x.val := by
  haveI : LocallyPathConnectedSpace X.manifold.Carrier :=
    ChartedSpace.locallyPathConnectedSpace (ComplexVector n) X.manifold.Carrier
  haveI : LocallyConnectedSpace X.manifold.Carrier :=
    ChartedSpace.locallyConnectedSpace (ComplexVector n) X.manifold.Carrier
  haveI : PathConnectedSpace X.manifold.Carrier := PathConnectedSpace.of_locallyPathConnectedSpace
  obtain ⟨Lc, hLc⟩ := compact_subset_sublevelComponent (continuous_of_smoothFn hu.1) o hK
  obtain ⟨b, hb⟩ := hK.exists_bound_of_continuousOn (continuous_of_smoothFn hu.1).continuousOn
  let L0 := max Lc (2 * (|b| + 1) + 1)
  have hL0 : 0 < L0 := by
    have h : 0 < 2 * (|b| + 1) + 1 := by positivity
    exact h.trans_le (le_max_right _ _)
  refine ⟨L0, hL0, ?_⟩
  intro L hLL0 ho
  have hL : 0 < L := hL0.trans_le hLL0
  refine ⟨hLc L ((le_max_left _ _).trans hLL0), ?_⟩
  intro x hxK
  have hux : u x.val ≤ |b| := by
    have hh : |u x.val| ≤ b := by simpa only [Real.norm_eq_abs] using hb x.val hxK
    exact (le_abs_self _).trans (hh.trans (le_abs_self b))
  have hscale := (le_max_right Lc (2 * (|b| + 1) + 1)).trans hLL0
  have hcore : u x.val / L < 1 / 2 := (div_lt_iff₀ hL).mpr (by nlinarith)
  have hf : approximatingScalar X.manifold u hu.1 o L ho x = 0 := conformalProfile_zero hcore.le
  refine ⟨hf, ?_, ?_⟩
  · rw [approximatingMetric_eq_conformalBase, conformalField_gMat, hf, Real.exp_zero,
      Complex.ofReal_one, one_smul]
    exact openRestrictedField_gMat X.manifold (sublevelOpens X.manifold u hu.1 o L)
      (sublevelComponent_isConnected ho) X.metric.form x
  · rw [approximatingMetric_ricci X.metric.form
      (LeafProofs.L12Aux.metricSmooth_of_smoothMetric X.metric) u hu.1 o hL ho x,
      approximatingScalar_levi_zero_on_core u hu.1 o hL ho x hcore, smul_zero, sub_zero]

end Yau.NodeProofs.F01Aux
