import Yau.Proofs.F04ShiftCoreBindings

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace

noncomputable section

namespace Yau.F04Proof

open Yau.Proofs.F03Aux Yau.LeafProofs.L03 Yau.HeatConcreteBindings

variable {n : ℕ} {M : ComplexManifold n}

/-- The supported shifted smooth graph is constructed from actual repaired
core tests. The smooth shift need not have zero boundary trace. -/
theorem dirichlet_shift_smoothing_graph
    (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (hO : IsOpen O)
    (δ : ℝ) (hδ : 0 < δ) (r : M.Carrier → ℝ) (hr : SmoothFn r)
    (hr0 : ∀ x ∈ O, 0 ≤ r x) (hr2 : ScalarL2 (μ.restrict O) r)
    (hdr2 : L2RealForm g.form (μ.restrict O) (scalarExterior r))
    (u : DirichletEnergy g μ hμ O) :
    ∃ v : DirichletEnergy g μ hμ O,
      dirichletL2 g μ hμ O v = smoothPositiveL2 (μ.restrict O) δ
        (dirichletL2 g μ hμ O u - scalarToLp hr2) ∧
      dirichletD g μ hμ O v =
        continuousFormMultiplier g (μ.restrict O) (deriv (smoothPositive δ))
          (contDiff_infty_iff_deriv.mp (smoothPositive_contDiff δ)).2.continuous
          1 zero_le_one (smoothPositive_deriv_abs_le δ)
          (dirichletL2 g μ hμ O u - scalarToLp hr2)
          (dirichletD g μ hμ O u -
            realizeL2Form g (μ.restrict O) (L2FormSpace.ofSection (scalarExterior r) hdr2)) := by
  obtain ⟨fs, hfs⟩ := exists_dirichletCore_tendsto g μ hμ O u
  have hcore (j : ℕ) := exists_shift_smoothing_core g μ hμ O hO δ hδ r hr hr0 (fs j)
  choose qs hqv hqd using hcore
  let rH := scalarToLp hr2
  let rD := realizeL2Form g (μ.restrict O) (L2FormSpace.ofSection (scalarExterior r) hdr2)
  have hJ : Tendsto
      (fun j => dirichletL2 g μ hμ O (dirichletCoreToEnergy g μ hμ O (fs j)) - rH)
      atTop (𝓝 (dirichletL2 g μ hμ O u - rH)) := by
    simpa only [Function.comp_def] using
      (((dirichletL2 g μ hμ O).continuous.tendsto u).comp hfs).sub
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => rH) atTop (𝓝 rH))
  have hD : Tendsto
      (fun j => dirichletD g μ hμ O (dirichletCoreToEnergy g μ hμ O (fs j)) - rD)
      atTop (𝓝 (dirichletD g μ hμ O u - rD)) := by
    simpa only [Function.comp_def] using
      (((dirichletD g μ hμ O).continuous.tendsto u).comp hfs).sub
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => rD) atTop (𝓝 rD))
  have hJq (j : ℕ) := shiftSmoothingCore_L2 g μ hμ O hO.measurableSet δ r hr2 (fs j) (qs j) (hqv j)
  have hDq (j : ℕ) := shiftSmoothingCore_D g μ hμ O hO.measurableSet δ r hr2 hdr2 (fs j) (qs j) (hqd j)
  have hJlim : Tendsto (fun j => dirichletL2 g μ hμ O (dirichletCoreToEnergy g μ hμ O (qs j)))
      atTop (𝓝 (smoothPositiveL2 (μ.restrict O) δ (dirichletL2 g μ hμ O u - rH))) := by
    simpa only [hJq, rH, smoothPositiveL2, Function.comp_def] using
      ((smoothPositive_lipschitz δ).continuous_compLp (smoothPositive_zero δ)
        |>.tendsto (dirichletL2 g μ hμ O u - rH) |>.comp hJ)
  have hDlim : Tendsto (fun j => dirichletD g μ hμ O (dirichletCoreToEnergy g μ hμ O (qs j)))
      atTop (𝓝 (continuousFormMultiplier g (μ.restrict O) (deriv (smoothPositive δ))
        (contDiff_infty_iff_deriv.mp (smoothPositive_contDiff δ)).2.continuous
        1 zero_le_one (smoothPositive_deriv_abs_le δ)
        (dirichletL2 g μ hμ O u - rH) (dirichletD g μ hμ O u - rD))) := by
    simpa only [hDq, rH, rD] using
      continuousFormMultiplier_tendsto g (μ.restrict O) (deriv (smoothPositive δ))
        (contDiff_infty_iff_deriv.mp (smoothPositive_contDiff δ)).2.continuous
        1 zero_le_one (smoothPositive_deriv_abs_le δ) _ _ hJ _ _ hD
  have hm := (dirichletGraphMap_isClosed_range g μ hμ O).mem_of_tendsto
    (hJlim.prodMk_nhds hDlim) (Eventually.of_forall fun j =>
      show (dirichletL2 g μ hμ O (dirichletCoreToEnergy g μ hμ O (qs j)),
        dirichletD g μ hμ O (dirichletCoreToEnergy g μ hμ O (qs j))) ∈
        range (dirichletGraphMap g μ hμ O) from ⟨dirichletCoreToEnergy g μ hμ O (qs j), rfl⟩)
  obtain ⟨v, hv⟩ := hm
  exact ⟨v, congrArg Prod.fst hv, congrArg Prod.snd hv⟩

end Yau.F04Proof
