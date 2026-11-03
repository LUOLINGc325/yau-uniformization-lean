import Yau.Proofs.F04ShiftPositiveDifferential

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace

noncomputable section

namespace Yau.F04Proof

open Yau.Proofs.F03Aux Yau.LeafProofs.L03 Yau.HeatConcreteBindings

variable {n : ℕ} {M : ComplexManifold n}

theorem dirichletShiftPosPart_L2_norm_le
    (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (hO : IsOpen O)
    (r : M.Carrier → ℝ) (hr : SmoothFn r) (hr0 : ∀ x ∈ O, 0 ≤ r x)
    (hr2 : ScalarL2 (μ.restrict O) r)
    (hdr2 : L2RealForm g.form (μ.restrict O) (scalarExterior r))
    (u : DirichletEnergy g μ hμ O) :
    ‖dirichletL2 g μ hμ O (dirichletShiftPosPart g μ hμ O hO r hr hr0 hr2 hdr2 u)‖ ≤
      ‖dirichletL2 g μ hμ O u‖ := by
  rw [(dirichletShiftPosPart_spec g μ hμ O hO r hr hr0 hr2 hdr2 u).1]
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [Lp.coeFn_posPart (dirichletL2 g μ hμ O u - scalarToLp hr2),
    Lp.coeFn_sub (dirichletL2 g μ hμ O u) (scalarToLp hr2), scalarToLp_coe hr2,
    ae_restrict_mem hO.measurableSet] with x hp hs hrx hx
  rw [hp, hs]
  simp only [Pi.sub_apply, hrx, Real.norm_eq_abs]
  rw [abs_of_nonneg (le_max_right _ _)]
  exact max_le ((sub_le_self _ (hr0 x hx)).trans (le_abs_self _)) (abs_nonneg _)

theorem dirichletShiftPosPart_D_norm_le
    (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (hO : IsOpen O)
    (r : M.Carrier → ℝ) (hr : SmoothFn r) (hr0 : ∀ x ∈ O, 0 ≤ r x)
    (hr2 : ScalarL2 (μ.restrict O) r)
    (hdr2 : L2RealForm g.form (μ.restrict O) (scalarExterior r))
    (u : DirichletEnergy g μ hμ O) :
    ‖dirichletD g μ hμ O (dirichletShiftPosPart g μ hμ O hO r hr hr0 hr2 hdr2 u)‖ ≤
      ‖dirichletD g μ hμ O u‖ +
        ‖realizeL2Form g (μ.restrict O) (L2FormSpace.ofSection (scalarExterior r) hdr2)‖ := by
  rw [(dirichletShiftPosPart_spec g μ hμ O hO r hr hr0 hr2 hdr2 u).2]
  exact (show ‖positiveFormMultiplier g (μ.restrict O)
      (dirichletL2 g μ hμ O u - scalarToLp hr2)
      (dirichletD g μ hμ O u -
        realizeL2Form g (μ.restrict O) (L2FormSpace.ofSection (scalarExterior r) hdr2))‖ ≤
      ‖dirichletD g μ hμ O u -
        realizeL2Form g (μ.restrict O) (L2FormSpace.ofSection (scalarExterior r) hdr2)‖ by
    simpa only [positiveFormMultiplier, one_mul] using
      multiplyL2FormHilbert_norm_le g (μ.restrict O) _ _ 1 zero_le_one _ _).trans
      (norm_sub_le _ _)

/-- Actual energy growth of the shifted lift; the inhomogeneous term is the
norm of the actual smooth differential, not a presumed H10 norm of r. -/
theorem dirichletShiftPosPart_norm_sq_le
    (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (hO : IsOpen O)
    (r : M.Carrier → ℝ) (hr : SmoothFn r) (hr0 : ∀ x ∈ O, 0 ≤ r x)
    (hr2 : ScalarL2 (μ.restrict O) r)
    (hdr2 : L2RealForm g.form (μ.restrict O) (scalarExterior r))
    (u : DirichletEnergy g μ hμ O) :
    ‖dirichletShiftPosPart g μ hμ O hO r hr hr0 hr2 hdr2 u‖ ^ 2 ≤
      2 * ‖u‖ ^ 2 +
        ‖realizeL2Form g (μ.restrict O) (L2FormSpace.ofSection (scalarExterior r) hdr2)‖ ^ 2 := by
  let v := dirichletShiftPosPart g μ hμ O hO r hr hr0 hr2 hdr2 u
  let a := ‖dirichletD g μ hμ O u‖
  let b := ‖realizeL2Form g (μ.restrict O) (L2FormSpace.ofSection (scalarExterior r) hdr2)‖
  have hJ := dirichletShiftPosPart_L2_norm_le g μ hμ O hO r hr hr0 hr2 hdr2 u
  have hD := dirichletShiftPosPart_D_norm_le g μ hμ O hO r hr hr0 hr2 hdr2 u
  have hJs := pow_le_pow_left₀ (norm_nonneg _) hJ 2
  have hDs := pow_le_pow_left₀ (norm_nonneg _) hD 2
  have hv := dirichletEnergy_norm_sq g μ hμ O v
  have hu := dirichletEnergy_norm_sq g μ hμ O u
  nlinarith [sq_nonneg (a - b), sq_nonneg ‖dirichletL2 g μ hμ O u‖]

end Yau.F04Proof
