import Yau.Proofs.F04ShiftJointContinuity
import Yau.Proofs.F04BochnerGrowth

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace ENNReal

noncomputable section

namespace Yau.F04Proof

open Yau.Proofs.F03Aux Yau.LeafProofs.L03 Yau.HeatConcreteBindings

variable {n : ℕ} {M : ComplexManifold n}

/-- The genuine supported shift is strongly continuous on Bochner L2 curves
for the finite physical time measure. -/
theorem dirichlet_shift_posPart_strongL2_family
    (g : SmoothMetric M) (hK : IsKahler g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (hO : IsOpen O)
    (r : ℝ → M.Carrier → ℝ) (hr : ∀ t, SmoothFn (r t)) (hr0 : ∀ t x, x ∈ O → 0 ≤ r t x)
    (hr2 : ∀ t, ScalarL2 (μ.restrict O) (r t))
    (hdr2 : ∀ t, L2RealForm g.form (μ.restrict O) (scalarExterior (r t)))
    (hRH : Continuous (fun t => scalarToLp (hr2 t)))
    (hRD : Continuous (fun t => realizeL2Form g (μ.restrict O)
      (L2FormSpace.ofSection (scalarExterior (r t)) (hdr2 t))))
    (τ : Measure ℝ) [IsFiniteMeasure τ]
    (hDr : MemLp (fun t => realizeL2Form g (μ.restrict O)
      (L2FormSpace.ofSection (scalarExterior (r t)) (hdr2 t))) 2 τ)
    (U : ℕ → ℝ → DirichletEnergy g μ hμ O) (u : ℝ → DirichletEnergy g μ hμ O)
    (hU : ∀ j, MemLp (U j) 2 τ) (hu : MemLp u 2 τ)
    (hlim : Tendsto (fun j => ∫ t, ‖U j t - u t‖ ^ 2 ∂τ) atTop (𝓝 0)) :
    Tendsto (fun j => ∫ t,
      ‖dirichletShiftPosPart g μ hμ O hO (r t) (hr t) (hr0 t) (hr2 t) (hdr2 t) (U j t) -
        dirichletShiftPosPart g μ hμ O hO (r t) (hr t) (hr0 t) (hr2 t) (hdr2 t) (u t)‖ ^ 2 ∂τ)
      atTop (𝓝 0) := by
  apply continuous_growth_comp_L2 τ
    (fun p : ℝ × DirichletEnergy g μ hμ O =>
      dirichletShiftPosPart g μ hμ O hO (r p.1) (hr p.1) (hr0 p.1) (hr2 p.1) (hdr2 p.1) p.2)
    (continuous_dirichletShiftPosPart_family g hK μ hμ O hO r hr hr0 hr2 hdr2 hRH hRD)
    2 (by norm_num)
    (fun t => ‖realizeL2Form g (μ.restrict O) (L2FormSpace.ofSection (scalarExterior (r t)) (hdr2 t))‖)
    hDr.norm _ U u hU hu hlim
  intro t v
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  calc
    _ ≤ 2 * ‖v‖ ^ 2 +
        ‖realizeL2Form g (μ.restrict O) (L2FormSpace.ofSection (scalarExterior (r t)) (hdr2 t))‖ ^ 2 :=
      dirichletShiftPosPart_norm_sq_le g μ hμ O hO (r t) (hr t) (hr0 t) (hr2 t) (hdr2 t) v
    _ ≤ _ := by
      nlinarith [sq_nonneg ‖v‖, mul_nonneg (norm_nonneg v)
        (norm_nonneg (realizeL2Form g (μ.restrict O) (L2FormSpace.ofSection (scalarExterior (r t)) (hdr2 t))))]

end Yau.F04Proof
