import Yau.Proofs.F04ShiftContinuity
import Yau.Proofs.F04ShiftPositiveBounds

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace ENNReal

noncomputable section

namespace Yau.F04Proof

open Yau.Proofs.F03Aux Yau.LeafProofs.L03 Yau.HeatConcreteBindings

variable {n : ℕ} {M : ComplexManifold n}

theorem continuous_dirichletShiftPosPart_family
    (g : SmoothMetric M) (hK : IsKahler g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (hO : IsOpen O)
    (r : ℝ → M.Carrier → ℝ) (hr : ∀ t, SmoothFn (r t)) (hr0 : ∀ t x, x ∈ O → 0 ≤ r t x)
    (hr2 : ∀ t, ScalarL2 (μ.restrict O) (r t))
    (hdr2 : ∀ t, L2RealForm g.form (μ.restrict O) (scalarExterior (r t)))
    (hRH : Continuous (fun t => scalarToLp (hr2 t)))
    (hRD : Continuous (fun t => realizeL2Form g (μ.restrict O)
      (L2FormSpace.ofSection (scalarExterior (r t)) (hdr2 t)))) :
    Continuous (fun p : ℝ × DirichletEnergy g μ hμ O =>
      dirichletShiftPosPart g μ hμ O hO (r p.1) (hr p.1) (hr0 p.1) (hr2 p.1) (hdr2 p.1) p.2) := by
  apply continuous_iff_seqContinuous.mpr
  intro seq p hp
  have ht : Tendsto (fun j => (seq j).1) atTop (𝓝 p.1) := (continuous_fst.tendsto p).comp hp
  have hv : Tendsto (fun j => (seq j).2) atTop (𝓝 p.2) := (continuous_snd.tendsto p).comp hp
  exact dirichletShiftPosPart_tendsto g hK μ hμ O hO
    (fun j => r (seq j).1) (fun j => hr (seq j).1) (fun j => hr0 (seq j).1)
    (fun j => hr2 (seq j).1) (fun j => hdr2 (seq j).1)
    (r p.1) (hr p.1) (hr0 p.1) (hr2 p.1) (hdr2 p.1)
    (fun j => (seq j).2) p.2 hv (hRH.continuousAt.tendsto.comp ht)
    (hRD.continuousAt.tendsto.comp ht)

/-- A time-dependent smooth shift preserves genuine Bochner L2 membership;
the inhomogeneous term is its actual differential profile. -/
theorem dirichletShiftPosPart_family_memLp
    (g : SmoothMetric M) (hK : IsKahler g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (hO : IsOpen O)
    (r : ℝ → M.Carrier → ℝ) (hr : ∀ t, SmoothFn (r t)) (hr0 : ∀ t x, x ∈ O → 0 ≤ r t x)
    (hr2 : ∀ t, ScalarL2 (μ.restrict O) (r t))
    (hdr2 : ∀ t, L2RealForm g.form (μ.restrict O) (scalarExterior (r t)))
    (hRH : Continuous (fun t => scalarToLp (hr2 t)))
    (hRD : Continuous (fun t => realizeL2Form g (μ.restrict O)
      (L2FormSpace.ofSection (scalarExterior (r t)) (hdr2 t))))
    (τ : Measure ℝ) (U : ℝ → DirichletEnergy g μ hμ O) (hU : MemLp U 2 τ)
    (hDr : MemLp (fun t => realizeL2Form g (μ.restrict O)
      (L2FormSpace.ofSection (scalarExterior (r t)) (hdr2 t))) 2 τ) :
    MemLp (fun t => dirichletShiftPosPart g μ hμ O hO (r t) (hr t) (hr0 t) (hr2 t) (hdr2 t) (U t)) 2 τ := by
  let Φ : ℝ × DirichletEnergy g μ hμ O → DirichletEnergy g μ hμ O := fun p =>
    dirichletShiftPosPart g μ hμ O hO (r p.1) (hr p.1) (hr0 p.1) (hr2 p.1) (hdr2 p.1) p.2
  have hΦ : Continuous Φ :=
    continuous_dirichletShiftPosPart_family g hK μ hμ O hO r hr hr0 hr2 hdr2 hRH hRD
  have hpair : AEStronglyMeasurable (fun t : ℝ => (t, U t)) τ :=
    (aestronglyMeasurable_id : AEStronglyMeasurable (fun t : ℝ => t) τ).prodMk hU.aestronglyMeasurable
  have hcomp : AEStronglyMeasurable (Φ ∘ fun t : ℝ => (t, U t)) τ := hΦ.comp_aestronglyMeasurable hpair
  have hm : AEStronglyMeasurable
      (fun t => dirichletShiftPosPart g μ hμ O hO (r t) (hr t) (hr0 t) (hr2 t) (hdr2 t) (U t)) τ := by
    simpa only [Function.comp_def, Φ] using hcomp
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  have hu := (memLp_two_iff_integrable_sq_norm hU.aestronglyMeasurable).mp hU
  have hd := (memLp_two_iff_integrable_sq_norm hDr.aestronglyMeasurable).mp hDr
  apply ((hu.const_mul 2).add hd).mono_nonneg (hm.norm.pow 2)
    (ae_of_all τ fun t => sq_nonneg _)
  exact ae_of_all τ fun t => dirichletShiftPosPart_norm_sq_le g μ hμ O hO
    (r t) (hr t) (hr0 t) (hr2 t) (hdr2 t) (U t)

end Yau.F04Proof
