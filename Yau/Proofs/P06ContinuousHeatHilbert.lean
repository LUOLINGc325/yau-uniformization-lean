import Yau.Proofs.P06ContinuousHeatRepresentation
import Yau.Proofs.P06ScalarUniqueness
import Yau.Proofs.P06TraceHilbertScalarHeat

noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace

namespace Yau.NodeProofs.P06Aux
open Yau Yau.Blueprint Yau.LeafProofs.L03
open Yau.LeafProofs.L19Aux Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

/-- Every solution in the original PDE class has that same normalized
representation; no global L² condition is imposed on the solution. -/
theorem continuousInitialHeat_normalized_representation (X : KahlerManifold n)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (f : Pt X → ℝ) (c : ℝ) (hcont : Continuous (fun x => f x - c))
    (hcompact : HasCompactSupport (fun x => f x - c))
    (u : ℝ → Pt X → ℝ) (hu : IsContinuousInitialScalarHeat X.metric.form f u) :
    ∃ hf0 : MemLp (fun x => f x - c) 2 μ, ∀ t, 0 < t →
      (fun x => u t x - c) =ᵐ[μ]
        scalarHeatFamily X.metric μ hμ t (hf0.toLp (fun x => f x - c)) := by
  obtain ⟨v, hv, hf0, hrep⟩ := continuousInitialHeat_exists_representation
    (complexDimension_pos X.manifold) X.metric X.kahler_metric μ hμ f c hcont hcompact
  refine ⟨hf0, ?_⟩
  intro t ht
  rw [continuousInitialScalarHeat_unique X f u v hu hv t ht]
  exact hrep t ht


theorem scalarHeat_ae_hilbert_realization (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (hk : IsKahler g)
    (f : M.Carrier → ℝ) (hf : MemLp f 2 μ)
    (hFL : L2RealForm g.form μ (G04Aux.scalarForm f)) (u : M.Carrier → ℝ)
    (t : ℝ) (ht : 0 ≤ t)
    (hae : u =ᵐ[μ] Yau.LeafProofs.L19Aux.scalarHeatFamily g μ hμ t (hf.toLp f)) :
    ∃ hUL : L2RealForm g.form μ (G04Aux.scalarForm u),
      realizeActualForm g μ (G04Aux.scalarForm u) hUL =
        hodgeHeatHilbert g μ hμ 0 t (realizeActualForm g μ (G04Aux.scalarForm f) hFL) := by
  let fL := hf.toLp f
  let q := Yau.LeafProofs.L19Aux.scalarHeatFamily g μ hμ t fL
  have hforms : ∀ᵐ x ∂μ, G04Aux.scalarForm q x = G04Aux.scalarForm u x := by
    filter_upwards [hae] with x hx
    ext V
    exact hx.symm
  let hUL := l2RealForm_of_ae_eq g.form hforms (TraceHilbert.scalar_l2 g μ q)
  refine ⟨hUL, ?_⟩
  calc
    _ = TraceHilbert.scalarLift g μ q :=
      (TraceHilbert.scalarLift_realize g μ q u hUL hae.symm).symm
    _ = hodgeHeatHilbert g μ hμ 0 t (TraceHilbert.scalarLift g μ fL) :=
      TraceHilbert.scalarHeat_eq_hodgeHeat g μ hμ hk fL t ht
    _ = _ := congrArg (hodgeHeatHilbert g μ hμ 0 t)
      (TraceHilbert.scalarLift_realize g μ fL f hFL hf.coeFn_toLp)

/-- The original bounded PDE solution becomes a genuine degree-zero L²
heat representative after subtracting its constant value at infinity. -/
theorem continuousInitialHeat_normalized_hilbert (X : KahlerManifold n)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (f : Pt X → ℝ) (c : ℝ) (hcont : Continuous (fun x => f x - c))
    (hc : HasCompactSupport (fun x => f x - c))
    (u : ℝ → Pt X → ℝ) (hu : IsContinuousInitialScalarHeat X.metric.form f u)
    (t : ℝ) (ht : 0 < t) :
    ∃ hUL : L2RealForm X.metric.form μ (G04Aux.scalarForm (fun x => u t x - c)),
      ∃ hFL : L2RealForm X.metric.form μ (G04Aux.scalarForm (fun x => f x - c)),
      realizeActualForm X.metric μ (G04Aux.scalarForm (fun x => u t x - c)) hUL =
        hodgeHeatHilbert X.metric μ hμ 0 t
          (realizeActualForm X.metric μ (G04Aux.scalarForm (fun x => f x - c)) hFL) := by
  obtain ⟨hf, hrep⟩ := continuousInitialHeat_normalized_representation X μ hμ f c hcont hc u hu
  let fL := hf.toLp (fun x => f x - c)
  have hae : ∀ᵐ x ∂μ, G04Aux.scalarForm fL x = G04Aux.scalarForm (fun y => f y - c) x := by
    filter_upwards [hf.coeFn_toLp] with x hx
    ext V
    exact hx
  let hFL := l2RealForm_of_ae_eq X.metric.form hae (TraceHilbert.scalar_l2 X.metric μ fL)
  obtain ⟨hUL, he⟩ := scalarHeat_ae_hilbert_realization X.metric μ hμ X.kahler_metric
    (fun x => f x - c) hf hFL (fun x => u t x - c) t ht.le (hrep t ht)
  exact ⟨hUL, hFL, he⟩

end Yau.NodeProofs.P06Aux
