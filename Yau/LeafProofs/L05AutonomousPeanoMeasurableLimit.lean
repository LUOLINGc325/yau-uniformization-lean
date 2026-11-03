import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.Topology.Separation.Hausdorff

noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace Yau.LeafProofs.L05AutonomousAux

/-- The actual finite limit of a real sequence, with explicit zero value when
the sequence does not converge in the real line. -/
def peanoRealSequenceLimit (a : ℕ → ℝ) : ℝ := by
  classical
  exact if ∃ c : ℝ, Tendsto a atTop (𝓝 c) then limUnder atTop a else 0

theorem peanoRealSequenceLimit_eq {a : ℕ → ℝ} {c : ℝ}
    (ha : Tendsto a atTop (𝓝 c)) : peanoRealSequenceLimit a = c := by
  rw [peanoRealSequenceLimit,ite_eq_left ⟨c,ha⟩,ha.limUnder_eq]

theorem peanoRealSequenceLimit_zero {a : ℕ → ℝ}
    (ha : ¬ ∃ c : ℝ, Tendsto a atTop (𝓝 c)) : peanoRealSequenceLimit a = 0 := by
  simp only [peanoRealSequenceLimit,ite_eq_right ha]

/-- The convergence set is measurable before any limit is selected. -/
theorem peanoRealSequenceLimit_convergence_measurable {X : Type*} [MeasurableSpace X]
    {f : ℕ → X → ℝ} (hf : ∀ j, Measurable (f j)) :
    MeasurableSet {x | ∃ c : ℝ, Tendsto (fun j => f j x) atTop (𝓝 c)} :=
  MeasureTheory.measurableSet_exists_tendsto hf

/-- The concrete finite-limit/default construction is measurable. -/
theorem measurable_peanoRealSequenceLimit {X : Type*} [MeasurableSpace X]
    {f : ℕ → X → ℝ} (hf : ∀ j, Measurable (f j)) :
    Measurable (fun x => peanoRealSequenceLimit (fun j => f j x)) := by
  classical
  let D : Set X := {x | ∃ c : ℝ, Tendsto (fun j => f j x) atTop (𝓝 c)}
  have hD : MeasurableSet D := peanoRealSequenceLimit_convergence_measurable hf
  have hL : StronglyMeasurable (fun x => limUnder atTop (fun j => f j x)) :=
    StronglyMeasurable.limUnder (fun j => (hf j).stronglyMeasurable)
  have hI := (hL.indicator hD).measurable
  have hEq : (fun x => peanoRealSequenceLimit (fun j => f j x)) =
      D.indicator (fun x => limUnder atTop (fun j => f j x)) := by
    funext x
    by_cases hx : x ∈ D
    · have hx' : ∃ c : ℝ, Tendsto (fun j => f j x) atTop (𝓝 c) := hx
      rw [Set.indicator_of_mem hx,peanoRealSequenceLimit,ite_eq_left hx']
    · have hx' : ¬ ∃ c : ℝ, Tendsto (fun j => f j x) atTop (𝓝 c) := hx
      rw [Set.indicator_of_notMem hx,peanoRealSequenceLimit,ite_eq_right hx']
  rw [hEq]
  exact hI

end Yau.LeafProofs.L05AutonomousAux
