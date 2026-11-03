import Yau.Geometry.Basic
import Mathlib.Topology.MetricSpace.HausdorffDimension

open scoped Topology ENNReal
open Set MeasureTheory

noncomputable section

namespace Yau.NodeProofs.P03Aux

/-- The actual native dimension theorem supplies density outside a
differentiable parameter chart of strictly smaller real dimension. -/
theorem dense_compl_lower_dimensional_image {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} {f : E → F} (hf : DifferentiableOn ℝ f s)
    (hd : Module.finrank ℝ E < Module.finrank ℝ F) : Dense (f '' s)ᶜ := by
  apply hf.dense_compl_image_of_dimH_lt_finrank
  calc
    dimH s ≤ dimH (univ : Set E) := dimH_mono (subset_univ _)
    _ = Module.finrank ℝ E := Real.dimH_univ_eq_finrank E
    _ < Module.finrank ℝ F := by exact_mod_cast hd

/-- A finite collection of genuine lower-dimensional differentiable
charts still leaves a dense complement in parameter space. -/
theorem dense_compl_finite_lower_dimensional_images {ι : Type*} [Fintype ι]
    (E : ι → Type*) [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    [∀ i, FiniteDimensional ℝ (E i)] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (s : ∀ i, Set (E i)) (f : ∀ i, E i → F)
    (hf : ∀ i, DifferentiableOn ℝ (f i) (s i))
    (hd : ∀ i, Module.finrank ℝ (E i) < Module.finrank ℝ F) :
    Dense (⋃ i, f i '' s i)ᶜ := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl hi => simp
  | inr hi =>
    have hpos : 0 < Module.finrank ℝ F := (Nat.zero_le _).trans_lt (hd (Classical.arbitrary ι))
    apply dense_compl_of_dimH_lt_finrank
    calc
      dimH (⋃ i, f i '' s i) = ⨆ i, dimH (f i '' s i) := dimH_iUnion _
      _ ≤ (Module.finrank ℝ F - 1 : ℕ) := by
        apply iSup_le
        intro i
        calc
          _ ≤ dimH (s i) := (hf i).dimH_image_le
          _ ≤ dimH (univ : Set (E i)) := dimH_mono (subset_univ _)
          _ = Module.finrank ℝ (E i) := Real.dimH_univ_eq_finrank (E i)
          _ ≤ (Module.finrank ℝ F - 1 : ℕ) := by
            have hdi := hd i
            exact_mod_cast (show Module.finrank ℝ (E i) ≤ Module.finrank ℝ F - 1 by omega)
      _ < Module.finrank ℝ F := by exact_mod_cast (show Module.finrank ℝ F - 1 < Module.finrank ℝ F by omega)

end Yau.NodeProofs.P03Aux
