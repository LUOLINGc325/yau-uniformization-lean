import Yau.Proofs.C04Clock
import Yau.Proofs.Y03Clock

/-! The same physical-time clock, with its inverse on a sufficiently late ray. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory Filter

namespace Yau.Proofs.C04Aux
open Yau Blueprint

variable {n : ℕ}

/-- Strictness holds on the entire nonnegative ray, so late clock levels
have no additional early physical-time preimages. -/
theorem rho_strictMonoOn_nonneg (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ)
    (hH : HarnackCompleteness X o h) :
    StrictMonoOn (ρ o) (Set.Ici 0) := by
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Ici (0 : ℝ))
  · exact (timeSlice_contDiffOn hf.2.2.2.1 o).continuousOn
  · intro t ht
    rw [interior_Ici] at ht
    exact (rho_hasDerivAt X o h U P ρ hf o ht).hasDerivWithinAt
  · intro t ht
    exact scalar_pos X o h hH (interior_subset ht) o

theorem clock_inverse (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ)
    (hH : HarnackCompleteness X o h) :
    ∃ A : ℝ, 1 ≤ A ∧ 1 ≤ ρ o A ∧ ∃ time : ℝ → ℝ,
      (∀ s, ρ o A ≤ s → A ≤ time s ∧ ρ o (time s) = s) ∧
      (∀ t, A ≤ t → time (ρ o t) = t) ∧
      StrictMonoOn time (Set.Ici (ρ o A)) ∧ Tendsto time atTop atTop := by
  obtain ⟨B, hB⟩ := (tendsto_atTop_atTop.1 (rho_tendsto_atTop X o h U P ρ hf hH)) 1
  let A := max 1 B
  have hA : 1 ≤ A := le_max_left _ _
  refine ⟨A, hA, hB A (le_max_right _ _), ?_⟩
  apply Blueprint.Alignment.Y03Proof.inverse_on_ray
    (rho_strictMonoOn X o h U P ρ hf hH (zero_lt_one.trans_le hA))
  · exact (timeSlice_contDiffOn hf.2.2.2.1 o).continuousOn.mono
      (fun t ht => zero_le_one.trans (hA.trans ht))
  · exact rho_tendsto_atTop X o h U P ρ hf hH

end Yau.Proofs.C04Aux
