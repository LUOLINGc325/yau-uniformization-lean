import Yau.Proofs.V04DataTransport
import Yau.Proofs.V04RadiusSelection

/-! The actual enlarged localization is constructed from a coefficient
already chosen on the original data. -/

open Filter
open scoped Topology
noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n}

theorem exists_localization_enlargement {d : VariationData X q} (hd : VariationSetup d)
    (C : ℕ → ℝ) (hC : ∀ j, 1 ≤ C j) :
    ∃ B : ℕ → ℝ, (∀ j, d.B j ≤ B j) ∧
      VariationSetup {d with B := B} ∧
      (∀ j : ℕ, (j + 1 : ℝ) ≤ B j) ∧
      Tendsto (fun j => Real.log (C j) / B j ^ 2) atTop (𝓝 0) := by
  have hB : ∀ j : ℕ, (j + 1 : ℝ) ≤ d.B j := by
    rcases hd with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, h⟩
    exact fun j => (h j).2.1
  let B := enlargedFiberRadius d.B C
  have henlarge : ∀ j, d.B j ≤ B j := enlargedFiberRadius_ge d.B C hC
  exact ⟨B, henlarge, variationSetup_enlarge_B hd B henlarge,
    fun j => (hB j).trans (henlarge j), enlargedFiberRadius_log_tendsto d.B C hB hC⟩

end Yau.Blueprint.V04Proof
