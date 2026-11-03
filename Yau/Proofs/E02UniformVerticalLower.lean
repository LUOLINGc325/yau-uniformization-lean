import Yau.Proofs.E02ColumnLowerContinuity
import Yau.Proofs.E02MatrixLowerLimit

open Matrix Filter
open scoped Topology Matrix ComplexOrder Matrix.Norms.Elementwise
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem columnLowerMatrix_contact_lower {n m : ℕ} (α : Fin m → ℝ) (θ w : ℝ)
    (η : Fin m → ComplexVector n) (B : Herm n) (hB : B.PosDef)
    (hGram : weightedColumns α η*(weightedColumns α η)ᴴ = B⁻¹)
    (hq : ∀ j, qform B (η j) = 1) (hθ : θ ≤ 1) (hα : ∀ j, α j ≤ w) (j : Fin m) :
    (columnLowerMatrix α θ η j-(((1-θ)*(1-w) : ℝ) : ℂ) • B).PosSemidef := by
  rw [columnLowerMatrix_at_contact α θ η B hB hGram j (hq j)]
  have hCoef : 0 ≤ (1-θ)*(w-α j) := mul_nonneg (sub_nonneg.mpr hθ) (sub_nonneg.mpr (hα j))
  have hp : ((((1-θ)*(w-α j) : ℝ) : ℂ) • B).PosSemidef :=
    hB.posSemidef.smul (RCLike.ofReal_nonneg.mpr hCoef)
  convert hp using 1
  push_cast
  module

/-- One fixed contact list and its actual limiting Gram/contact data
give the simultaneous vertical coefficient bound. The matrix size and
original B stay fixed throughout this limit. -/
theorem eventually_columnLowerMatrix_lower {ι : Type*} {l : Filter ι} {n m : ℕ}
    (α : Fin m → ℝ) (θ w : ℝ) (η : ι → Fin m → ComplexVector n)
    (η₀ : Fin m → ComplexVector n) (B : Herm n) (hB : B.PosDef)
    (hlim : Tendsto η l (𝓝 η₀))
    (hGram : weightedColumns α η₀*(weightedColumns α η₀)ᴴ = B⁻¹)
    (hq : ∀ j, qform B (η₀ j) = 1) (hθ : θ ≤ 1) (hα : ∀ j, α j ≤ w)
    {r : ℝ} (hr : 0 < r) :
    ∀ᶠ i in l, ∀ j, (columnLowerMatrix α θ (η i) j-
      ((((1-θ)*(1-w)-r : ℝ) : ℂ) • B)).PosSemidef := by
  have hM : (weightedColumns α η₀*(weightedColumns α η₀)ᴴ).PosDef := by
    rw [hGram]
    exact hB.inv
  have hColumns : Tendsto (fun i => weightedColumns α (η i)) l (𝓝 (weightedColumns α η₀)) :=
    (((weightedColumnsCLM α).restrictScalars ℝ).continuous.continuousAt.tendsto).comp hlim
  have hRank := hColumns.eventually ((isOpen_fullRankRect n m).mem_nhds
    ((fullRankRect_iff_posDef _).mpr hM))
  have hHerm : ∀ j, ∀ᶠ i in l, (columnLowerMatrix α θ (η i) j).IsHermitian := by
    intro j
    filter_upwards [hRank] with i hi
    exact columnLowerMatrix_isHermitian α θ (η i) ((fullRankRect_iff_posDef _).mp hi) j
  have hLower : ∀ j, (columnLowerMatrix α θ η₀ j-
      (((1-θ)*(1-w) : ℝ) : ℂ) • B).PosSemidef :=
    columnLowerMatrix_contact_lower α θ w η₀ B hB hGram hq hθ hα
  have hLimits : ∀ j, Tendsto (fun i => columnLowerMatrix α θ (η i) j) l
      (𝓝 (columnLowerMatrix α θ η₀ j)) := fun j =>
    (columnLowerMatrix_continuousAt α θ η₀ hM j).tendsto.comp hlim
  exact eventually_finite_matrix_lower (fun j i => columnLowerMatrix α θ (η i) j)
    (fun j => columnLowerMatrix α θ η₀ j) B hB ((1-θ)*(1-w)) hLower hHerm hLimits hr

end Yau.NodeProofs.E02Aux
