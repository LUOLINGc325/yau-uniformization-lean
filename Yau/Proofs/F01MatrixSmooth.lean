import spec.CHAIN.CONTRACTS

/-! Entrywise smoothness gives smoothness into the actual Frobenius-normed
matrix space via the genuine finite-dimensional identity linear map. -/
open Set
open scoped ContDiff Matrix.Norms.Frobenius
noncomputable section
namespace Yau.NodeProofs.F01Aux
variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]

theorem matrix_contDiffOn_of_entries {U : Set E} {G : E → Matrix ι ι ℂ}
    (hG : ∀ i j, ContDiffOn ℝ ∞ (fun x => G x i j) U) : ContDiffOn ℝ ∞ G U := by
  let L : (ι → ι → ℂ) →ₗ[ℝ] Matrix ι ι ℂ :=
    { toFun := Matrix.of
      map_add' := by intro A B; rfl
      map_smul' := by intro r A; rfl }
  let T : (ι → ι → ℂ) →L[ℝ] Matrix ι ι ℂ :=
    LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := ι → ι → ℂ) (F' := Matrix ι ι ℂ) L
  have hp : ContDiffOn ℝ ∞ (fun x : E => fun i j : ι => G x i j) U :=
    contDiffOn_pi.mpr (fun i => contDiffOn_pi.mpr (hG i))
  convert! T.contDiff.comp_contDiffOn hp using 1

end Yau.NodeProofs.F01Aux
