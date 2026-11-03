import Yau.Proofs.E02SchurContinuity
import Yau.Proofs.E02WeightedForms
import Yau.Proofs.E02CotangentTensor

open Matrix
open scoped Matrix ComplexOrder MatrixOrder
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint

/-- Independent vertical minimizers are substituted into the SAME
shared-base contact inequality. These are complex Schur complements. -/
theorem weighted_schur_order {n m : ℕ}
    (α : Fin m → ℝ)
    (W : Fin m → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (hW : ∀ i, (W i).IsHermitian) (hC : ∀ i, (W i).toBlocks₂₂.PosDef)
    (L : Herm n) (hL : L.IsHermitian)
    (hForms : ∀ (X : ComplexVector n) (V : Fin m → ComplexVector n),
      (star (WithLp.ofLp X) ⬝ᵥ (L*ᵥWithLp.ofLp X)).re ≤
        ∑ i, α i*(star (cotangentVector X (V i)) ⬝ᵥ
          (W i*ᵥcotangentVector X (V i))).re) :
    ((∑ i, (α i : ℂ) • schurComplement (W i))-L).PosSemidef := by
  have hHerm := weighted_sum_isHermitian α (fun i => schurComplement (W i))
    (fun i => schurComplement_isHermitian (W i) (hW i) (hC i))
  apply (hermitian_posSemidef_iff_re_quadratic_nonneg _ (hHerm.sub hL)).mpr
  intro v
  let X : ComplexVector n := WithLp.toLp 2 v
  let V : Fin m → ComplexVector n := fun i =>
    WithLp.toLp 2 (-(((W i).toBlocks₂₂⁻¹*(W i).toBlocks₁₂ᴴ)*ᵥv))
  have hBound := hForms X V
  have hMin (i : Fin m) :
      star (cotangentVector X (V i)) ⬝ᵥ (W i*ᵥcotangentVector X (V i)) =
        star v ⬝ᵥ (schurComplement (W i)*ᵥv) := by
    exact V05Aux.schur_at_minimizer (hW i) (hC i) v
  have hSum : (∑ i, α i*(star (cotangentVector X (V i)) ⬝ᵥ
      (W i*ᵥcotangentVector X (V i))).re) =
      ∑ i, α i*(star v ⬝ᵥ (schurComplement (W i)*ᵥv)).re := by
    apply Finset.sum_congr rfl
    intro i _
    rw [hMin i]
  rw [hSum] at hBound
  change (star v ⬝ᵥ (L*ᵥv)).re ≤ _ at hBound
  rw [Matrix.sub_mulVec,dotProduct_sub,Complex.sub_re,real_quadratic_sum_smul]
  exact sub_nonneg.mpr hBound

/-- The weighted PSD majorants remain PSD and dominate the original
horizontal matrix after the independent Schur minimizations. -/
theorem weighted_schur_majorants {n m : ℕ}
    (α : Fin m → ℝ) (hα : ∀ i, 0 ≤ α i)
    (S K : Fin m → Herm n) (L : Herm n)
    (hK : ∀ i, (K i).PosSemidef) (hDom : ∀ i, (K i-S i).PosSemidef)
    (hOrder : ((∑ i, (α i : ℂ) • S i)-L).PosSemidef) :
    (∑ i, (α i : ℂ) • K i).PosSemidef ∧
      ((∑ i, (α i : ℂ) • K i)-L).PosSemidef := by
  refine ⟨weighted_sum_posSemidef α hα K hK,?_⟩
  have hSum := (weighted_sum_posSemidef α hα (fun i => K i-S i) hDom).add hOrder
  have hEq : (∑ i, (α i : ℂ) • (K i-S i))+((∑ i, (α i : ℂ) • S i)-L) =
      (∑ i, (α i : ℂ) • K i)-L := by
    simp only [smul_sub,Finset.sum_sub_distrib]
    abel
  rwa [hEq] at hSum

end Yau.NodeProofs.E02Aux
