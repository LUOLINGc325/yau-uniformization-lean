import Yau.Proofs.E02GramSmooth
import Yau.Proofs.E02ProductMaps
import Yau.Proofs.E02ProjectorWirtinger

open Matrix Set Filter
open scoped Topology ContDiff Matrix ComplexOrder Matrix.Norms.Elementwise
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def columnLowerMatrix {n m : ℕ} (α : Fin m → ℝ) (θ : ℝ)
    (η : Fin m → ComplexVector n) (j : Fin m) : Herm n :=
  (((1-θ)*(1-α j*qform ((weightedColumns α η*(weightedColumns α η)ᴴ)⁻¹) (η j)) : ℝ) : ℂ) •
    (weightedColumns α η*(weightedColumns α η)ᴴ)⁻¹

theorem columnLowerMatrix_isHermitian {n m : ℕ} (α : Fin m → ℝ) (θ : ℝ)
    (η : Fin m → ComplexVector n) (hM : (weightedColumns α η*(weightedColumns α η)ᴴ).PosDef)
    (j : Fin m) : (columnLowerMatrix α θ η j).IsHermitian := by
  apply hM.inv.isHermitian.smul
  simp [isSelfAdjoint_iff]

theorem columnLowerMatrix_continuousAt {n m : ℕ} (α : Fin m → ℝ) (θ : ℝ)
    (η : Fin m → ComplexVector n) (hM : (weightedColumns α η*(weightedColumns α η)ᴴ).PosDef)
    (j : Fin m) : ContinuousAt (fun ξ => columnLowerMatrix α θ ξ j) η := by
  have hSmooth : ContDiffAt ℝ ∞ (fun ξ => (weightedColumns α ξ*(weightedColumns α ξ)ᴴ)⁻¹) η :=
    (inverseGram_contDiffAt _ hM).comp η
      ((weightedColumnsCLM α).restrictScalars ℝ).contDiff.contDiffAt
  have hInv := hSmooth.continuousAt
  have hEntry (a b : Fin n) : ContDiffAt ℝ ∞
      (fun ξ => (weightedColumns α ξ*(weightedColumns α ξ)ᴴ)⁻¹ a b) η :=
    hSmooth.continuousLinearMap_comp (rectEntryCLM n n a b)
  have hXi (a : Fin n) : ContDiffAt ℝ ∞ (fun ξ : Fin m → ComplexVector n => (ξ j) a) η :=
    (contDiffAt_piLp_apply (p := 2) (i := a)).comp η
      (contDiff_apply ℝ (fun _ : Fin m => ComplexVector n) j).contDiffAt
  have hQ : ContinuousAt (fun ξ => qform ((weightedColumns α ξ*(weightedColumns α ξ)ᴴ)⁻¹) (ξ j)) η := by
    have hSum : ContDiffAt ℝ ∞ (fun ξ : Fin m → ComplexVector n =>
        ∑ a, star ((ξ j) a)*∑ b, (weightedColumns α ξ*(weightedColumns α ξ)ᴴ)⁻¹ a b*(ξ j) b) η :=
      ContDiffAt.sum fun a _ =>
        (Complex.conjCLE.contDiff.contDiffAt.comp η (hXi a)).mul
          (ContDiffAt.sum fun b _ => (hEntry a b).mul (hXi b))
    simp only [qform,dotProduct,Matrix.mulVec,Pi.star_apply]
    exact (Complex.reCLM.contDiff.contDiffAt.comp η hSum).continuousAt
  exact (continuousAt_const.mul (continuousAt_const.sub
    (continuousAt_const.mul hQ))).ofReal.smul hInv

theorem columnLowerMatrix_at_contact {n m : ℕ} (α : Fin m → ℝ) (θ : ℝ)
    (η : Fin m → ComplexVector n) (B : Herm n) (hB : B.PosDef)
    (hGram : weightedColumns α η*(weightedColumns α η)ᴴ = B⁻¹)
    (j : Fin m) (hq : qform B (η j) = 1) :
    columnLowerMatrix α θ η j = (((1-θ)*(1-α j) : ℝ) : ℂ) • B := by
  unfold columnLowerMatrix
  rw [hGram,Matrix.nonsing_inv_nonsing_inv _ (hB.isUnit.map Matrix.detMonoidHom),hq,mul_one]

end Yau.NodeProofs.E02Aux
