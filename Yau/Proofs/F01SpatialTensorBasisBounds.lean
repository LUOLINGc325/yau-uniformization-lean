import Yau.Proofs.F01HolderComposition
import Mathlib.LinearAlgebra.Multilinear.Basis
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional

/-! Finitely many evaluations on the actual native real frame control
the full spatial multilinear operator norm, including order/dimension zero.
The same fixed finite-dimensional constant controls genuine Holder jets. -/
noncomputable section
open scoped ContDiff
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ}

def spatialTensorBasisEvaluation (k : ℕ) :
    (ContinuousMultilinearMap ℝ (fun _ : Fin k => Space n) ℝ) →ₗ[ℝ]
      ((Fin k → RIdx n) → ℝ) where
  toFun D m := D (fun i => Yau.LeafProofs.L12Aux.realVec_basis n (m i))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem spatialTensorBasisEvaluation_injective (k : ℕ) :
    Function.Injective (spatialTensorBasisEvaluation (n := n) k) := by
  intro D E h
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  apply Module.Basis.ext_multilinear (fun _ : Fin k => Yau.LeafProofs.L12Aux.realVec_basis n)
  intro m
  exact congrFun h m

theorem spatial_tensor_basis_norm_budget (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D : ContinuousMultilinearMap ℝ (fun _ : Fin k => Space n) ℝ)
      (B : ℝ), 0 ≤ B →
      (∀ m : Fin k → RIdx n, ‖D (fun i => realVec (m i))‖ ≤ B) → ‖D‖ ≤ C * B := by
  let J : (ContinuousMultilinearMap ℝ (fun _ : Fin k => Space n) ℝ) →ₗ[ℝ]
      MultilinearMap ℝ (fun _ : Fin k => Space n) ℝ :=
    ContinuousMultilinearMap.toMultilinearMapLinear
  letI : FiniteDimensional ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin k => Space n) ℝ) :=
    FiniteDimensional.of_injective J ContinuousMultilinearMap.toMultilinearMap_injective
  let L := spatialTensorBasisEvaluation (n := n) k
  obtain ⟨C, hC, hAnti⟩ := L.injective_iff_antilipschitz.mp (spatialTensorBasisEvaluation_injective k)
  refine ⟨(C : ℝ), by exact_mod_cast hC, ?_⟩
  intro D B hB hb
  have hnorm : ‖L D‖ ≤ B := by
    apply (pi_norm_le_iff_of_nonneg hB).mpr
    intro m
    change ‖D (fun i => Yau.LeafProofs.L12Aux.realVec_basis n (m i))‖ ≤ B
    simpa only [Yau.LeafProofs.L12Aux.realVec_basis_apply] using hb m
  exact (ZeroHomClass.bound_of_antilipschitz L hAnti D).trans
    (mul_le_mul_of_nonneg_left hnorm C.coe_nonneg)

theorem spatial_tensor_basis_holder_budget (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : Set (Point n)) (β B : ℝ), 0 ≤ B →
      ∀ J : Point n → ContinuousMultilinearMap ℝ (fun _ : Fin k => Space n) ℝ,
      (∀ m : Fin k → RIdx n, HolderBound β Q (fun p => J p (fun i => realVec (m i))) B) →
      HolderBound β Q J (C * B) := by
  obtain ⟨C, hC, hc⟩ := spatial_tensor_basis_norm_budget (n := n) k
  refine ⟨C, hC, ?_⟩
  intro Q β B hB J hb
  refine ⟨mul_nonneg hC.le hB, ?_, ?_⟩
  · intro p hp
    exact hc (J p) B hB (fun m => (hb m).2.1 p hp)
  · intro p hp q hq
    have hw : 0 ≤ holderWeight β p q := by unfold holderWeight; positivity
    have hdiff := hc (J p - J q) (B * holderWeight β p q) (mul_nonneg hB hw)
      (fun m => by simpa only [ContinuousMultilinearMap.sub_apply] using (hb m).2.2 p hp q hq)
    exact hdiff.trans_eq (by ring)

end Yau.NodeProofs.F01Aux
