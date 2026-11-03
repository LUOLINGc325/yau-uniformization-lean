import Yau.Proofs.F01NativeFrameWordHolder
import Yau.Proofs.F01CommutatorSourceHolder

/-! One numerical forcing budget precedes every native frame word of
fixed order and every realized equation. The solution input consists
strictly of lower Hessian words, as required by the Schauder induction. -/
noncomputable section
open Set
open scoped ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ}

local instance uniformCommutatorBilinearNorm (n : ℕ) :
    Norm (Mat n →L[ℝ] (Space n →L[ℝ] Space n →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.hasOpNorm

theorem uniform_native_commutator_holder_budget (r : ℕ) {Ca Cu Cf : ℝ}
    (hCa : 0 ≤ Ca) (hCu : 0 ≤ Cu) (hCf : 0 ≤ Cf) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : Set (Point n)) (S : Set (Space n)) (β : ℝ)
      (a : Point n → Mat n) (u f : Point n → ℝ), IsOpen S →
      Q ⊆ S ×ˢ (Set.univ : Set ℝ) →
      (∀ p ∈ Q, ContDiffOn ℝ ∞ (fun z => a (z, p.2)) S) →
      (∀ p ∈ Q, ContDiffOn ℝ ∞ (fun z => u (z, p.2)) S) →
      (∀ p ∈ Q, ContDiffOn ℝ ∞ (fun z => f (z, p.2)) S) →
      (∀ j : ℕ, j ≤ r → HolderBound β Q
        (fun p => iteratedFDeriv ℝ j (fun z => a (z, p.2)) p.1) Ca) →
      (∀ j : ℕ, j ≤ r → HolderBound β Q
        (fun p => iteratedFDeriv ℝ j (fun z => f (z, p.2)) p.1) Cf) →
      (∀ ws : List (Space n), NativeFrameWord ws → ws.length < r →
        HolderBound β Q (spatialDD (spatialDerivativeWord ws u)) Cu) →
      ∀ vs : List (Space n), NativeFrameWord vs → vs.length = r →
        HolderBound β Q (linearCommutatorSource a u f vs) C := by
  let M : ℝ := 2 * ‖realHessianContractionCLM (n := n)‖ * Ca * Cu
  have hM : 0 ≤ M := mul_nonneg (mul_nonneg
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
      (ContinuousLinearMap.opNorm_nonneg _)) hCa) hCu
  let C : ℝ := 1 + Cf + (2 : ℝ) ^ r * M
  have hC : 0 < C := by
    dsimp only [C]
    linarith [mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) r) hM]
  refine ⟨C, hC, ?_⟩
  intro Q S β a u f hS hQ ha hu hf hAj hFj hLower vs hv hvs
  have hF := native_frame_word_holder_of_tensor hS hQ hf vs hv
    (hFj vs.length (by omega))
  have hA : ∀ ab ∈ linearSpatialCommutatorPairs vs,
      HolderBound β Q (spatialDerivativeWord ab.1 a) Ca := by
    intro ab hab
    have hFrame := (nativeFrameWord_commutator_pairs vs hv ab hab).1
    have hOrders := (linearSpatialCommutatorPairs_orders vs ab hab).2
    exact native_frame_word_holder_of_tensor hS hQ ha ab.1 hFrame
      (hAj ab.1.length (by omega))
  have hH : ∀ ab ∈ linearSpatialCommutatorPairs vs,
      HolderBound β Q (spatialDD (spatialDerivativeWord ab.2 u)) Cu := by
    intro ab hab
    exact hLower ab.2 (nativeFrameWord_commutator_pairs vs hv ab hab).2
      (by have hh := linearSpatialCommutatorPairs_lower_solution_order vs hab; omega)
  have hSource := linearCommutatorSource_holder a u f hS hQ ha hu hf hCa hCu vs hF hA hH
  have hLen : ((linearSpatialCommutatorPairs vs).length : ℝ) ≤ (2 : ℝ) ^ r := by
    have hn := linearSpatialCommutatorPairs_count vs
    rw [hvs] at hn
    have hNat : (linearSpatialCommutatorPairs vs).length ≤ 2 ^ r := by omega
    exact_mod_cast hNat
  apply holderBound_mono_const hSource
  change Cf + ((linearSpatialCommutatorPairs vs).length : ℝ) * M ≤ C
  have hh := mul_le_mul_of_nonneg_right hLen hM
  dsimp only [C]
  linarith

end Yau.NodeProofs.F01Aux
