import Yau.Proofs.F01SpatialWordCalculus
import Yau.Proofs.F01VectorWordsTensorJets
import Yau.Proofs.F01LeviSpatialCommutation

/-! The initial-surface tensor bridge uses only smooth spatial slices.
In particular it applies to the actual parabolic C2 zero extension,
without a jointly smooth extension across time zero. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ}

local instance sliceLeviTensorOpNorm (n : ℕ) :
    Norm ((Space n →L[ℝ] Space n →L[ℝ] ℝ) →L[ℝ] Matrix (Fin n) (Fin n) ℂ) :=
  ContinuousLinearMap.hasOpNorm

theorem spatialWord_levi_commute_slice {u : Point n → ℝ} {S : Set (Space n)} {t : ℝ}
    (hS : IsOpen S) (hu : ContDiffOn ℝ ∞ (fun z => u (z, t)) S)
    (vs : List (Space n)) {x : Space n} (hx : x ∈ S) :
    spatialDerivativeWord vs (fun p => leviC (fun z => u (z, p.2)) p.1) (x, t) =
      leviC (fun z => spatialDerivativeWord vs u (z, t)) x := by
  induction vs generalizing x with
  | nil => rfl
  | cons v vs ih =>
    have he : (fun z => spatialDerivativeWord vs
        (fun p => leviC (fun w => u (w, p.2)) p.1) (z, t)) =ᶠ[𝓝 x]
        (fun z => leviC (fun w => spatialDerivativeWord vs u (w, t)) z) := by
      filter_upwards [hS.mem_nhds hx] with z hz
      exact ih hz
    change fderiv ℝ (fun z => spatialDerivativeWord vs
      (fun p => leviC (fun w => u (w, p.2)) p.1) (z, t)) x v = _
    rw [he.fderiv_eq]
    exact leviC_spatial_direction_commute hS (spatialDerivativeWord_smooth_slice hS hu vs) hx v

theorem spatialWord_levi_holder_of_slices {u : Point n → ℝ}
    {S : Set (Space n)} {β C : ℝ} {Q : Set (Point n)} (hS : IsOpen S)
    (hQ : Q ⊆ S ×ˢ (Set.univ : Set ℝ))
    (hu : ∀ p ∈ Q, ContDiffOn ℝ ∞ (fun z => u (z, p.2)) S) (vs : List (Space n))
    (hDD : HolderBound β Q (spatialDD (spatialDerivativeWord vs u)) C) :
    HolderBound β Q
      (spatialDerivativeWord vs (fun p => leviC (fun z => u (z, p.2)) p.1))
      (‖leviSecondMatrixCLM (n := n)‖ * C) := by
  have hLevi := native_levi_holder_of_spatialDD (fun p hp =>
    ((spatialDerivativeWord_smooth_slice hS (hu p hp) vs).contDiffAt
      (hS.mem_nhds (hQ hp).1)).of_le (by simp)) hDD
  refine ⟨hLevi.1, ?_, ?_⟩
  · intro p hp
    change ‖spatialDerivativeWord vs (fun p => leviC (fun z => u (z, p.2)) p.1) p‖ ≤ _
    rw [spatialWord_levi_commute_slice hS (hu p hp) vs (hQ hp).1]
    exact hLevi.2.1 p hp
  · intro p hp q hq
    change ‖spatialDerivativeWord vs (fun p => leviC (fun z => u (z, p.2)) p.1) p -
      spatialDerivativeWord vs (fun p => leviC (fun z => u (z, p.2)) p.1) q‖ ≤ _
    rw [spatialWord_levi_commute_slice hS (hu p hp) vs (hQ hp).1,
      spatialWord_levi_commute_slice hS (hu q hq) vs (hQ hq).1]
    exact hLevi.2.2 p hp q hq

theorem levi_tensor_holder_budget_of_slices (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : Set (Point n)) (S : Set (Space n)) (β B : ℝ)
      (u : Point n → ℝ), IsOpen S → 0 ≤ B → Q ⊆ S ×ˢ (Set.univ : Set ℝ) →
      (∀ p ∈ Q, ContDiffOn ℝ ∞ (fun z => u (z, p.2)) S) →
      (∀ m : Fin k → RIdx n, HolderBound β Q (spatialDD
        (spatialDerivativeWord (List.ofFn (fun i => realVec (m i))) u)) B) →
      HolderBound β Q (fun p => iteratedFDeriv ℝ k
        (fun z => leviC (fun w => u (w, p.2)) z) p.1) (C * B) := by
  obtain ⟨C0, hC0, hc⟩ := spatial_vector_words_tensor_holder_budget
    (n := n) (G := Matrix (Fin n) (Fin n) ℂ) k
  let N : ℝ := ‖leviSecondMatrixCLM (n := n)‖
  have hN : 0 ≤ N := ContinuousLinearMap.opNorm_nonneg _
  refine ⟨1 + C0 * N, by positivity, ?_⟩
  intro Q S β B u hS hB hQ hu hDD
  have hw : ∀ m : Fin k → RIdx n,
      HolderBound β Q (spatialDerivativeWord (List.ofFn (fun i => realVec (m i)))
        (fun p => leviC (fun z => u (z, p.2)) p.1)) (N * B) :=
    fun m => spatialWord_levi_holder_of_slices hS hQ hu _ (hDD m)
  have hs : ∀ p ∈ Q,
      ContDiffOn ℝ ∞ (fun z => leviC (fun w => u (w, p.2)) z) S :=
    fun p hp => native_levi_frobenius_contDiffOn hS (hu p hp)
  have hres := hc Q S β (N * B) hS (mul_nonneg hN hB) hQ
    (fun p => leviC (fun z => u (z, p.2)) p.1) hs hw
  apply holderBound_mono_const hres
  nlinarith

end Yau.NodeProofs.F01Aux
