import Yau.Proofs.F01InitialSourceJetBudget
import Yau.Proofs.F01DerivativeTensorHolder
import Yau.Proofs.F01TripleTensorHolder
import Yau.Proofs.F01NativeFrameWordHolder

/-! Assemble the computed first differentiated potential forcing from
the same transformed matrix and genuine background jets. Each order has
one constant before every realization, and uses matrix jets only through
that order and background jets through the next order. -/
noncomputable section
open Set
open scoped ContDiff Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ}
attribute [local instance] sourceMatrixDualNormed sourceSpatialMatrixNormed
  sourceMatrixDualSpace sourceSpatialMatrixSpace

theorem initial_forcing_spatial_tensor_jet_budget {ell C : ℝ}
    (hell : 0 < ell) (hC : 0 ≤ C) (k : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ (Q : Set (Point n)) (O : Set (Space n)) (β : ℝ)
      (H S : Point n → Matrix (Fin n) (Fin n) ℂ) (b : Point n → ℝ),
      IsOpen O → Q ⊆ O ×ˢ (Set.univ : Set ℝ) →
      (∀ p ∈ Q, (H p - (ell : ℂ) • 1).PosSemidef) →
      (∀ p ∈ Q, ContDiffOn ℝ ∞ (fun z => H (z, p.2)) O) →
      (∀ p ∈ Q, ContDiffOn ℝ ∞ (fun z => S (z, p.2)) O) →
      (∀ p ∈ Q, ContDiffOn ℝ ∞ (fun z => b (z, p.2)) O) →
      (∀ j : ℕ, j ≤ k → HolderBound β Q
        (fun p => iteratedFDeriv ℝ j (fun z => H (z, p.2)) p.1) C) →
      (∀ j : ℕ, j ≤ k + 1 → HolderBound β Q
        (fun p => iteratedFDeriv ℝ j (fun z => S (z, p.2)) p.1) C) →
      (∀ j : ℕ, j ≤ k + 1 → HolderBound β Q
        (fun p => iteratedFDeriv ℝ j (fun z => b (z, p.2)) p.1) C) →
      HolderBound β Q (fun p => iteratedFDeriv ℝ k
        (fun z => potentialSourceGradient (H (z, p.2),
          (fderiv ℝ (fun y => S (y, p.2)) z, fderiv ℝ (fun y => b (y, p.2)) z))) p.1) B := by
  obtain ⟨B, hB, hb⟩ := potentialSourceGradient_jet_holder_budget (n := n) hell hC k
  refine ⟨B, hB, ?_⟩
  intro Q O β H S b hO hQ hlo hHs hSs hbs hHj hSj hbj
  let DS := fun p : Point n => fderiv ℝ (fun z => S (z, p.2)) p.1
  let Db := fun p : Point n => fderiv ℝ (fun z => b (z, p.2)) p.1
  let Z := fun p : Point n => (H p, (DS p, Db p))
  have hDSs (p : Point n) (hp : p ∈ Q) : ContDiffOn ℝ ∞ (fun z => DS (z, p.2)) O :=
    (hSs p hp).fderiv_of_isOpen hO (by simp)
  have hDbs (p : Point n) (hp : p ∈ Q) : ContDiffOn ℝ ∞ (fun z => Db (z, p.2)) O :=
    (hbs p hp).fderiv_of_isOpen hO (by simp)
  have hPair (p : Point n) (hp : p ∈ Q) :
      ContDiffOn ℝ ∞ (fun z => (DS (z, p.2), Db (z, p.2))) O :=
    (hDSs p hp).prodMk (hDbs p hp)
  have hZs (p : Point n) (hp : p ∈ Q) : ContDiffOn ℝ ∞ (fun z => Z (z, p.2)) O :=
    (hHs p hp).prodMk (hPair p hp)
  have hZj (j : ℕ) (hj : j ≤ k) : HolderBound β Q
      (fun p => iteratedFDeriv ℝ j (fun z => Z (z, p.2)) p.1) C := by
    have hDj := holderBound_spatial_tensor_derivative
      (f := S) j (hSj (j + 1) (by omega))
    have hbj' := holderBound_spatial_tensor_derivative
      (f := b) j (hbj (j + 1) (by omega))
    exact holderBound_spatial_tensor_triple (f := H) (g := DS) (h := Db)
      (C := C) j hO hQ hHs hDSs hDbs (hHj j hj) hDj hbj'
  have hZ : HolderBound β Q Z C := by
    have hz := native_frame_word_holder_of_tensor hO hQ hZs []
      (by intro v hv; simp at hv) (hZj 0 (Nat.zero_le k))
    simpa only [spatialDerivativeWord] using hz
  exact hb Q O β Z hO hQ hZ hlo hZs (fun j => hZj j.val (by omega))

end Yau.NodeProofs.F01Aux
