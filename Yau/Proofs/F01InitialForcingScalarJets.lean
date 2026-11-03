import Yau.Proofs.F01InitialForcingTensorJets
import Yau.Proofs.F01TensorLinearImage
import Yau.Proofs.F01AffineParabolicHolder

/-! Evaluate the genuine forcing covector in an arbitrary unit
direction. Its scalar jet constants precede the direction as well as
the coefficient fields, and the conclusion uses the actual inverse trace. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ}
attribute [local instance] sourceMatrixDualNormed sourceSpatialMatrixNormed
  sourceMatrixDualSpace sourceSpatialMatrixSpace

theorem potentialSourceGradient_field_smooth
    {H S : Point n → Matrix (Fin n) (Fin n) ℂ} {b : Point n → ℝ}
    {O : Set (Space n)} {t : ℝ} (hO : IsOpen O)
    (hH : ContDiffOn ℝ ∞ (fun z => H (z, t)) O)
    (hS : ContDiffOn ℝ ∞ (fun z => S (z, t)) O)
    (hb : ContDiffOn ℝ ∞ (fun z => b (z, t)) O)
    (hpos : ∀ z ∈ O, (H (z, t)).PosDef) :
    ContDiffOn ℝ ∞ (fun z => potentialSourceGradient (H (z, t),
      (fderiv ℝ (fun y => S (y, t)) z, fderiv ℝ (fun y => b (y, t)) z))) O := by
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ (fun y => S (y, t))) O :=
    hS.fderiv_of_isOpen hO (by simp)
  have hDb : ContDiffOn ℝ ∞ (fderiv ℝ (fun y => b (y, t))) O :=
    hb.fderiv_of_isOpen hO (by simp)
  apply (potentialSourceGradient_contDiffOn n).comp (hH.prodMk (hD.prodMk hDb))
  intro z hz
  exact (Complex.pos_iff.mp (hpos z hz).det_pos).1.ne'

theorem initial_forcing_spatial_scalar_jet_budget {ell C : ℝ}
    (hell : 0 < ell) (hC : 0 ≤ C) (k : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ (Q : Set (Point n)) (O : Set (Space n)) (β : ℝ)
      (H S : Point n → Matrix (Fin n) (Fin n) ℂ) (b : Point n → ℝ),
      IsOpen O → Q ⊆ O ×ˢ (Set.univ : Set ℝ) →
      (∀ p ∈ Q, (H p - (ell : ℂ) • 1).PosSemidef) →
      (∀ p ∈ Q, ∀ z ∈ O, (H (z, p.2)).PosDef) →
      (∀ p ∈ Q, ContDiffOn ℝ ∞ (fun z => H (z, p.2)) O) →
      (∀ p ∈ Q, ContDiffOn ℝ ∞ (fun z => S (z, p.2)) O) →
      (∀ p ∈ Q, ContDiffOn ℝ ∞ (fun z => b (z, p.2)) O) →
      (∀ j : ℕ, j ≤ k → HolderBound β Q
        (fun p => iteratedFDeriv ℝ j (fun z => H (z, p.2)) p.1) C) →
      (∀ j : ℕ, j ≤ k + 1 → HolderBound β Q
        (fun p => iteratedFDeriv ℝ j (fun z => S (z, p.2)) p.1) C) →
      (∀ j : ℕ, j ≤ k + 1 → HolderBound β Q
        (fun p => iteratedFDeriv ℝ j (fun z => b (z, p.2)) p.1) C) →
      ∀ v : Space n, ‖v‖ ≤ 1 → HolderBound β Q (fun p => iteratedFDeriv ℝ k
        (fun z => traceWith (H (z, p.2)) (fderiv ℝ (fun y => S (y, p.2)) z v) +
          fderiv ℝ (fun y => b (y, p.2)) z v) p.1) B := by
  obtain ⟨B, hB, hb⟩ := initial_forcing_spatial_tensor_jet_budget (n := n) hell hC k
  refine ⟨B, hB, ?_⟩
  intro Q O β H S b hO hQ hlo hpos hHs hSs hbs hHj hSj hbj v hv
  let G := fun p : Point n => potentialSourceGradient (H p,
    (fderiv ℝ (fun y => S (y, p.2)) p.1, fderiv ℝ (fun y => b (y, p.2)) p.1))
  let L : (Space n →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ v
  have hGs (p : Point n) (hp : p ∈ Q) : ContDiffOn ℝ ∞ (fun z => G (z, p.2)) O :=
    potentialSourceGradient_field_smooth hO (hHs p hp) (hSs p hp) (hbs p hp) (hpos p hp)
  have hG : HolderBound β Q
      (fun p => iteratedFDeriv ℝ k (fun z => G (z, p.2)) p.1) B :=
    hb Q O β H S b hO hQ hlo hHs hSs hbs hHj hSj hbj
  have hOut := holderBound_spatial_tensor_linear_contraction (f := G)
    k hO hQ hGs L (covector_evaluation_norm_le_one v hv) hG
  have he (p : Point n) (hp : p ∈ Q) :
      iteratedFDeriv ℝ k (fun z => L (G (z, p.2))) p.1 =
      iteratedFDeriv ℝ k (fun z => traceWith (H (z, p.2))
        (fderiv ℝ (fun y => S (y, p.2)) z v) +
        fderiv ℝ (fun y => b (y, p.2)) z v) p.1 := by
    have hLocal : (fun z => L (G (z, p.2))) =ᶠ[𝓝 p.1]
        (fun z => traceWith (H (z, p.2)) (fderiv ℝ (fun y => S (y, p.2)) z v) +
          fderiv ℝ (fun y => b (y, p.2)) z v) := by
      filter_upwards [hO.mem_nhds (hQ hp).1] with z hz
      exact potentialSourceGradient_apply _ _ _ (hpos p hp z hz) v
    exact (hLocal.iteratedFDeriv (𝕜 := ℝ) k).eq_of_nhds
  apply holderBound_congr_on_native hOut
  intro p hp
  exact he p hp

end Yau.NodeProofs.F01Aux
