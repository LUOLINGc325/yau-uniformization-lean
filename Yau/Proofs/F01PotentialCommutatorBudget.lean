import Yau.Proofs.F01UniformSymbolSpatialJets
import Yau.Proofs.F01UniformInitialForcingJets
import Yau.Proofs.F01UniformCommutatorHolder

/-! The actual differentiated potential equation has one commutator
forcing bound before every native word of a fixed order, unit direction
and realization. Its solution data involve strictly lower Hessian words. -/
noncomputable section
open Set
open scoped ContDiff Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ}
attribute [local instance] sourceMatrixDualNormed sourceSpatialMatrixNormed
  sourceMatrixDualSpace sourceSpatialMatrixSpace

theorem potential_direction_commutator_holder_budget {ell C Cu : ℝ}
    (hell : 0 < ell) (hC : 0 ≤ C) (hCu : 0 ≤ Cu) (r : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ (Q : Set (Point n)) (O : Set (Space n)) (β : ℝ)
      (H S : Point n → Matrix (Fin n) (Fin n) ℂ) (b w : Point n → ℝ),
      IsOpen O → Q ⊆ O ×ˢ (Set.univ : Set ℝ) → HolderBound β Q H C →
      (∀ p ∈ Q, (H p - (ell : ℂ) • 1).PosSemidef) →
      (∀ p ∈ Q, ∀ z ∈ O, (H (z, p.2)).PosDef) →
      (∀ p ∈ Q, ContDiffOn ℝ ∞ (fun z => H (z, p.2)) O) →
      (∀ p ∈ Q, ContDiffOn ℝ ∞ (fun z => S (z, p.2)) O) →
      (∀ p ∈ Q, ContDiffOn ℝ ∞ (fun z => b (z, p.2)) O) →
      (∀ p ∈ Q, ContDiffOn ℝ ∞ (fun z => w (z, p.2)) O) →
      (∀ j : ℕ, j ≤ r → HolderBound β Q
        (fun p => iteratedFDeriv ℝ j (fun z => H (z, p.2)) p.1) C) →
      (∀ j : ℕ, j ≤ r + 1 → HolderBound β Q
        (fun p => iteratedFDeriv ℝ j (fun z => S (z, p.2)) p.1) C) →
      (∀ j : ℕ, j ≤ r + 1 → HolderBound β Q
        (fun p => iteratedFDeriv ℝ j (fun z => b (z, p.2)) p.1) C) →
      (∀ ws : List (Space n), NativeFrameWord ws → ws.length < r →
        HolderBound β Q (spatialDD (spatialDerivativeWord ws w)) Cu) →
      ∀ v : Space n, ‖v‖ ≤ 1 → ∀ vs : List (Space n), NativeFrameWord vs → vs.length = r →
        HolderBound β Q (linearCommutatorSource (fun p => scalarSymbol (H p)) w
          (fun p => traceWith (H p) (fderiv ℝ (fun z => S (z, p.2)) p.1 v) +
            fderiv ℝ (fun z => b (z, p.2)) p.1 v) vs) B := by
  obtain ⟨Ca, hCa, hCoeff⟩ := scalarSymbol_uniform_spatial_jet_budget (n := n) hell hC r
  obtain ⟨Cf, hCf, hForce⟩ := initial_forcing_uniform_spatial_jet_budget (n := n) hell hC r
  obtain ⟨B, hB, hBudget⟩ := uniform_native_commutator_holder_budget (n := n) r hCa.le hCu hCf.le
  refine ⟨B, hB, ?_⟩
  intro Q O β H S b w hO hQ hH hlo hpos hHs hSs hbs hws hHj hSj hbj hLower v hv vs hvs hlen
  let f := fun p : Point n => traceWith (H p)
    (fderiv ℝ (fun z => S (z, p.2)) p.1 v) + fderiv ℝ (fun z => b (z, p.2)) p.1 v
  have ha (p : Point n) (hp : p ∈ Q) :
      ContDiffOn ℝ ∞ (fun z => scalarSymbol (H (z, p.2))) O :=
    scalarSymbol_contDiffOn_nonsingular.comp (hHs p hp)
      (fun z hz => (hpos p hp z hz).det_pos.ne')
  have hf (p : Point n) (hp : p ∈ Q) : ContDiffOn ℝ ∞ (fun z => f (z, p.2)) O := by
    have hG := potentialSourceGradient_field_smooth hO (hHs p hp) (hSs p hp) (hbs p hp) (hpos p hp)
    apply (hG.clm_apply (contDiffOn_const (c := v))).congr
    intro z hz
    exact (potentialSourceGradient_apply _ _ _ (hpos p hp z hz) v).symm
  exact hBudget Q O β (fun p => scalarSymbol (H p)) w f hO hQ ha hws hf
    (hCoeff Q O β H hO hQ hH hlo hHs hHj)
    (hForce Q O β H S b hO hQ hlo hpos hHs hSs hbs hHj hSj hbj v hv)
    hLower vs hvs hlen

end Yau.NodeProofs.F01Aux
