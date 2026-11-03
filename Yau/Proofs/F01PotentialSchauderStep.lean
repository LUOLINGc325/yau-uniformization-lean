import Yau.Proofs.F01PotentialCommutatorBudget
import Yau.Proofs.F01NativeBufferedSchauder
import Yau.Proofs.F01ScalarSymbolEllipticity

/-! One quantitative step for the actual differentiated potential
equation. The word equation and qualitative C2 data are supplied by the
proved zero-extension calculus. Only lower Hessian words enter the
forcing budget; the original L16 producer supplies the new estimate. -/
noncomputable section
open Set Metric
open scoped ContDiff Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ}

theorem potential_word_schauder_step_budget (hn : 0 < n)
    {κ β D C Cu Bu : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hβ : 0 < β) (hβ1 : β < 1) (hD : 1 ≤ D)
    (hC : 0 ≤ C) (hCu : 0 ≤ Cu) (hBu : 0 ≤ Bu) (order : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (R r a b l s : ℝ)
      (H S : Point n → Matrix (Fin n) (Fin n) ℂ) (w d : Point n → ℝ),
      l < s → r + 2 * κ ≤ R → a + 4 * κ ^ 2 ≤ l → s ≤ b →
      let Q := cylinder (ball 0 R) a b
      HolderBound β Q H C →
      (∀ p ∈ Q, (H p - ((D⁻¹ : ℝ) : ℂ) • 1).PosSemidef ∧
        ((D : ℂ) • 1 - H p).PosSemidef) →
      (∀ p ∈ Q, ∀ z ∈ ball 0 R, (H (z, p.2)).PosDef) →
      (∀ p ∈ Q, ContDiffOn ℝ ∞ (fun z => H (z, p.2)) (ball 0 R)) →
      (∀ p ∈ Q, ContDiffOn ℝ ∞ (fun z => S (z, p.2)) (ball 0 R)) →
      (∀ p ∈ Q, ContDiffOn ℝ ∞ (fun z => d (z, p.2)) (ball 0 R)) →
      (∀ p ∈ Q, ContDiffOn ℝ ∞ (fun z => w (z, p.2)) (ball 0 R)) →
      (∀ j : ℕ, j ≤ order → HolderBound β Q
        (fun p => iteratedFDeriv ℝ j (fun z => H (z, p.2)) p.1) C) →
      (∀ j : ℕ, j ≤ order + 1 → HolderBound β Q
        (fun p => iteratedFDeriv ℝ j (fun z => S (z, p.2)) p.1) C) →
      (∀ j : ℕ, j ≤ order + 1 → HolderBound β Q
        (fun p => iteratedFDeriv ℝ j (fun z => d (z, p.2)) p.1) C) →
      (∀ ws : List (Space n), NativeFrameWord ws → ws.length < order →
        HolderBound β Q (spatialDD (spatialDerivativeWord ws w)) Cu) →
      ∀ v : Space n, ‖v‖ ≤ 1 → ∀ vs : List (Space n), NativeFrameWord vs → vs.length = order →
        let f := fun p => traceWith (H p) (fderiv ℝ (fun z => S (z, p.2)) p.1 v) +
          fderiv ℝ (fun z => d (z, p.2)) p.1 v
        C2 Q (spatialDerivativeWord vs w) →
        (∀ p ∈ Q, |spatialDerivativeWord vs w p| ≤ Bu) →
        (∀ p ∈ Q, linearOp Q (fun q => scalarSymbol (H q)) (fun _ _ => 0)
          (spatialDerivativeWord vs w) p = linearCommutatorSource (fun q => scalarSymbol (H q)) w f vs p) →
        SchauderBound β (cylinder (ball 0 r) l s) (spatialDerivativeWord vs w) K := by
  have hDpos : 0 < D := zero_lt_one.trans_le hD
  have hell : 0 < D⁻¹ := inv_pos.mpr hDpos
  obtain ⟨M, hM, hCoeff⟩ := scalarSymbol_holder_budget (n := n) hell hC
  obtain ⟨F, hF, hSource⟩ := potential_direction_commutator_holder_budget (n := n) hell hC hCu order
  obtain ⟨K, hK, hNative⟩ := native_buffered_linear_schauder_budget (n := n)
    (ell := (4 * D)⁻¹) (upper := D / 4) hn hκ hκ1 hβ hβ1 hM hBu hF.le
  refine ⟨K, hK, ?_⟩
  intro R r a b l s H S w d hls hSpace hLower hUpper
  dsimp only
  intro hH hBounds hpos hHs hSs hds hws hHj hSj hdj hLowerWords v hv vs hvs hlen
  intro hWordC2 hWordSup hWordEq
  have hQ : cylinder (ball (0 : Space n) R) a b ⊆ ball 0 R ×ˢ (Set.univ : Set ℝ) :=
    fun p hp => ⟨hp.1, mem_univ _⟩
  have hEll := scalarSymbol_elliptic_of_uniform_sandwich hD
    (fun p hp => hpos p hp p.1 hp.1) hBounds
  have hA := hCoeff (cylinder (ball 0 R) a b) β H hH (fun p hp => (hBounds p hp).1)
  have hf := hSource (cylinder (ball 0 R) a b) (ball 0 R) β H S d w isOpen_ball hQ
    hH (fun p hp => (hBounds p hp).1) hpos hHs hSs hds hws hHj hSj hdj hLowerWords
    v hv vs hvs hlen
  exact hNative R r a b l s (fun p => scalarSymbol (H p)) (spatialDerivativeWord vs w)
    (linearCommutatorSource (fun p => scalarSymbol (H p)) w
      (fun p => traceWith (H p) (fderiv ℝ (fun z => S (z, p.2)) p.1 v) +
        fderiv ℝ (fun z => d (z, p.2)) p.1 v) vs)
    hls hSpace hLower hUpper hEll hA hf hWordC2 hWordSup hWordEq

end Yau.NodeProofs.F01Aux
