import Yau.Proofs.F01PreviousMatrixJetBudget
import Yau.Proofs.F01PotentialSchauderStep
import Yau.Proofs.F01ZeroExtendedWordEquations

/-! One noncircular potential bootstrap step. Earlier differentiated
Schauder words determine both matrix jets and the current word's
supremum; the actual linear equation then supplies its new Hessian. -/
noncomputable section
open Set Metric
open scoped ContDiff Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ}

theorem potential_bootstrap_step_budget (hn : 0 < n) (order : ℕ)
    {κ β D Cs Cu Ci : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hβ : 0 < β) (hβ1 : β < 1) (hD : 1 ≤ D)
    (hCs : 0 ≤ Cs) (hCu : 0 ≤ Cu) (hCi : 0 ≤ Ci) :
    ∃ K : ℝ, 0 < K ∧ ∀ (R r a b l s : ℝ)
      (S : Point n → Matrix (Fin n) (Fin n) ℂ) (u : Point n → ℝ) (d : Space n → ℝ),
      l < s → r + 2 * κ ≤ R → a + 4 * κ ^ 2 ≤ l → s ≤ b →
      let Q := cylinder (ball 0 R) a b
      let H := chartPotentialMatrix S u
      HolderBound β Q S Cs →
      (∀ p ∈ Q, ContDiffOn ℝ ∞ (fun z => S (z, p.2)) (ball 0 R)) →
      (∀ p ∈ Q, ContDiffOn ℝ ∞ (fun z => u (z, p.2)) (ball 0 R)) →
      ContDiffOn ℝ ∞ d (ball 0 R) →
      (∀ j : ℕ, j ≤ order + 1 → HolderBound β Q
        (fun p => iteratedFDeriv ℝ j (fun z => S (z, p.2)) p.1) Cs) →
      (∀ j : ℕ, j ≤ order + 1 → HolderBound β Q
        (fun p => iteratedFDeriv ℝ j d p.1) Cs) →
      (∀ p ∈ Q, (H p).PosDef) →
      (∀ p ∈ Q, (H p - ((D⁻¹ : ℝ) : ℂ) • 1).PosSemidef ∧
        ((D : ℂ) • 1 - H p).PosSemidef) →
      SchauderBound β Q u Ci → HolderBound β Q (spatialDD u) Cu →
      (∀ (i : RIdx n) (ws : List (Space n)), NativeFrameWord ws → ws.length < order →
        SchauderBound β Q (spatialDerivativeWord ws (spatialDerivativeWord [realVec i] u)) Cu) →
      ∀ (i : RIdx n) (vs : List (Space n)), NativeFrameWord vs → vs.length = order →
        let w := spatialDerivativeWord [realVec i] u
        let f := fun p => traceWith (H p)
          (fderiv ℝ (fun z => S (z, p.2)) p.1 (realVec i)) + fderiv ℝ d p.1 (realVec i)
        C2 Q (spatialDerivativeWord vs w) →
        (∀ p ∈ Q, linearOp Q (fun q => scalarSymbol (H q)) (fun _ _ => 0)
          (spatialDerivativeWord vs w) p =
          linearCommutatorSource (fun q => scalarSymbol (H q)) w f vs p) →
        SchauderBound β (cylinder (ball 0 r) l s) (spatialDerivativeWord vs w) K := by
  obtain ⟨Cm, hCm, hMatrix⟩ := previous_schauder_matrix_jet_budget (n := n) order hCs hCu
  let C := max Cs Cm
  let B := max Ci Cu
  have hC : 0 ≤ C := hCs.trans (le_max_left _ _)
  have hB : 0 ≤ B := hCi.trans (le_max_left _ _)
  obtain ⟨K, hK, hStep⟩ := potential_word_schauder_step_budget (n := n) hn
    hκ hκ1 hβ hβ1 hD hC hCu hB order
  refine ⟨K, hK, ?_⟩
  intro R r a b l s S u d hls hSpace hLower hUpper
  dsimp only
  intro hS hSs hus hd hSj hdj hPos hBounds hInitial hDD hPrev i vs hvs hlen hC2 hEq
  have hQ : cylinder (ball (0 : Space n) R) a b ⊆ ball 0 R ×ˢ (Set.univ : Set ℝ) :=
    fun p hp => ⟨hp.1, mem_univ _⟩
  have hMat := hMatrix (cylinder (ball 0 R) a b) (ball 0 R) β S u isOpen_ball hQ
    hS hSs hus (fun j => hSj j.val (by omega)) hDD hPrev
  have hH : HolderBound β (cylinder (ball 0 R) a b) (chartPotentialMatrix S u) C :=
    holderBound_mono_const hMat.1 (le_max_right _ _)
  have hHj (j : ℕ) (hj : j ≤ order) : HolderBound β (cylinder (ball 0 R) a b)
      (fun p => iteratedFDeriv ℝ j (fun z => chartPotentialMatrix S u (z, p.2)) p.1) C :=
    holderBound_mono_const (hMat.2 ⟨j, by omega⟩) (le_max_right _ _)
  have hSup : ∀ p ∈ cylinder (ball 0 R) a b,
      |spatialDerivativeWord vs (spatialDerivativeWord [realVec i] u) p| ≤ B := by
    intro p hp
    cases vs with
    | nil =>
      exact (word_cons_sup_of_schauder [] (realVec_norm_one i).le hInitial p hp).trans (le_max_left _ _)
    | cons v ws =>
      obtain ⟨j, hj⟩ := hvs v (by simp)
      have hv : ‖v‖ ≤ 1 := by rw [hj]; exact (realVec_norm_one j).le
      have hws : NativeFrameWord ws := fun z hz => hvs z (by simp [hz])
      have hsmall : ws.length < order := by simp only [List.length_cons] at hlen; omega
      exact (word_cons_sup_of_schauder ws hv (hPrev i ws hws hsmall) p hp).trans (le_max_right _ _)
  apply hStep R r a b l s (chartPotentialMatrix S u) S
    (spatialDerivativeWord [realVec i] u) (fun p => d p.1) hls hSpace hLower hUpper
    hH hBounds
  · intro p hp z hz
    exact hPos (z, p.2) ⟨hz, hp.2⟩
  · intro p hp
    exact chartPotentialMatrix_smooth_slice isOpen_ball (hSs p hp) (hus p hp)
  · exact hSs
  · intro p hp
    exact hd
  · intro p hp
    exact spatialDerivativeWord_smooth_slice isOpen_ball (hus p hp) [realVec i]
  · exact hHj
  · intro j hj
    exact holderBound_mono_const (hSj j hj) (le_max_left _ _)
  · intro j hj
    exact holderBound_mono_const (hdj j hj) (le_max_left _ _)
  · intro ws hws hsmall
    exact (hPrev i ws hws hsmall).2.2.2.1
  · exact (realVec_norm_one i).le
  · exact hvs
  · exact hlen
  · exact hC2
  · exact hSup
  · exact hEq

end Yau.NodeProofs.F01Aux
