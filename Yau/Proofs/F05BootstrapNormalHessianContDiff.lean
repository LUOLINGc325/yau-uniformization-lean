import Yau.Proofs.F05BootstrapNormalGradientContDiff
import Yau.Proofs.F05BootstrapSourceContDiff
import Yau.Proofs.F05BootstrapLinearNormalRecovery
import Yau.Proofs.F05BootstrapGoodSourceAlgebra

/-! Inner finite word-length induction recovers every normal Hessian at
the current joint order. The commutator source uses only shorter Hessians;
all off-normal entries come from the value/normal-first family. -/

open Set
open scoped ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2400000
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_word_hessian_contDiff {T α lam upper : ℝ} {k : ℕ} {Q : Set (Point n)}
    (j : RIdx n) (hQ : Q ⊆ F05PosPatch (some j) T)
    (A : Point n → Mat n) (B : Point n → RIdx n → ℝ) (H J u : Point n → ℝ)
    (hA : ContDiffOn ℝ ∞ A (Metric.ball 0 3 ×ˢ Ioc 0 T))
    (hB : ∀ i, ContDiffOn ℝ ∞ (fun z => B z i) (Metric.ball 0 3 ×ˢ Ioc 0 T))
    (hH : ContDiffOn ℝ ∞ H (Metric.ball 0 3 ×ˢ Ioc 0 T))
    (hJ : ContDiffOn ℝ ∞ J (Metric.ball 0 3 ×ˢ Ioc 0 T))
    (hEll : Elliptic (F05PosPatch (some j) T) (fun z => Real.exp (-u z) • A z) lam upper)
    (hWords : ∀ γ : List (Option (RIdx n)), F05GoodList (some j) γ →
      F05LocalSchauder α (some j) T (F05GoodWord T γ u))
    (hEquations : ∀ β : List (Option (RIdx n)), F05GoodList (some j) β → ∀ z ∈ F05PosPatch (some j) T,
      F05RelOp (F05PosSpace (some j)) (Ioc 0 T) (fun z => Real.exp (-u z) • A z)
        (fun z i => Real.exp (-u z)*B z i) (F05GoodWord T β u) z =
      F05GoodSource T (F05PosSpace (some j)) (fun z => Real.exp (-u z) • A z)
        (fun z i => Real.exp (-u z)*B z i) (fun z => Real.exp (-u z)*H z+J z) u β z)
    (hJoint : ∀ γ : List (Option (RIdx n)), F05GoodList (some j) γ →
      ContDiffOn ℝ k (F05GoodWord T γ u) Q)
    (hNormal : ∀ γ : List (Option (RIdx n)), F05GoodList (some j) γ →
      ContDiffOn ℝ k (F05NormalWord T j γ u) Q) :
    ∀ β : List (Option (RIdx n)), F05GoodList (some j) β →
      ContDiffOn ℝ k (F05RelDD (F05PosSpace (some j)) (F05GoodWord T β u)) Q := by
  classical
  let a := fun z => Real.exp (-u z) • A z
  let b := fun z i => Real.exp (-u z)*B z i
  let f := fun z => Real.exp (-u z)*H z+J z
  let X := F05PosSpace (some j)
  have hNil : F05GoodList (some j) ([] : List (Option (RIdx n))) := by simp [F05GoodList]
  have hAWord := fun β hβ => F05_exp_background_word_contDiff hQ u A hWords hJoint hA β hβ
  have hBWord := fun β hβ i => F05_exp_background_word_contDiff hQ u (fun z => B z i) hWords hJoint (hB i) β hβ
  have hFWord := fun β hβ => F05_exp_forcing_word_contDiff hQ u H J hWords hJoint hH hJ β hβ
  have hGradient := fun β hβ => F05_word_gradient_contDiff j hQ u hWords hJoint hNormal β hβ
  have hOff := fun β hβ i l hOff => F05_off_normal_hessian_contDiff j hQ u hWords hJoint hNormal β hβ i l hOff
  have hBaseA : ContDiffOn ℝ k a Q := hAWord [] hNil
  have hBaseB (i : RIdx n) : ContDiffOn ℝ k (fun z => b z i) Q := hBWord [] hNil i
  have hInv : ContDiffOn ℝ k (fun z => (a z j j)⁻¹) Q :=
    ((matrixEntryCLM j j).contDiff.comp_contDiffOn hBaseA).inv (fun z hz =>
      (hEll.1.trans_le (F05_elliptic_diagonal_lower hEll (hQ hz) j)).ne')
  have hNN (m : ℕ) : ∀ β : List (Option (RIdx n)), β.length = m → F05GoodList (some j) β →
      ContDiffOn ℝ k (fun z => F05RelDD X (F05GoodWord T β u) z (realVec j) (realVec j)) Q := by
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro β hLen hβ
      have hShort (δ : List (Option (RIdx n))) (hδLen : δ.length < β.length)
          (hGood : F05GoodList (some j) δ) :
          ContDiffOn ℝ k (F05RelDD X (F05GoodWord T δ u)) Q := by
        apply F05_bilinear_contDiff_of_components
        intro i l
        by_cases hPair : i = j ∧ l = j
        · rcases hPair with ⟨rfl,rfl⟩
          exact ih δ.length (by omega) δ rfl hGood
        · exact hOff δ hGood i l (by tauto)
      have hSource : ContDiffOn ℝ k (F05GoodSource T X a b f u β) Q := by
        apply (hFWord β hβ).add
        apply F05_contDiffOn_list_sum (commutatorSplits β)
        intro st hst
        have hGood := F05_commutator_splits_good hβ hst
        have hLower := commutatorSplits_lower_length β st hst
        exact F05_good_correction_contDiff X a b u st.1 st.2
          (hAWord st.1 hGood.1) (hBWord st.1 hGood.1)
          (hShort st.2 (by omega) hGood.2) (hGradient st.2 hGood.2)
      have hTime : ContDiffOn ℝ k (F05RelT (Ioc 0 T) (F05GoodWord T β u)) Q :=
        hJoint (none::β) ((F05GoodList_cons (some j) none β).mpr ⟨by trivial,hβ⟩)
      have hOffSum := F05_off_principal_contDiff j hBaseA (hOff β hβ)
      have hDrift := F05_drift_contraction_contDiff hBaseB (hGradient β hβ)
      have hRight := hInv.mul (((hTime.sub hSource).sub hOffSum).sub hDrift)
      apply hRight.congr
      intro z hz
      exact F05_linear_normal_recovery a b (F05GoodSource T X a b f u β) (F05GoodWord T β u)
        hEll (hQ hz) (hEquations β hβ z (hQ hz)) j
  intro β hβ
  apply F05_bilinear_contDiff_of_components
  intro i l
  by_cases hPair : i = j ∧ l = j
  · rcases hPair with ⟨rfl,rfl⟩
    exact hNN β.length β rfl hβ
  · exact hOff β hβ i l (by tauto)

end Yau.Proofs.F05Aux
