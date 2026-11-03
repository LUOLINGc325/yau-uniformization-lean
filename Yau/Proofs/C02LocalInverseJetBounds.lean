import Yau.Proofs.C02LocalInverseFieldJets
import Yau.Proofs.C02InverseJetDomination

noncomputable section
open Set
open scoped ContDiff
namespace Yau.Blueprint.C02Proof
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem actualInverseField_jet_majorant_on {O : Set E} (hO : IsOpen O)
    {B : E → E →L[ℝ] E} (hB : ContDiffOn ℝ ∞ B O)
    (hInv : ∀ y ∈ O, (B y).IsInvertible) {x : E} (hx : x ∈ O)
    (b : ℕ → ℝ) (hb : ∀ i, 0 ≤ b i)
    (hbound : ∀ i, ‖iteratedFDeriv ℝ i B x‖ ≤ b i)
    (h0 : ‖(B x).inverse‖ ≤ 2) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun y => (B y).inverse) x‖ ≤ inverseJetMajorant b m := by
  let a := fun i => ‖iteratedFDeriv ℝ i (fun y => (B y).inverse) x‖
  have hInitial : a 0 ≤ 2 := by simpa only [a, norm_iteratedFDeriv_zero] using h0
  apply inverseJetMajorant_dominates a b (fun i => norm_nonneg _) hb hInitial _ m
  intro k
  apply (actualInverseField_jet_norm_on_le hO hB hInv hx k).trans
  apply binomialJetProduct_mono k
  · intro j hj
    apply binomialJetProduct_mono j
    · intro i hi; exact le_refl _
    · intro i hi; exact hbound (i + 1)
    · intro i hi; exact norm_nonneg _
    · intro i hi; exact hb (i + 1)
  · intro i hi; exact le_refl _
  · intro j hj
    exact binomialJetProduct_nonneg (fun i => norm_nonneg _) (fun i => norm_nonneg _) j
  · intro i hi; exact norm_nonneg _

end Yau.Blueprint.C02Proof
