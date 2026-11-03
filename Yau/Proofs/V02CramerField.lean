import Yau.Proofs.V02SpanningCorona
import Yau.Proofs.V03FrameSmooth

/-! Division-free coefficients in the actual global spanning fields.
The exact first field is reconstructed through the original immersion. -/

open scoped Topology ContDiff Manifold Matrix

noncomputable section
namespace Yau.Blueprint.V02Proof
open Yau Yau.Blueprint

theorem adjugate_entry_contDiffOn
    {P ι : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
    [Fintype ι] [DecidableEq ι] {S : Set P} {A : P → Matrix ι ι ℂ}
    (hA : ∀ i j, ContDiffOn ℂ ∞ (fun z => A z i j) S) (i j : ι) :
    ContDiffOn ℂ ∞ (fun z => (A z).adjugate i j) S := by
  simp_rw [Matrix.adjugate_apply, Matrix.det_apply']
  apply ContDiffOn.sum
  intro σ _
  apply contDiffOn_const.mul
  apply contDiffOn_prod
  intro k _
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact contDiffOn_const
  · exact hA _ _

theorem tupleCramer_entry_contDiffOn
    {P ι κ β : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Fintype β] [DecidableEq β]
    {S : Set P} {A : P → Matrix κ β ℂ} {Y : P → κ → ℂ}
    (hA : ∀ i j, ContDiffOn ℂ ∞ (fun z => A z i j) S)
    (hY : ∀ i, ContDiffOn ℂ ∞ (fun z => Y z i) S)
    (r : ι → κ) (c : ι → β) (j : β) :
    ContDiffOn ℂ ∞ (fun z => tupleCramer (A z) r c (Y z) j) S := by
  unfold tupleCramer tuplePush
  apply ContDiffOn.sum
  intro i _
  split_ifs
  · simp only [Matrix.mulVec, dotProduct, Function.comp_def]
    exact ContDiffOn.sum (fun k _ =>
      (adjugate_entry_contDiffOn (fun i j => hA (r i) (c j)) i k).mul (hY (r k)))
  · exact contDiffOn_const

variable {n q b : ℕ} {M : ComplexManifold n}

def spanningFirstCoefficients (G : CotangentPoint M → ComplexVector q)
    (Z : Fin b → CotangentPoint M → CotangentIndex n → ℂ)
    (f : ℂ → CotangentPoint M) (E : ℂ → CotangentMatrix n)
    (l : ℂ → CotangentIndex n → ℂ) (α : ℂ → ℂ) (ζ : ℂ) : Fin b → ℂ :=
  ∑ k : SpanningMinorIndex n q b, (α ζ * spanningCorona G Z f k ζ) •
    tupleCramer (spanningAmbientMatrix G Z (f ζ)) k.1 k.2
      (ambientFrame G f E ζ *ᵥ l ζ)

theorem spanningFirstCoefficients_contDiffOn
    {G : CotangentPoint M → ComplexVector q} (hG : CotangentImmersion G)
    {Z : Fin b → CotangentPoint M → CotangentIndex n → ℂ}
    (hZ : ∀ k x i, DifferentiableOn ℂ
      (fun z => (cotangentTransition (chartInv x z.1) x (cotangentChartInv x z) *ᵥ
        Z k (cotangentChartInv x z)) i) (cotangentTarget x))
    (hspan : ∀ y, Submodule.span ℂ (Set.range (fun k => Z k y)) = ⊤)
    {f : ℂ → CotangentPoint M} {E : ℂ → CotangentMatrix n}
    (hE : IsDiscFrame f E) {l : ℂ → CotangentIndex n → ℂ}
    (hl : HolomorphicColumn l) {α : ℂ → ℂ}
    (hα : ContDiffOn ℂ ∞ α (Metric.closedBall (0 : ℂ) 1)) (j : Fin b) :
    ContDiffOn ℂ ∞ (fun ζ => spanningFirstCoefficients G Z f E l α ζ j)
      (Metric.closedBall (0 : ℂ) 1) := by
  classical
  have hA (a : Fin q) (k : Fin b) : ContDiffOn ℂ ∞
      (fun ζ => spanningAmbientMatrix G Z (f ζ) a k) (Metric.closedBall (0 : ℂ) 1) :=
    cotangentDisc_comp_complex_smooth
      (F := fun y => spanningAmbientMatrix G Z y a k) hE.2.1
      (fun x => spanningAmbient_entry_chart_contDiffOn hG.1 hZ x a k)
  have hY (a : Fin q) : ContDiffOn ℂ ∞
      (fun ζ => (ambientFrame G f E ζ *ᵥ l ζ) a) (Metric.closedBall (0 : ℂ) 1) := by
    simpa only [Matrix.mulVec, dotProduct] using
      (ContDiffOn.sum (s := Finset.univ)
        (fun i _ => (V03Proof.ambientFrame_entry_contDiffOn hE hG.1 a i).mul (hl i)))
  simp only [spanningFirstCoefficients, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact ContDiffOn.sum (fun k _ =>
    (hα.mul (spanningCorona_contDiffOn hG hZ hspan hE.2.1 k)).mul
      (tupleCramer_entry_contDiffOn hA hY k.1 k.2 j))

theorem spanningFirstCoefficients_field
    {G : CotangentPoint M → ComplexVector q} (hG : CotangentImmersion G)
    {Z : Fin b → CotangentPoint M → CotangentIndex n → ℂ}
    (hZ : ∀ k x i, DifferentiableOn ℂ
      (fun z => (cotangentTransition (chartInv x z.1) x (cotangentChartInv x z) *ᵥ
        Z k (cotangentChartInv x z)) i) (cotangentTarget x))
    (hspan : ∀ y, Submodule.span ℂ (Set.range (fun k => Z k y)) = ⊤)
    {f : ℂ → CotangentPoint M} (hf : CotangentDisc f)
    (E : ℂ → CotangentMatrix n) (l : ℂ → CotangentIndex n → ℂ)
    (α : ℂ → ℂ) {ζ : ℂ} (hζ : ζ ∈ Metric.closedBall (0 : ℂ) 1) :
    fieldMatrix Z (f ζ) *ᵥ spanningFirstCoefficients G Z f E l α ζ =
      α ζ • (E ζ *ᵥ l ζ) := by
  classical
  apply V03Proof.cotangentDG_mulVec_injective hG (f ζ)
  rw [Matrix.mulVec_mulVec]
  change spanningAmbientMatrix G Z (f ζ) *ᵥ spanningFirstCoefficients G Z f E l α ζ = _
  have heq : ambientFrame G f E ζ *ᵥ l ζ =
      cotangentDG G (f ζ).1 (f ζ) *ᵥ (E ζ *ᵥ l ζ) := by
    rw [ambientFrame, Matrix.mulVec_mulVec]
  have hc (k : SpanningMinorIndex n q b) := mulVec_tupleCramer
    (cotangentDG G (f ζ).1 (f ζ)) (fieldMatrix Z (f ζ)) k.1 k.2 (E ζ *ᵥ l ζ)
  have h := combine_cramer_coefficients (Λ := SpanningMinorIndex n q b)
    (spanningAmbientMatrix G Z (f ζ))
    (ambientFrame G f E ζ *ᵥ l ζ) (fun k => spanningMinor G Z k (f ζ))
    (fun k => spanningCorona G Z f k ζ)
    (fun k => tupleCramer (spanningAmbientMatrix G Z (f ζ)) k.1 k.2
      (ambientFrame G f E ζ *ᵥ l ζ))
    (fun k => by simpa only [heq, spanningAmbientMatrix, spanningMinor] using hc k)
    (spanningCorona_sum_eq_one hG hZ hspan hf hζ) (α ζ)
  simpa only [spanningFirstCoefficients, heq, Matrix.mulVec_smul] using h

end Yau.Blueprint.V02Proof
