import Yau.Proofs.P06HodgeEnergyRepresentation
import Yau.LeafProofs.L19NormalContraction

noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace

namespace Yau.NodeProofs.P06Aux
open Yau Yau.LeafProofs.L03
variable {n : ℕ} {M : ComplexManifold n}

theorem hilbert_strong_image_limit_sharp
    {E Z : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
    (J : E →L[ℝ] Z) (w : ℕ → E) (f : Z) (a : ℕ → ℝ) (A : ℝ)
    (hstrong : Tendsto (fun j => J (w j)) atTop (𝓝 f))
    (hupper : ∀ j, ‖w j‖ ^ 2 - ‖J (w j)‖ ^ 2 ≤ a j) (ha : Tendsto a atTop (𝓝 A)) :
    ∃ v : E, J v = f ∧ ‖v‖ ^ 2 - ‖f‖ ^ 2 ≤ A := by
  let b (j : ℕ) := a j + ‖J (w j)‖ ^ 2
  let C : ℝ := A + ‖f‖ ^ 2
  have hb : Tendsto b atTop (𝓝 C) := ha.add (hstrong.norm.pow 2)
  have hnorm (j : ℕ) : ‖w j‖ ^ 2 ≤ b j := by
    dsimp only [b]
    linarith [hupper j]
  have hbe : ∀ᶠ j in atTop, b j < |C| + 1 :=
    hb.eventually (gt_mem_nhds (by linarith [le_abs_self C]))
  have hbound : ∀ᶠ j in atTop, ‖w j‖ ≤ |C| + 2 := by
    filter_upwards [hbe] with j hj
    have hn := hnorm j
    nlinarith [abs_nonneg C, norm_nonneg (w j)]
  obtain ⟨v, hev, hv⟩ := Yau.LeafProofs.L19Aux.hilbert_strong_image_limit
    J w f b C (|C| + 2) hbound hstrong (Eventually.of_forall hnorm) hb
  exact ⟨v, hev, by dsimp only [C] at hv; linarith⟩

theorem hodgeEnergy_norm_sub_eq (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (u : HodgeEnergySpace g μ hμ) :
    ‖u‖ ^ 2 - ‖hodgeEnergyValue g μ hμ u‖ ^ 2 = hodgeEnergy g μ hμ u := by
  rw [hodgeEnergy_norm_sq]
  ring

theorem hodgeEnergy_strong_image_limit_norm (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (w : ℕ → HodgeEnergySpace g μ hμ)
    (f : L2FormHilbert g μ 2) (a : ℕ → ℝ) (A : ℝ)
    (hstrong : Tendsto (fun j => hodgeEnergyValue g μ hμ (w j)) atTop (𝓝 f))
    (hupper : ∀ j, ‖w j‖ ^ 2 - ‖hodgeEnergyValue g μ hμ (w j)‖ ^ 2 ≤ a j)
    (ha : Tendsto a atTop (𝓝 A)) :
    ∃ v : HodgeEnergySpace g μ hμ, hodgeEnergyValue g μ hμ v = f ∧ ‖v‖ ^ 2 - ‖f‖ ^ 2 ≤ A :=
  @hilbert_strong_image_limit_sharp
    (HodgeEnergySpace g μ hμ) (L2FormHilbert g μ 2)
    (inferInstance : NormedAddCommGroup (HodgeEnergySpace g μ hμ))
    (inferInstance : InnerProductSpace ℝ (HodgeEnergySpace g μ hμ))
    (hodgeEnergyCompleteSpace g μ hμ)
    (inferInstance : NormedAddCommGroup (L2FormHilbert g μ 2))
    (inferInstance : InnerProductSpace ℝ (L2FormHilbert g μ 2))
    (inferInstance : CompleteSpace (L2FormHilbert g μ 2))
    (hodgeEnergyValue g μ hμ) w f a A hstrong hupper ha

/-- Strong L² convergence and a sharp convergent q upper bound produce
an element of the same original closed d/δ domain. Subtracting the actual
L² norm after the Hilbert weak limit preserves the q constant exactly. -/
theorem hodgeEnergy_strong_image_limit (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (w : ℕ → HodgeEnergySpace g μ hμ)
    (f : L2FormHilbert g μ 2) (a : ℕ → ℝ) (A : ℝ)
    (hstrong : Tendsto (fun j => hodgeEnergyValue g μ hμ (w j)) atTop (𝓝 f))
    (hupper : ∀ j, hodgeEnergy g μ hμ (w j) ≤ a j) (ha : Tendsto a atTop (𝓝 A)) :
    ∃ v : HodgeEnergySpace g μ hμ, hodgeEnergyValue g μ hμ v = f ∧ hodgeEnergy g μ hμ v ≤ A := by
  have hu (j : ℕ) : ‖w j‖ ^ 2 - ‖hodgeEnergyValue g μ hμ (w j)‖ ^ 2 ≤ a j := by
    rw [hodgeEnergy_norm_sub_eq]
    exact hupper j
  obtain ⟨v, hev, hv⟩ := hodgeEnergy_strong_image_limit_norm g μ hμ w f a A hstrong hu ha
  refine ⟨v, hev, ?_⟩
  rw [← hev, hodgeEnergy_norm_sub_eq] at hv
  exact hv

end Yau.NodeProofs.P06Aux
