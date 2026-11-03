import Yau.Proofs.C02BilinearJetBound
import Yau.Proofs.C02JetProductBounds

/-! Product bounds use smoothness on the actual open chart domain;
they do not extend the chart through its boundary. -/

noncomputable section
open Set
open scoped ContDiff
namespace Yau.Blueprint.C02Proof
variable {D E F G : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem norm_iteratedFDeriv_bilinear_on_le
    (L : E →L[ℝ] F →L[ℝ] G) (hL : ‖L‖ ≤ 1)
    {O : Set D} (hO : IsOpen O) {f : D → E} {g : D → F}
    (hf : ContDiffOn ℝ ∞ f O) (hg : ContDiffOn ℝ ∞ g O)
    {x : D} (hx : x ∈ O) (m : ℕ) (a b : ℕ → ℝ)
    (ha : ∀ i ≤ m, ‖iteratedFDeriv ℝ i f x‖ ≤ a i)
    (hb : ∀ i ≤ m, ‖iteratedFDeriv ℝ i g x‖ ≤ b i)
    (ha0 : ∀ i, 0 ≤ a i) (hb0 : ∀ i, 0 ≤ b i) :
    ‖iteratedFDeriv ℝ m (fun y => L (f y) (g y)) x‖ ≤ binomialJetProduct a b m := by
  have h := L.norm_iteratedFDerivWithin_le_of_bilinear hf hg hO.uniqueDiffOn hx
    (show (m : ℕ∞ω) ≤ ∞ by simp)
  simp only [iteratedFDerivWithin_of_isOpen _ hO hx] at h
  have hProd := binomialJetProduct_mono m ha hb (fun i hi => norm_nonneg _) (fun i hi => hb0 i)
  have hNonneg := binomialJetProduct_nonneg (fun i => norm_nonneg (iteratedFDeriv ℝ i f x))
    (fun i => norm_nonneg (iteratedFDeriv ℝ i g x)) m
  have h' : ‖iteratedFDeriv ℝ m (fun y => L (f y) (g y)) x‖ ≤
      ‖L‖ * binomialJetProduct (fun i => ‖iteratedFDeriv ℝ i f x‖)
        (fun i => ‖iteratedFDeriv ℝ i g x‖) m := by
    simpa only [binomialJetProduct, mul_assoc] using h
  exact h'.trans (((mul_le_mul_of_nonneg_right hL hNonneg).trans_eq (one_mul _)).trans hProd)

theorem norm_iteratedFDeriv_linear_on_le
    (L : E →L[ℝ] F) (hL : ‖L‖ ≤ 1)
    {O : Set D} (hO : IsOpen O) {f : D → E}
    (hf : ContDiffOn ℝ ∞ f O) {x : D} (hx : x ∈ O) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (L ∘ f) x‖ ≤ ‖iteratedFDeriv ℝ m f x‖ := by
  have h := L.norm_iteratedFDeriv_comp_left
    (hf.contDiffAt (hO.mem_nhds hx)) (show (m : ℕ∞ω) ≤ ∞ by simp)
  exact h.trans ((mul_le_mul_of_nonneg_right hL (norm_nonneg _)).trans_eq (one_mul _))

end Yau.Blueprint.C02Proof
