import Yau.Proofs.C02BilinearJetBound

/-! Bilinear jet estimates on an actual open smooth domain. A separate
finite derivative order is used each time; no common infinite-order
neighborhood is inferred from a ContDiffAt infinity germ. -/

noncomputable section
open Set
open scoped ContDiff
namespace Yau.Blueprint.C02Proof
variable {D E F G : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem norm_iteratedFDeriv_bilinearOn_le (L : E →L[ℝ] F →L[ℝ] G) (hL : ‖L‖ ≤ 1)
    {O : Set D} (hO : IsOpen O) {f : D → E} {g : D → F}
    (hf : ContDiffOn ℝ ∞ f O) (hg : ContDiffOn ℝ ∞ g O) {x : D} (hx : x ∈ O) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun y => L (f y) (g y)) x‖ ≤
      binomialJetProduct (fun i => ‖iteratedFDeriv ℝ i f x‖) (fun i => ‖iteratedFDeriv ℝ i g x‖) m := by
  have h := L.norm_iteratedFDerivWithin_le_of_bilinear hf hg hO.uniqueDiffOn hx
    (show (m : ℕ∞ω) ≤ ∞ by simp)
  rw [iteratedFDerivWithin_of_isOpen m hO hx] at h
  have hfe (i : ℕ) : iteratedFDerivWithin ℝ i f O x = iteratedFDeriv ℝ i f x :=
    iteratedFDerivWithin_of_isOpen i hO hx
  have hge (i : ℕ) : iteratedFDerivWithin ℝ i g O x = iteratedFDeriv ℝ i g x :=
    iteratedFDerivWithin_of_isOpen i hO hx
  simp_rw [hfe, hge] at h
  have hsum := binomialJetProduct_nonneg (fun i => norm_nonneg (iteratedFDeriv ℝ i f x))
    (fun i => norm_nonneg (iteratedFDeriv ℝ i g x)) m
  have h' : ‖iteratedFDeriv ℝ m (fun y => L (f y) (g y)) x‖ ≤
      ‖L‖ * binomialJetProduct (fun i => ‖iteratedFDeriv ℝ i f x‖)
        (fun i => ‖iteratedFDeriv ℝ i g x‖) m := by simpa only [binomialJetProduct] using h
  exact h'.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hL hsum)

end Yau.Blueprint.C02Proof
