import Yau.Proofs.C02JetProducts

noncomputable section
open scoped ContDiff
namespace Yau.Blueprint.C02Proof
variable {D E F G : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem norm_iteratedFDeriv_bilinear_le (L : E →L[ℝ] F →L[ℝ] G)
    (hL : ‖L‖ ≤ 1) {f : D → E} {g : D → F}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : D) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun y => L (f y) (g y)) x‖ ≤
      binomialJetProduct (fun i => ‖iteratedFDeriv ℝ i f x‖)
        (fun i => ‖iteratedFDeriv ℝ i g x‖) m := by
  have h := L.norm_iteratedFDerivWithin_le_of_bilinear hf.contDiffOn hg.contDiffOn
    uniqueDiffOn_univ (Set.mem_univ x) (show (m : ℕ∞ω) ≤ ∞ by simp)
  simp only [iteratedFDerivWithin_univ] at h
  have hsum : 0 ≤ binomialJetProduct (fun i => ‖iteratedFDeriv ℝ i f x‖)
      (fun i => ‖iteratedFDeriv ℝ i g x‖) m :=
    binomialJetProduct_nonneg (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) m
  have h' : ‖iteratedFDeriv ℝ m (fun y => L (f y) (g y)) x‖ ≤
      ‖L‖ * binomialJetProduct (fun i => ‖iteratedFDeriv ℝ i f x‖)
        (fun i => ‖iteratedFDeriv ℝ i g x‖) m := by
    simpa only [binomialJetProduct] using h
  exact h'.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hL hsum)

end Yau.Blueprint.C02Proof
