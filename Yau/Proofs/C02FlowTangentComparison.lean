import Yau.Proofs.C02FlowTangentDerivative
import Yau.Proofs.C02ScalarExponentialComparison
import Yau.Proofs.C02MetricSlice

/-! A curvature bound on an actual flow cylinder controls the original
Hermitian quadratic form backwards over that same time interval. -/

noncomputable section
open Set
namespace Yau.Blueprint.C02Proof
variable {n : ℕ} {M : ComplexManifold n}

theorem kahlerRicciFlow_tangentNormSq_comparison
    (g : HermitianField M) (h : ℝ → HermitianField M) (hflow : IsKahlerRicciFlow g h)
    (a b K : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (x : M.Carrier) (v : TangentVector M x)
    (hCurv : ∀ t ∈ Icc a b, curvatureJetNorm (h t) 0 x ≤ K) :
    hermitianNormSq (h a x) v ≤
      Real.exp ((2 * n : ℕ) * K * (b - a)) * hermitianNormSq (h b x) v := by
  let F := fun t => hermitianNormSq (h t x) v
  let D := fun t => -centralRicciQuadratic (h t) x v
  have hI : Icc a b ⊆ Ici 0 := fun t ht => ha.trans ht.1
  have hd (t : ℝ) (ht : t ∈ Icc a b) :
      HasDerivWithinAt F (D t) (Ici 0) t :=
    kahlerRicciFlow_tangentNormSq_hasDerivWithinAt g h hflow x v t (hI ht)
  have hF : ContinuousOn F (Icc a b) := fun t ht =>
    ((hd t ht).mono hI).continuousWithinAt
  have hD (t : ℝ) (ht : t ∈ Ioo a b) : HasDerivAt F (D t) t := by
    exact ((hd t (Ioo_subset_Icc_self ht)).mono
      (Ioo_subset_Icc_self.trans hI)).hasDerivAt (isOpen_Ioo.mem_nhds ht)
  have hLower (t : ℝ) (ht : t ∈ Ioo a b) :
      -((2 * n : ℕ) * K) * F t ≤ D t := by
    have ht0 := hI (Ioo_subset_Icc_self ht)
    have hRic := centralRicciQuadratic_abs_le (h t)
      (metricFamilySmooth_slice hflow.2.1 ht0) (hflow.2.2.1 t ht0) x v
    have hBound : centralRicciQuadratic (h t) x v ≤
        (2 * n : ℕ) * K * F t := by
      apply (le_abs_self _).trans (hRic.trans ?_)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hCurv t (Ioo_subset_Icc_self ht))
          (Nat.cast_nonneg _)) (hermitianNormSq_nonneg _ _)
    dsimp only [D]
    linarith
  exact scalar_exponential_lower_comparison hab hF hD hLower

end Yau.Blueprint.C02Proof
