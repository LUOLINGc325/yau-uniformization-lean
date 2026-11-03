import Yau.Proofs.P07Affine
import Yau.Blueprint.HeatSmoothing

/-! The two genuine positive translates of a unit-range heat solution
supply its missing trace and gradient estimates through original L19. -/
noncomputable section
open Set
open scoped Topology ComplexOrder
namespace Yau.NodeProofs.P07Aux
open Yau Yau.Blueprint Yau.LeafProofs.L19Aux Yau.LeafProofs.L18Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem continuousInitialHeat_positive_affine (g : SmoothMetric M)
    (f : M.Carrier → ℝ) (U : ℝ → M.Carrier → ℝ)
    (hU : IsContinuousInitialScalarHeat g.form f U) (a b : ℝ)
    (hpos : ∀ x t, 0 < t → 0 < a * U t x + b) :
    Yau.LeafCandidates.PositiveHeatSolution g.form (fun x t => a * U t x + b) := by
  refine ⟨?_, ?_⟩
  · intro x
    exact (contDiffOn_const.mul (hU.2.1 x)).add contDiffOn_const
  · intro x t ht
    refine ⟨hpos x t ht, ?_⟩
    rw [laplacian_affine g.form (smoothSpaceTime_slice hU.2.1 ht) a b x]
    exact (((hU.2.2.1 x t ht).const_mul a).add_const b).deriv

theorem continuousInitialHeat_affine_liYau (X : KahlerManifold n)
    (hRic : ∀ x, (ricci X.metric.form x).PosSemidef)
    (f : Pt X → ℝ) (U : ℝ → Pt X → ℝ)
    (hU : IsContinuousInitialScalarHeat X.metric.form f U) (a b : ℝ)
    (hpos : ∀ x t, 0 < t → 0 < a * U t x + b)
    (x : Pt X) {t : ℝ} (ht : 0 < t) :
    a ^ 2 * gradNormSq X.metric.form (U t) x / (a * U t x + b) ^ 2 -
      a * laplacian X.metric.form (U t) x / (a * U t x + b) ≤ (n : ℝ) / t := by
  have hv := continuousInitialHeat_positive_affine X.metric f U hU a b hpos
  have hly := liYauDifferential n X.manifold X.metric X.complete_metric X.kahler_metric hRic
    (fun y s => a * U s y + b) hv x t ht
  rw [gradNormSq_log X.metric.form (positiveHeatSolution_slice X.metric.form hv ht)
    (fun y => hpos y t ht) x,
    (positiveHeatSolution_log_hasDerivAt X.metric.form hv x ht).deriv,
    gradNormSq_affine X.metric.form (smoothSpaceTime_slice hU.2.1 ht) a b x,
    laplacian_affine X.metric.form (smoothSpaceTime_slice hU.2.1 ht) a b x] at hly
  exact hly

theorem two_positive_translates_bounds {G d p m N : ℝ}
    (hG : 0 ≤ G) (hN : 0 ≤ N) (hp : p ∈ Icc (1 : ℝ) 2) (hm : m ∈ Icc (1 : ℝ) 2)
    (hP : G / p ^ 2 - d / p ≤ N) (hM : G / m ^ 2 + d / m ≤ N) :
    |d| ≤ 2 * N ∧ G ≤ 12 * N := by
  have hp0 : 0 < p := by linarith [hp.1]
  have hm0 : 0 < m := by linarith [hm.1]
  have hdlo : -d ≤ N * p := (div_le_iff₀ hp0).mp (by
    have hh := div_nonneg hG (sq_nonneg p)
    have he : (-d) / p = -(d / p) := neg_div _ _
    rw [he]
    linarith)
  have hdhi : d ≤ N * m := (div_le_iff₀ hm0).mp (by
    linarith [div_nonneg hG (sq_nonneg m)])
  have hd : |d| ≤ 2 * N := abs_le.mpr ⟨by nlinarith [hp.2], by nlinarith [hm.2]⟩
  have hdP : d / p ≤ 2 * N := (div_le_iff₀ hp0).mpr (by
    nlinarith [hp.1, (abs_le.mp hd).2])
  have hgp : G ≤ (3 * N) * p ^ 2 := (div_le_iff₀ (sq_pos_of_pos hp0)).mp (by linarith)
  refine ⟨hd, ?_⟩
  have hp2 : p ^ 2 ≤ 4 := by nlinarith [hp.1, hp.2]
  nlinarith

theorem continuousInitialHeat_derivative_bounds (X : KahlerManifold n)
    (hRic : ∀ x, (ricci X.metric.form x).PosSemidef)
    (f : Pt X → ℝ) (U : ℝ → Pt X → ℝ)
    (hU : IsContinuousInitialScalarHeat X.metric.form f U)
    (h01 : ∀ x t, 0 < t → U t x ∈ Icc (0 : ℝ) 1)
    (x : Pt X) {t : ℝ} (ht : 0 < t) :
    |laplacian X.metric.form (U t) x| ≤ 2 * (n : ℝ) / t ∧
      gradNormSq X.metric.form (U t) x ≤ 12 * (n : ℝ) / t := by
  have hp := continuousInitialHeat_affine_liYau X hRic f U hU 1 1
    (fun y s hs => by linarith [(h01 y s hs).1]) x ht
  have hm := continuousInitialHeat_affine_liYau X hRic f U hU (-1) 2
    (fun y s hs => by linarith [(h01 y s hs).2]) x ht
  simp only [one_pow, one_mul, neg_one_sq, neg_one_mul, neg_div, sub_neg_eq_add] at hp hm
  have hh := two_positive_translates_bounds
    (gradNormSq_nonnegative X.metric.form (smoothSpaceTime_slice hU.2.1 ht) x)
    (div_nonneg (Nat.cast_nonneg n) ht.le)
    (show U t x + 1 ∈ Icc (1 : ℝ) 2 from ⟨by linarith [(h01 x t ht).1], by linarith [(h01 x t ht).2]⟩)
    (show -U t x + 2 ∈ Icc (1 : ℝ) 2 from ⟨by linarith [(h01 x t ht).2], by linarith [(h01 x t ht).1]⟩)
    hp hm
  simpa only [mul_div_assoc] using hh

end Yau.NodeProofs.P07Aux
