import Yau.Proofs.F04ZeroPastIntegral
import Yau.Proofs.F04WeakRestriction

open MeasureTheory Filter Set
open scoped Topology ContDiff

noncomputable section

namespace Yau.F04Proof

open Yau.Parabolic Yau.LeafProofs.L16Aux

/-- The actual weak divergence equation crosses time zero without a boundary
 distribution when its original solution has linear initial growth. -/
theorem zeroPast_weakDivergence {n : ℕ} {O : Set (Space n)} (hO : MeasurableSet O)
    {l s K : ℝ} (hl : l ≤ 0) (hK : 0 ≤ K)
    {u R : Point n → ℝ} {P : Point n → Yau.RIdx n → ℝ}
    (hu : MemLp u 2 (productVolume O (Ioo 0 s)))
    (hP : ∀ i, MemLp (fun p => P p i) 2 (productVolume O (Ioo 0 s)))
    (hR : MemLp R 2 (productVolume O (Ioo 0 s)))
    (hGrowth : ∀ p ∈ O ×ˢ Ioo 0 s, |u p| ≤ K * p.2)
    (hWeak : WeakDivergenceEvolution O (Ioo 0 s) u P R) :
    WeakDivergenceEvolution O (Ioo l s) (zeroPast u)
      (fun p i => zeroPast (fun q => P q i) p) (zeroPast R) := by
  intro φ hφ
  have hφ2 : MemLp φ 2 (productVolume O (Ioo 0 s)) := by
    rw [productVolume_eq_restrict]
    exact (hφ.1.continuous.memLp_of_hasCompactSupport hφ.2.1).restrict _
  have htφ := test_timeDerivative hφ
  have htφ2 : MemLp (fun p => deriv (fun t => φ (p.1, t)) p.2) 2
      (productVolume O (Ioo 0 s)) := by
    rw [productVolume_eq_restrict]
    exact (htφ.1.continuous.memLp_of_hasCompactSupport htφ.2.1).restrict _
  have hxφ2 (i : Yau.RIdx n) : MemLp (fun p => d (fun x => φ (x, p.2)) p.1 i) 2
      (productVolume O (Ioo 0 s)) := by
    have hh := test_spatialDerivative hφ i
    rw [productVolume_eq_restrict]
    exact (hh.1.continuous.memLp_of_hasCompactSupport hh.2.1).restrict _
  let F : Point n → ℝ := fun p => -(u p * deriv (fun t => φ (p.1, t)) p.2) +
    (∑ i, P p i * d (fun x => φ (x, p.2)) p.1 i) - R p * φ p
  have hF : Integrable F (productVolume O (Ioo 0 s)) :=
    ((hu.integrable_mul htφ2).neg.add
      (integrable_finsetSum _ (fun i _ => (hP i).integrable_mul (hxφ2 i)))).sub
        (hR.integrable_mul hφ2)
  have hMain := tendsto_integral_zeroPastCutoff hO hF
  have hError := tendsto_integral_zeroPastCutoff_error hO hK hu hGrowth hφ.1 hφ.2.1
  have hEq (j : ℕ) :
      (∫ p, F p * zeroPastCutoff (1 / ((j : ℝ) + 1)) p.2 ∂productVolume O (Ioo 0 s)) =
      ∫ p, (deriv (zeroPastCutoff (1 / ((j : ℝ) + 1))) p.2 * u p) * φ p
        ∂productVolume O (Ioo 0 s) := by
    let δ : ℝ := 1 / ((j : ℝ) + 1)
    have hδ : 0 < δ := by dsimp only [δ]; positivity
    have hh := hWeak _ (zeroPastCutoff_test hδ hφ)
    change (∫ p, -u p * deriv (fun t => φ (p.1, t) * zeroPastCutoff δ t) p.2 +
      (∑ i, P p i * d (fun x => φ (x, p.2) * zeroPastCutoff δ p.2) p.1 i) -
        R p * (φ p * zeroPastCutoff δ p.2) ∂productVolume O (Ioo 0 s)) = 0 at hh
    simp_rw [zeroPastCutoff_test_time_deriv hφ.1, zeroPastCutoff_test_space_deriv hφ.1] at hh
    have he : (fun p => -u p *
        (deriv (fun t => φ (p.1, t)) p.2 * zeroPastCutoff δ p.2 + φ p * deriv (zeroPastCutoff δ) p.2) +
        (∑ i, P p i * (d (fun x => φ (x, p.2)) p.1 i * zeroPastCutoff δ p.2)) -
          R p * (φ p * zeroPastCutoff δ p.2)) =
        fun p => F p * zeroPastCutoff δ p.2 - (deriv (zeroPastCutoff δ) p.2 * u p) * φ p := by
      funext p
      have hsum : (∑ i, P p i * (d (fun x => φ (x, p.2)) p.1 i * zeroPastCutoff δ p.2)) =
          (∑ i, P p i * d (fun x => φ (x, p.2)) p.1 i) * zeroPastCutoff δ p.2 := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        ring
      dsimp only [F]
      rw [hsum]
      ring
    rw [he, integral_sub (integrable_mul_zeroPastCutoff hF δ)
      (integrable_zeroPastCutoff_error hu hφ.1 hφ.2.1 δ)] at hh
    exact sub_eq_zero.mp hh
  have hLimit : (∫ p, F p ∂productVolume O (Ioo 0 s)) = 0 :=
    tendsto_nhds_unique hMain (hError.congr' (Eventually.of_forall (fun j => (hEq j).symm)))
  have he : (fun p => -zeroPast u p * deriv (fun t => φ (p.1, t)) p.2 +
      (∑ i, zeroPast (fun q => P q i) p * d (fun x => φ (x, p.2)) p.1 i) - zeroPast R p * φ p) =
      zeroPast F := by
    funext p
    by_cases hp : 0 < p.2 <;> simp [zeroPast, hp, F, neg_mul]
  change (∫ p, -zeroPast u p * deriv (fun t => φ (p.1, t)) p.2 +
    (∑ i, zeroPast (fun q => P q i) p * d (fun x => φ (x, p.2)) p.1 i) - zeroPast R p * φ p
      ∂productVolume O (Ioo l s)) = 0
  rw [he]
  have hz : (∫ p, zeroPast F p ∂productVolume O (Ioo l s)) =
      ∫ p, F p ∂productVolume O (Ioo 0 s) := by
    simpa only [mul_one] using zeroPast_pairing_integral O hl F (fun _ => 1)
  exact hz.trans hLimit

end Yau.F04Proof
