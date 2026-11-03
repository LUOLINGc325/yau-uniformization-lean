import Yau.Proofs.F04ChartSpacetimeTestEntries
import Yau.LeafProofs.L16EnergyEquation

open MeasureTheory Filter Set
open scoped Topology ContDiff
noncomputable section
namespace Yau.F04Proof
open Yau.Parabolic Yau.LeafProofs.L16Aux

/-- An actual chart variational identity gives the literal nondivergence
 weak equation. The coefficient drift is computed, and the L2 hypotheses
 prove every integral needed to separate the source term. -/
theorem weakEquation_of_chart_test_integrals
    {n : ℕ} {O : Set (Space n)} (hO : IsOpen O) {I : Set ℝ} (hI : IsOpen I)
    {a : Point n → Mat n}
    (ha : ∀ i j, ContDiffOn ℝ 1 (fun p => a p i j) (O ×ˢ I))
    {u F : Point n → ℝ} {G : Point n → RIdx n → ℝ}
    (hu : MemLp u 2 (productVolume O I))
    (hG : ∀ i, MemLp (fun p => G p i) 2 (productVolume O I))
    (hF : MemLp F 2 (productVolume O I))
    (hTest : ∀ φ : Point n → ℝ, Test (O ×ˢ I) φ →
      (∫ p, u p * deriv (fun t => φ (p.1, t)) p.2 -
        (∑ i, ∑ j, G p j * chartWeakTestEntry (fun z => a (z, p.2)) (fun z => φ (z, p.2)) i j p.1) +
        F p * φ p ∂productVolume O I) = 0) :
    WeakEquation O I a (fun _ _ => 0) F u G := by
  intro φ hφ
  let H := fun p => ∑ i, ∑ j, G p j *
    chartWeakTestEntry (fun z => a (z, p.2)) (fun z => φ (z, p.2)) i j p.1
  have hφL : MemLp φ 2 (productVolume O I) := by
    rw [productVolume_eq_restrict]
    exact (hφ.1.continuous.memLp_of_hasCompactSupport hφ.2.1).restrict _
  have hφt := test_timeDerivative hφ
  have hφtL : MemLp (fun p => deriv (fun t => φ (p.1, t)) p.2) 2 (productVolume O I) := by
    rw [productVolume_eq_restrict]
    exact (hφt.1.continuous.memLp_of_hasCompactSupport hφt.2.1).restrict _
  have hUT := hu.integrable_mul hφtL
  have hHT : Integrable H (productVolume O I) :=
    integrable_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ
      (fun j _ => (hG j).integrable_mul (chartWeakTestEntry_spacetime_memLp hO hI ha hφ i j)))
  have hFT : Integrable (fun p => F p * φ p) (productVolume O I) := hF.integrable_mul hφL
  have hOp : Integrable (fun p => -u p * deriv (fun t => φ (p.1, t)) p.2 + H p) (productVolume O I) := by
    have he : (fun p => -u p * deriv (fun t => φ (p.1, t)) p.2 + H p) =
        -(u * fun p => deriv (fun t => φ (p.1, t)) p.2) + H := by
      funext p
      change -u p * deriv (fun t => φ (p.1, t)) p.2 + H p =
        -(u p * deriv (fun t => φ (p.1, t)) p.2) + H p
      ring
    rw [he]
    exact hUT.neg.add hHT
  have hHEq (p : Point n) : H p =
      (∑ i, ∑ j, a p i j * G p j * d (fun x => φ (x, p.2)) p.1 i) +
      (∑ j, ∑ i, d (fun x => a (x, p.2) i j) p.1 i * G p j * φ p) := by
    simp only [H, chartWeakTestEntry, mul_add, Finset.sum_add_distrib]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      change G p j * (a p i j * d (fun x => φ (x, p.2)) p.1 i) = _
      ring
    · rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      change G p j * (d (fun x => a (x, p.2) i j) p.1 i * φ p) = _
      ring
  have hAlg (p : Point n) :
      -u p * deriv (fun t => φ (p.1, t)) p.2 +
        (∑ i, ∑ j, a p i j * G p j * d (fun x => φ (x, p.2)) p.1 i) -
        (∑ j, ((0 : ℝ) - ∑ i, d (fun x => a (x, p.2) i j) p.1 i) * G p j * φ p) =
      -u p * deriv (fun t => φ (p.1, t)) p.2 + H p := by
    rw [hHEq]
    simp only [zero_sub, neg_mul, Finset.sum_neg_distrib, Finset.sum_mul, sub_neg_eq_add]
    ring
  have hT : (∫ p, u p * deriv (fun t => φ (p.1, t)) p.2 - H p + F p * φ p
      ∂productVolume O I) = 0 := hTest φ hφ
  have hZero : (∫ p, (-u p * deriv (fun t => φ (p.1, t)) p.2 + H p) - F p * φ p
      ∂productVolume O I) = 0 := by
    calc
      _ = -(∫ p, u p * deriv (fun t => φ (p.1, t)) p.2 - H p + F p * φ p
          ∂productVolume O I) := by
        rw [← integral_neg]
        apply integral_congr_ae
        exact ae_of_all _ (fun p => by ring)
      _ = 0 := by rw [hT, neg_zero]
  rw [integral_sub hOp hFT] at hZero
  change (∫ p, -u p * deriv (fun t => φ (p.1, t)) p.2 +
    (∑ i, ∑ j, a p i j * G p j * d (fun x => φ (x, p.2)) p.1 i) -
    (∑ j, ((0 : ℝ) - ∑ i, d (fun x => a (x, p.2) i j) p.1 i) * G p j * φ p)
      ∂productVolume O I) = _
  simpa only [hAlg] using sub_eq_zero.mp hZero

end Yau.F04Proof
