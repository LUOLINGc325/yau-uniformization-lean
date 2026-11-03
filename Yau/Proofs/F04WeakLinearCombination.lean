import Yau.LeafProofs.L16EnergyEquation
import Yau.LeafProofs.L16WeakL2Representation

open MeasureTheory Filter Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
namespace Yau.F04Proof
open Yau.Parabolic Yau.LeafProofs.L16Aux

theorem integral_sub_mul_of_memLp
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g w : α → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (hw : MemLp w 2 μ) :
    (∫ x, (f x - g x) * w x ∂μ) = (∫ x, f x * w x ∂μ) - ∫ x, g x * w x ∂μ := by
  have h₁ : Integrable (fun x => f x * w x) μ := hf.integrable_mul hw
  have h₂ : Integrable (fun x => g x * w x) μ := hg.integrable_mul hw
  calc
    _ = ∫ x, f x * w x - g x * w x ∂μ := by
      apply integral_congr_ae
      exact ae_of_all _ (fun x => by ring)
    _ = _ := integral_sub h₁ h₂

theorem weakGradient_sub_of_memLp
    {n : ℕ} {O : Set (Space n)} {I : Set ℝ}
    {u v : Point n → ℝ} {G H : Point n → RIdx n → ℝ}
    (hu : MemLp u 2 (productVolume O I)) (hv : MemLp v 2 (productVolume O I))
    (hG : ∀ i, MemLp (fun p => G p i) 2 (productVolume O I))
    (hH : ∀ i, MemLp (fun p => H p i) 2 (productVolume O I))
    (hWu : WeakGradient O I u G) (hWv : WeakGradient O I v H) :
    WeakGradient O I (fun p => u p - v p) (fun p i => G p i - H p i) := by
  intro φ hφ i
  have hφL : MemLp φ 2 (productVolume O I) := by
    rw [productVolume_eq_restrict]
    exact test_memLp hφ
  have hDL : MemLp (fun p => d (fun z => φ (z, p.2)) p.1 i) 2 (productVolume O I) := by
    rw [productVolume_eq_restrict]
    exact test_memLp (test_spatialDerivative hφ i)
  change (∫ p, (u p - v p) * d (fun z => φ (z, p.2)) p.1 i ∂productVolume O I) =
    -(∫ p, (G p i - H p i) * φ p ∂productVolume O I)
  rw [integral_sub_mul_of_memLp hu hv hDL, integral_sub_mul_of_memLp (hG i) (hH i) hφL,
    hWu φ hφ i, hWv φ hφ i]
  ring

theorem localEnergy_sub_of_memLp
    {n : ℕ} {O : Set (Space n)} {I : Set ℝ}
    {u v : Point n → ℝ} {G H : Point n → RIdx n → ℝ}
    (hu : MemLp u 2 (productVolume O I)) (hv : MemLp v 2 (productVolume O I))
    (hG : ∀ i, MemLp (fun p => G p i) 2 (productVolume O I))
    (hH : ∀ i, MemLp (fun p => H p i) 2 (productVolume O I))
    (hEu : LocalEnergy O I u G) (hEv : LocalEnergy O I v H) :
    LocalEnergy O I (fun p => u p - v p) (fun p i => G p i - H p i) := by
  refine ⟨weakGradient_sub_of_memLp hu hv hG hH hEu.1 hEv.1, ?_⟩
  intro V l r hV hVC hVO hI
  obtain ⟨huV, hGV⟩ := hEu.2 V l r hV hVC hVO hI
  obtain ⟨hvV, hHV⟩ := hEv.2 V l r hV hVC hVO hI
  exact ⟨huV.sub hvV, fun i => (hGV i).sub (hHV i)⟩

def weakTestExpression {n : ℕ} (a : Point n → Mat n) (b : Point n → RIdx n → ℝ)
    (u : Point n → ℝ) (G : Point n → RIdx n → ℝ) (φ : Point n → ℝ) (p : Point n) : ℝ :=
  -u p * deriv (fun t => φ (p.1, t)) p.2 +
    (∑ i, energyFlux a G p i * d (fun z => φ (z, p.2)) p.1 i) -
    (∑ j, energyDrift a b p j * G p j) * φ p

theorem weakTestExpression_integrable
    {n : ℕ} {O : Set (Space n)} {I : Set ℝ}
    {a : Point n → Mat n} {b : Point n → RIdx n → ℝ}
    {u : Point n → ℝ} {G : Point n → RIdx n → ℝ}
    (hu : MemLp u 2 (productVolume O I))
    (hP : ∀ i, MemLp (fun p => energyFlux a G p i) 2 (productVolume O I))
    (hR : MemLp (fun p => ∑ j, energyDrift a b p j * G p j) 2 (productVolume O I))
    {φ : Point n → ℝ} (hφ : Test (O ×ˢ I) φ) :
    Integrable (weakTestExpression a b u G φ) (productVolume O I) := by
  have hLp {ψ : Point n → ℝ} (hψ : Test (O ×ˢ I) ψ) : MemLp ψ 2 (productVolume O I) := by
    rw [productVolume_eq_restrict]
    exact test_memLp hψ
  let L := fun p : Point n => deriv (fun t => φ (p.1, t)) p.2
  let J := fun p : Point n => ∑ i, energyFlux a G p i * d (fun z => φ (z, p.2)) p.1 i
  let R := fun p : Point n => ∑ j, energyDrift a b p j * G p j
  have hUT : Integrable (u * L) (productVolume O I) := hu.integrable_mul (hLp (test_timeDerivative hφ))
  have hJT : Integrable J (productVolume O I) := integrable_finsetSum Finset.univ (fun i _ =>
    (hP i).integrable_mul (hLp (test_spatialDerivative hφ i)))
  have hRT : Integrable (R * φ) (productVolume O I) := hR.integrable_mul (hLp hφ)
  have he : weakTestExpression a b u G φ = (-(u * L) + J) - R * φ := by
    funext p
    change -u p * L p + J p - R p * φ p = -(u p * L p) + J p - R p * φ p
    ring
  rw [he]
  exact (hUT.neg.add hJT).sub hRT

theorem weakTestExpression_sub
    {n : ℕ} (a : Point n → Mat n) (b : Point n → RIdx n → ℝ)
    (u v : Point n → ℝ) (G H : Point n → RIdx n → ℝ) (φ : Point n → ℝ) (p : Point n) :
    weakTestExpression a b (fun q => u q - v q) (fun q i => G q i - H q i) φ p =
      weakTestExpression a b u G φ p - weakTestExpression a b v H φ p := by
  simp only [weakTestExpression, energyFlux, mul_sub, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul]
  ring

/-- Subtract two ACTUAL weak equations with the same source. All operator
 test integrals are integrable from actual value/flux/drift L2 data, and
 the source cancels exactly. No homogeneous equation is supplied. -/
theorem weakEquation_sub_same_source
    {n : ℕ} {O : Set (Space n)} {I : Set ℝ}
    {a : Point n → Mat n} {b : Point n → RIdx n → ℝ} {f u v : Point n → ℝ}
    {G H : Point n → RIdx n → ℝ}
    (hu : MemLp u 2 (productVolume O I)) (hv : MemLp v 2 (productVolume O I))
    (hPu : ∀ i, MemLp (fun p => energyFlux a G p i) 2 (productVolume O I))
    (hPv : ∀ i, MemLp (fun p => energyFlux a H p i) 2 (productVolume O I))
    (hRu : MemLp (fun p => ∑ j, energyDrift a b p j * G p j) 2 (productVolume O I))
    (hRv : MemLp (fun p => ∑ j, energyDrift a b p j * H p j) 2 (productVolume O I))
    (hEu : WeakEquation O I a b f u G) (hEv : WeakEquation O I a b f v H) :
    WeakEquation O I a b (fun _ => 0) (fun p => u p - v p) (fun p i => G p i - H p i) := by
  intro φ hφ
  have hU : (∫ p, weakTestExpression a b u G φ p ∂productVolume O I) = ∫ p, f p * φ p ∂productVolume O I := by
    simpa only [weakTestExpression, energyFlux, energyDrift, Finset.sum_mul] using hEu φ hφ
  have hV : (∫ p, weakTestExpression a b v H φ p ∂productVolume O I) = ∫ p, f p * φ p ∂productVolume O I := by
    simpa only [weakTestExpression, energyFlux, energyDrift, Finset.sum_mul] using hEv φ hφ
  have hZero : (∫ p, weakTestExpression a b (fun q => u q - v q) (fun q i => G q i - H q i) φ p
      ∂productVolume O I) = 0 := by
    calc
      _ = ∫ p, weakTestExpression a b u G φ p - weakTestExpression a b v H φ p ∂productVolume O I := by
        apply integral_congr_ae
        exact ae_of_all _ (weakTestExpression_sub a b u v G H φ)
      _ = _ := integral_sub (weakTestExpression_integrable hu hPu hRu hφ)
        (weakTestExpression_integrable hv hPv hRv hφ)
      _ = 0 := by rw [hU, hV, sub_self]
  simpa only [weakTestExpression, energyFlux, energyDrift, Finset.sum_mul, zero_mul, integral_zero] using hZero

end Yau.F04Proof
