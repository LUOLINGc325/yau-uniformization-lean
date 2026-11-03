import Yau.LeafProofs.L16WeakEvolutionCalculus

open MeasureTheory Filter
open scoped Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

theorem weakGradientOn_weighted_finset_sum {n : ℕ} {Q : Set (Point n)}
    {ι : Type*} (s : Finset ι) (g u : ι → Point n → ℝ)
    (G : ι → Point n → Yau.RIdx n → ℝ)
    (hu : ∀ k ∈ s, MemLp (u k) 2 (volume.restrict Q))
    (hG : ∀ k ∈ s, ∀ i, MemLp (fun p => G k p i) 2 (volume.restrict Q))
    (hWeak : ∀ k ∈ s, WeakGradientOn Q (u k) (G k))
    (hg : ∀ k ∈ s, ContDiff ℝ ∞ (g k)) (hcg : ∀ k ∈ s, HasCompactSupport (g k)) :
    MemLp (fun p => ∑ k ∈ s, g k p*u k p) 2 (volume.restrict Q) ∧
      (∀ i, MemLp (fun p => ∑ k ∈ s,
        (g k p*G k p i+u k p*fderiv ℝ (g k) p (Yau.realVec i,0))) 2 (volume.restrict Q)) ∧
      WeakGradientOn Q (fun p => ∑ k ∈ s, g k p*u k p)
        (fun p i => ∑ k ∈ s, (g k p*G k p i+u k p*fderiv ℝ (g k) p (Yau.realVec i,0))) := by
  have hEach (k : ι) (hk : k ∈ s) :=
    weakGradientOn_smooth_compact_mul (hu k hk) (hG k hk) (hWeak k hk) (hg k hk) (hcg k hk)
  exact weakGradientOn_finset_sum s (fun k p => g k p*u k p)
    (fun k p i => g k p*G k p i+u k p*fderiv ℝ (g k) p (Yau.realVec i,0))
    (fun k hk => (hEach k hk).1) (fun k hk => (hEach k hk).2.1)
    (fun k hk => (hEach k hk).2.2)

theorem weakGradientOn_unique_ae {n : ℕ} {Q : Set (Point n)} (hQ : IsOpen Q)
    {u : Point n → ℝ} {G H : Point n → Yau.RIdx n → ℝ}
    (hG : ∀ i, MemLp (fun p => G p i) 2 (volume.restrict Q))
    (hH : ∀ i, MemLp (fun p => H p i) 2 (volume.restrict Q))
    (hWu : WeakGradientOn Q u G) (hWu' : WeakGradientOn Q u H) :
    ∀ᵐ p ∂volume.restrict Q, ∀ i, G p i = H p i := by
  rw [ae_all_iff]
  intro i
  apply ae_eq_of_test_integrals_eq hQ (hG i) (hH i)
  intro φ hφ
  have h := hWu φ hφ i
  have h' := hWu' φ hφ i
  linarith

end Yau.LeafProofs.L16Aux
