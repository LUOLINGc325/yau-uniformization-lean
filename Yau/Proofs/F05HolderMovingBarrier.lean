import Yau.LeafProofs.L16ExpBoundaryComparison
import Yau.LeafProofs.L16ExpBoundaryInitial

/-! A time-affine addition to the native stationary comparison. This uses
only open-top interior derivatives and closed-cylinder continuity. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux Yau.LeafProofs.L16ExpBoundaryAux
variable {n : ℕ}

theorem F05_moving_barrier_upper {O : Set (Space n)} {T lam upper Ht : ℝ}
    {a : Point n → Mat n} {b : Point n → RIdx n → ℝ}
    {u : Point n → ℝ} {W : Space n → ℝ}
    (hO : IsOpen O) (hcompact : IsCompact (closure O)) (hT : 0 < T)
    (hc : ContinuousOn u (cylinder (closure O) 0 T))
    (hs : ∀ z ∈ O ×ˢ Ioo 0 T, ContDiffAt ℝ 2 (fun x => u (x,z.2)) z.1)
    (ht : ∀ z ∈ O ×ˢ Ioo 0 T, DifferentiableAt ℝ (fun t => u (z.1,t)) z.2)
    (he : Elliptic (O ×ˢ Ioo 0 T) a lam upper)
    (hWc : ContinuousOn W (closure O)) (hWs : ∀ x ∈ O, ContDiffAt ℝ 2 W x)
    (hi : ∀ x ∈ closure O, u (x,0) ≤ W x)
    (hl : ∀ x ∈ frontier O, ∀ t ∈ Icc 0 T, u (x,t) ≤ W x+Ht*t)
    (hop : ∀ z ∈ O ×ˢ Ioo 0 T,
      linearOp (cylinder (closure O) 0 T) a b u z ≤
        Ht+stationaryOp (a z) (b z) W z.1) :
    ∀ z ∈ cylinder (closure O) 0 T, u z ≤ W z.1+Ht*z.2 := by
  have hcmp := stationary_barrier_upper (u := fun z => u z-Ht*z.2) (b := b)
    hO hcompact hT (hc.sub (by fun_prop))
    (by
      intro z hz
      change ContDiffAt ℝ 2 (fun x => u (x,z.2)-Ht*z.2) z.1
      exact (hs z hz).sub contDiffAt_const)
    (fun z hz => (ht z hz).sub (by fun_prop)) he hWc hWs
    (by intro x hx; simpa only [mul_zero,sub_zero] using hi x hx)
    (by intro x hx t htm; exact sub_le_iff_le_add.mpr (hl x hx t htm))
    (by
      intro z hz
      rw [linearOp_sub_time hT (ht z hz).differentiableWithinAt Ht
        ⟨hz.1,hz.2.1,hz.2.2.le⟩]
      linarith [hop z hz])
  intro z hz
  exact sub_le_iff_le_add.mp (hcmp z hz)

theorem F05_moving_barrier_abs {O : Set (Space n)} {T lam upper H Ht : ℝ}
    {a : Point n → Mat n} {b : Point n → RIdx n → ℝ}
    {u : Point n → ℝ} {W : Space n → ℝ}
    (hO : IsOpen O) (hcompact : IsCompact (closure O)) (hT : 0 < T)
    (hc : ContinuousOn u (cylinder (closure O) 0 T))
    (hs : ∀ z ∈ O ×ˢ Ioo 0 T, ContDiffAt ℝ 2 (fun x => u (x,z.2)) z.1)
    (ht : ∀ z ∈ O ×ˢ Ioo 0 T, DifferentiableAt ℝ (fun t => u (z.1,t)) z.2)
    (he : Elliptic (O ×ˢ Ioo 0 T) a lam upper)
    (hWc : ContinuousOn W (closure O)) (hWs : ∀ x ∈ O, ContDiffAt ℝ 2 W x)
    (hi : ∀ x ∈ closure O, |u (x,0)| ≤ W x)
    (hl : ∀ x ∈ frontier O, ∀ t ∈ Icc 0 T, |u (x,t)| ≤ W x+Ht*t)
    (hop : ∀ z ∈ O ×ˢ Ioo 0 T,
      |linearOp (cylinder (closure O) 0 T) a b u z| ≤ H)
    (hbar : ∀ z ∈ O ×ˢ Ioo 0 T, H ≤ Ht+stationaryOp (a z) (b z) W z.1) :
    ∀ z ∈ cylinder (closure O) 0 T, |u z| ≤ W z.1+Ht*z.2 := by
  have hu := F05_moving_barrier_upper hO hcompact hT hc hs ht he hWc hWs
    (fun x hx => (le_abs_self _).trans (hi x hx))
    (fun x hx t htm => (le_abs_self _).trans (hl x hx t htm))
    (fun z hz => ((le_abs_self _).trans (hop z hz)).trans (hbar z hz))
  have hn := F05_moving_barrier_upper (u := fun z => -u z) hO hcompact hT hc.neg
    (fun z hz => (hs z hz).neg) (fun z hz => (ht z hz).neg) he hWc hWs
    (fun x hx => (neg_le_abs _).trans (hi x hx))
    (fun x hx t htm => (neg_le_abs _).trans (hl x hx t htm))
    (by
      intro z hz
      rw [linearOp_neg]
      exact ((neg_le_abs _).trans (hop z hz)).trans (hbar z hz))
  intro z hz
  exact abs_le.mpr ⟨neg_le.mp (hn z hz),hu z hz⟩

end Yau.Proofs.F05Aux
