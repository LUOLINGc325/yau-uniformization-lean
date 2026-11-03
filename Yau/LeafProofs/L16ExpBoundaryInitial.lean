import Yau.LeafProofs.L16ExpBoundaryCalculus

open Filter Set
open scoped Topology ContDiff

noncomputable section

namespace Yau.LeafProofs.L16ExpBoundaryAux

open Yau.Parabolic Yau.ParabolicCandidates

theorem linearOp_sub_time {n : ℕ} {O : Set (Space n)} {T : ℝ}
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ} {u : Point n → ℝ}
    (hT : 0 < T) {p : Point n}
    (htime : DifferentiableWithinAt ℝ (fun t => u (p.1,t)) (Icc 0 T) p.2)
    (H : ℝ) (hp : p ∈ O ×ˢ Ioc 0 T) :
    linearOp (cylinder (closure O) 0 T) a b (fun z => u z-H*z.2) p =
      linearOp (cylinder (closure O) 0 T) a b u p-H := by
  have hfiber : {t | (p.1,t) ∈ cylinder (closure O) 0 T} = Icc 0 T := by
    ext t
    simp [cylinder, subset_closure hp.1]
  have hc : HasDerivAt (fun t : ℝ => H*t) H p.2 := by
    convert (hasDerivAt_id p.2).const_mul H using 1 <;> simp
  have ht : timeD (cylinder (closure O) 0 T) (fun z => u z-H*z.2) p =
      timeD (cylinder (closure O) 0 T) u p-H := by
    simp only [timeD, hfiber]
    rw [derivWithin_fun_sub htime hc.differentiableAt.differentiableWithinAt]
    rw [hc.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc hT p.2 ⟨hp.2.1.le,hp.2.2⟩)]
  simp only [linearOp, spatialD, spatialDD, fderiv_sub_const, ht]
  ring

/-- Time-affine comparison uses no derivatives on the spatial boundary and no
equation compatibility at the initial corner. -/
theorem initial_barrier_upper {n : ℕ} {O : Set (Space n)} {T lam upper H : ℝ}
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ} {u : Point n → ℝ}
    (hO : IsOpen O) (hcompact : IsCompact (closure O)) (hT : 0 < T) (hH : 0 ≤ H)
    (hc : ContinuousOn u (cylinder (closure O) 0 T))
    (hs : ∀ p ∈ O ×ˢ Ioc 0 T, ContDiffAt ℝ 2 (fun x => u (x,p.2)) p.1)
    (ht : ∀ p ∈ O ×ˢ Ioc 0 T,
      DifferentiableWithinAt ℝ (fun t => u (p.1,t)) (Icc 0 T) p.2)
    (he : Elliptic (O ×ˢ Ioc 0 T) a lam upper)
    (hi : ∀ x ∈ closure O, u (x,0) ≤ 0)
    (hl : ∀ x ∈ frontier O, ∀ t ∈ Icc 0 T, u (x,t) ≤ 0)
    (hop : ∀ p ∈ O ×ˢ Ioc 0 T, linearOp (cylinder (closure O) 0 T) a b u p ≤ H) :
    ∀ p ∈ cylinder (closure O) 0 T, u p ≤ H*p.2 := by
  have hcmp := L16Aux.interior_maximum_principle hO hcompact hT
    (u := fun p => u p-H*p.2) (a := a) (b := b)
    (hc.sub (by fun_prop)) (fun p hp => by
      change ContDiffAt ℝ 2 (fun x => u (x,p.2)-H*p.2) p.1
      exact (hs p hp).sub contDiffAt_const)
    (fun p hp => (ht p hp).sub (by fun_prop)) he
    (by intro x hx; simpa using hi x hx)
    (by intro x hx t htm; exact sub_nonpos.mpr ((hl x hx t htm).trans
      (mul_nonneg hH htm.1)))
    (by intro p hp; rw [linearOp_sub_time hT (ht p hp) H hp]; linarith [hop p hp])
  intro p hp
  exact sub_nonpos.mp (hcmp p hp)

/-- Both signs give a uniform initial modulus from a bound on the forcing. -/
theorem initial_barrier_abs {n : ℕ} {O : Set (Space n)} {T lam upper H : ℝ}
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ} {u : Point n → ℝ}
    (hO : IsOpen O) (hcompact : IsCompact (closure O)) (hT : 0 < T) (hH : 0 ≤ H)
    (hc : ContinuousOn u (cylinder (closure O) 0 T))
    (hs : ∀ p ∈ O ×ˢ Ioc 0 T, ContDiffAt ℝ 2 (fun x => u (x,p.2)) p.1)
    (ht : ∀ p ∈ O ×ˢ Ioc 0 T,
      DifferentiableWithinAt ℝ (fun t => u (p.1,t)) (Icc 0 T) p.2)
    (he : Elliptic (O ×ˢ Ioc 0 T) a lam upper)
    (hi : ∀ x ∈ closure O, u (x,0) = 0)
    (hl : ∀ x ∈ frontier O, ∀ t ∈ Icc 0 T, u (x,t) = 0)
    (hop : ∀ p ∈ O ×ˢ Ioc 0 T, |linearOp (cylinder (closure O) 0 T) a b u p| ≤ H) :
    ∀ p ∈ cylinder (closure O) 0 T, |u p| ≤ H*p.2 := by
  have hu := initial_barrier_upper (b := b) hO hcompact hT hH hc hs ht he
    (fun x hx => (hi x hx).le) (fun x hx t htm => (hl x hx t htm).le)
    (fun p hp => (abs_le.mp (hop p hp)).2)
  have hn := initial_barrier_upper (b := b) (u := fun p => -u p) hO hcompact hT hH hc.neg
    (fun p hp => (hs p hp).neg) (fun p hp => (ht p hp).neg) he
    (by intro x hx; simp [hi x hx]) (by intro x hx t htm; simp [hl x hx t htm])
    (by intro p hp; rw [linearOp_neg]; exact (neg_le.mpr (abs_le.mp (hop p hp)).1))
  intro p hp
  exact abs_le.mpr ⟨neg_le.mp (hn p hp), hu p hp⟩

end Yau.LeafProofs.L16ExpBoundaryAux
