import Yau.LeafProofs.L16ExpBoundaryOpenTop

open Filter Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

noncomputable section

namespace Yau.LeafProofs.L16ExpBoundaryAux

open Yau.Parabolic Yau.ParabolicCandidates

/-- Open-top comparison follows from closed subslabs and continuity. -/
theorem maximum_principle_openTop {n : ℕ} {O : Set (Space n)} {T lam upper : ℝ}
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ} {u : Point n → ℝ}
    (hO : IsOpen O) (hcompact : IsCompact (closure O)) (hT : 0 < T)
    (hc : ContinuousOn u (cylinder (closure O) 0 T))
    (hs : ∀ z ∈ O ×ˢ Ioo 0 T, ContDiffAt ℝ 2 (fun x => u (x,z.2)) z.1)
    (ht : ∀ z ∈ O ×ˢ Ioo 0 T, DifferentiableAt ℝ (fun t => u (z.1,t)) z.2)
    (he : Elliptic (O ×ˢ Ioo 0 T) a lam upper)
    (hi : ∀ x ∈ closure O, u (x,0) ≤ 0)
    (hl : ∀ x ∈ frontier O, ∀ t ∈ Icc 0 T, u (x,t) ≤ 0)
    (hop : ∀ z ∈ O ×ˢ Ioo 0 T, linearOp (cylinder (closure O) 0 T) a b u z ≤ 0) :
    ∀ z ∈ cylinder (closure O) 0 T, u z ≤ 0 := by
  have hbelow : ∀ z ∈ closure O ×ˢ Ico 0 T, u z ≤ 0 := by
    intro z hz
    let S : ℝ := (z.2+T)/2
    have hS : 0 < S := by dsimp [S]; linarith [hz.2.1]
    have hST : S < T := by dsimp [S]; linarith [hz.2.2]
    have hzS : z.2 ≤ S := by dsimp [S]; linarith [hz.2.2]
    have hsub : O ×ˢ Ioc 0 S ⊆ O ×ˢ Ioo 0 T := by
      intro p hp
      exact ⟨hp.1,hp.2.1,hp.2.2.trans_lt hST⟩
    have htime (p : Point n) (hp : p ∈ O ×ˢ Ioc 0 S) :
        timeD (cylinder (closure O) 0 S) u p =
          timeD (cylinder (closure O) 0 T) u p := by
      rw [timeD_closed_eq_deriv hS (subset_closure hp.1) ⟨hp.2.1.le,hp.2.2⟩ (ht p (hsub hp)),
        timeD_closed_eq_deriv hT (subset_closure hp.1)
          ⟨hp.2.1.le,(hp.2.2.trans_lt hST).le⟩ (ht p (hsub hp))]
    exact L16Aux.interior_maximum_principle hO hcompact hS
      (hc.mono (L16Aux.cylinder_mono_time hST.le))
      (fun p hp => hs p (hsub hp))
      (fun p hp => (ht p (hsub hp)).differentiableWithinAt)
      ⟨he.1,he.2.1,fun p hp => he.2.2 p (hsub hp)⟩ hi
      (fun x hx t htm => hl x hx t ⟨htm.1,htm.2.trans hST.le⟩)
      (by intro p hp; simpa only [linearOp,htime p hp] using hop p (hsub hp))
      z ⟨hz.1,hz.2.1,hzS⟩
  have hclosure : closure (closure O ×ˢ Ico 0 T) = cylinder (closure O) 0 T := by
    rw [closure_prod_eq,closure_closure,closure_Ico hT.ne]
    rfl
  intro z hz
  apply le_on_closure hbelow (by rw [hclosure]; exact hc) continuousOn_const
  rwa [hclosure]

def stationaryOp {n : ℕ} (A : Mat n) (β : Yau.RIdx n → ℝ)
    (W : Space n → ℝ) (x : Space n) : ℝ :=
  -(∑ i, ∑ j, A i j*fderiv ℝ (fderiv ℝ W) x (Yau.realVec i) (Yau.realVec j)) -
    ∑ i, β i*d W x i

theorem linearOp_spatial_lift {n : ℕ} (Q : Set (Point n)) (a : Point n → Mat n)
    (b : Point n → Yau.RIdx n → ℝ) (W : Space n → ℝ) (z : Point n) :
    linearOp Q a b (fun p => W p.1) z = stationaryOp (a z) (b z) W z.1 := by
  simp [linearOp,stationaryOp,timeD,spatialD,spatialDD,d]

/-- A stationary supersolution compares with a solution using only interior
derivatives; its boundary regularity is mere continuity. -/
theorem stationary_barrier_upper {n : ℕ} {O : Set (Space n)} {T lam upper : ℝ}
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ}
    {u : Point n → ℝ} {W : Space n → ℝ}
    (hO : IsOpen O) (hcompact : IsCompact (closure O)) (hT : 0 < T)
    (hc : ContinuousOn u (cylinder (closure O) 0 T))
    (hs : ∀ z ∈ O ×ˢ Ioo 0 T, ContDiffAt ℝ 2 (fun x => u (x,z.2)) z.1)
    (ht : ∀ z ∈ O ×ˢ Ioo 0 T, DifferentiableAt ℝ (fun t => u (z.1,t)) z.2)
    (he : Elliptic (O ×ˢ Ioo 0 T) a lam upper)
    (hWc : ContinuousOn W (closure O)) (hWs : ∀ x ∈ O, ContDiffAt ℝ 2 W x)
    (hi : ∀ x ∈ closure O, u (x,0) ≤ W x)
    (hl : ∀ x ∈ frontier O, ∀ t ∈ Icc 0 T, u (x,t) ≤ W x)
    (hop : ∀ z ∈ O ×ˢ Ioo 0 T,
      linearOp (cylinder (closure O) 0 T) a b u z ≤ stationaryOp (a z) (b z) W z.1) :
    ∀ z ∈ cylinder (closure O) 0 T, u z ≤ W z.1 := by
  have hWlift : ContinuousOn (fun z : Point n => W z.1) (cylinder (closure O) 0 T) :=
    hWc.comp continuous_fst.continuousOn (fun z hz => hz.1)
  have hcmp := maximum_principle_openTop (b := b) hO hcompact hT (hc.sub hWlift)
    (u := fun z => u z-W z.1)
    (by intro z hz; change ContDiffAt ℝ 2 (fun x => u (x,z.2)-W x) z.1
        exact (hs z hz).sub (hWs z.1 hz.1))
    (by intro z hz; change DifferentiableAt ℝ (fun t => u (z.1,t)-W z.1) z.2
        exact (ht z hz).sub (differentiableAt_const _)) he
    (by intro x hx; exact sub_nonpos.mpr (hi x hx))
    (by intro x hx t htm; exact sub_nonpos.mpr (hl x hx t htm))
    (by
      intro z hz
      have hWt : DifferentiableWithinAt ℝ (fun t => W (z.1,t).1)
          {t | (z.1,t) ∈ cylinder (closure O) 0 T} z.2 := by
        change DifferentiableWithinAt ℝ (fun _ : ℝ => W z.1)
          {t | (z.1,t) ∈ cylinder (closure O) 0 T} z.2
        exact differentiableWithinAt_const _
      rw [linearOp_sub_at (hs z hz) (hWs z.1 hz.1)
        (ht z hz).differentiableWithinAt hWt,linearOp_spatial_lift]
      exact sub_nonpos.mpr (hop z hz))
  intro z hz
  exact sub_nonpos.mp (hcmp z hz)

theorem stationary_barrier_abs {n : ℕ} {O : Set (Space n)} {T lam upper H : ℝ}
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ}
    {u : Point n → ℝ} {W : Space n → ℝ}
    (hO : IsOpen O) (hcompact : IsCompact (closure O)) (hT : 0 < T)
    (hc : ContinuousOn u (cylinder (closure O) 0 T))
    (hs : ∀ z ∈ O ×ˢ Ioo 0 T, ContDiffAt ℝ 2 (fun x => u (x,z.2)) z.1)
    (ht : ∀ z ∈ O ×ˢ Ioo 0 T, DifferentiableAt ℝ (fun t => u (z.1,t)) z.2)
    (he : Elliptic (O ×ˢ Ioo 0 T) a lam upper)
    (hWc : ContinuousOn W (closure O)) (hWs : ∀ x ∈ O, ContDiffAt ℝ 2 W x)
    (hi : ∀ x ∈ closure O, |u (x,0)| ≤ W x)
    (hl : ∀ x ∈ frontier O, ∀ t ∈ Icc 0 T, |u (x,t)| ≤ W x)
    (hop : ∀ z ∈ O ×ˢ Ioo 0 T, |linearOp (cylinder (closure O) 0 T) a b u z| ≤ H)
    (hbar : ∀ z ∈ O ×ˢ Ioo 0 T, H ≤ stationaryOp (a z) (b z) W z.1) :
    ∀ z ∈ cylinder (closure O) 0 T, |u z| ≤ W z.1 := by
  have hu := stationary_barrier_upper (b := b) hO hcompact hT hc hs ht he hWc hWs
    (fun x hx => (le_abs_self _).trans (hi x hx))
    (fun x hx t htm => (le_abs_self _).trans (hl x hx t htm))
    (fun z hz => ((le_abs_self _).trans (hop z hz)).trans (hbar z hz))
  have hn := stationary_barrier_upper (b := b) (u := fun z => -u z) hO hcompact hT hc.neg
    (fun z hz => (hs z hz).neg) (fun z hz => (ht z hz).neg) he hWc hWs
    (fun x hx => (neg_le_abs _).trans (hi x hx))
    (fun x hx t htm => (neg_le_abs _).trans (hl x hx t htm))
    (by intro z hz; rw [linearOp_neg]
        exact ((neg_le_abs _).trans (hop z hz)).trans (hbar z hz))
  intro z hz
  exact abs_le.mpr ⟨neg_le.mp (hn z hz),hu z hz⟩

end Yau.LeafProofs.L16ExpBoundaryAux
