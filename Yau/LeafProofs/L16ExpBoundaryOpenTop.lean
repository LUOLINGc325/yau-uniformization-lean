import Yau.LeafProofs.L16ExpBoundaryInitial

open Filter Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

noncomputable section

namespace Yau.LeafProofs.L16ExpBoundaryAux

open Yau.Parabolic Yau.ParabolicCandidates

theorem timeD_closed_eq_deriv {n : ℕ} {O : Set (Space n)} {T : ℝ}
    (hT : 0 < T) {u : Point n → ℝ} {p : Point n}
    (hx : p.1 ∈ closure O) (ht : p.2 ∈ Icc 0 T)
    (hu : DifferentiableAt ℝ (fun t => u (p.1,t)) p.2) :
    timeD (cylinder (closure O) 0 T) u p = deriv (fun t => u (p.1,t)) p.2 := by
  have hf : {t | (p.1,t) ∈ cylinder (closure O) 0 T} = Icc 0 T := by
    ext t
    simp [cylinder,hx]
  simp only [timeD,hf]
  exact hu.derivWithin (uniqueDiffOn_Icc hT p.2 ht)

/-- Estimates proved below every terminal face extend to the original closed
cylinder by continuity. No continuation beyond the final time is needed. -/
theorem initial_barrier_abs_openTop {n : ℕ} {O : Set (Space n)} {T lam upper H : ℝ}
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ} {u : Point n → ℝ}
    (hO : IsOpen O) (hcompact : IsCompact (closure O)) (hT : 0 < T) (hH : 0 ≤ H)
    (hc : ContinuousOn u (cylinder (closure O) 0 T))
    (hs : ∀ p ∈ O ×ˢ Ioo 0 T, ContDiffAt ℝ 2 (fun x => u (x,p.2)) p.1)
    (ht : ∀ p ∈ O ×ˢ Ioo 0 T, DifferentiableAt ℝ (fun t => u (p.1,t)) p.2)
    (he : Elliptic (O ×ˢ Ioo 0 T) a lam upper)
    (hi : ∀ x ∈ closure O, u (x,0) = 0)
    (hl : ∀ x ∈ frontier O, ∀ t ∈ Icc 0 T, u (x,t) = 0)
    (hop : ∀ p ∈ O ×ˢ Ioo 0 T, |linearOp (cylinder (closure O) 0 T) a b u p| ≤ H) :
    ∀ p ∈ cylinder (closure O) 0 T, |u p| ≤ H*p.2 := by
  have hbelow : ∀ p ∈ closure O ×ˢ Ico 0 T, |u p| ≤ H*p.2 := by
    intro p hp
    let S : ℝ := (p.2+T)/2
    have hS : 0 < S := by dsimp [S]; linarith [hp.2.1]
    have hST : S < T := by dsimp [S]; linarith [hp.2.2]
    have hps : p.2 ≤ S := by dsimp [S]; linarith [hp.2.2]
    have hsub : O ×ˢ Ioc 0 S ⊆ O ×ˢ Ioo 0 T := by
      intro z hz
      exact ⟨hz.1,hz.2.1,hz.2.2.trans_lt hST⟩
    have htime (z : Point n) (hz : z ∈ O ×ˢ Ioc 0 S) :
        timeD (cylinder (closure O) 0 S) u z =
          timeD (cylinder (closure O) 0 T) u z := by
      rw [timeD_closed_eq_deriv hS (subset_closure hz.1) ⟨hz.2.1.le,hz.2.2⟩ (ht z (hsub hz)),
        timeD_closed_eq_deriv hT (subset_closure hz.1)
          ⟨hz.2.1.le,(hz.2.2.trans_lt hST).le⟩ (ht z (hsub hz))]
    have hEst := initial_barrier_abs (b := b) hO hcompact hS hH
      (hc.mono (L16Aux.cylinder_mono_time hST.le))
      (fun z hz => hs z (hsub hz))
      (fun z hz => (ht z (hsub hz)).differentiableWithinAt)
      ⟨he.1,he.2.1,fun z hz => he.2.2 z (hsub hz)⟩ hi
      (fun x hx t htm => hl x hx t ⟨htm.1,htm.2.trans hST.le⟩)
      (by intro z hz; simpa only [linearOp,htime z hz] using hop z (hsub hz))
    exact hEst p ⟨hp.1,hp.2.1,hps⟩
  have hclosure : closure (closure O ×ˢ Ico 0 T) = cylinder (closure O) 0 T := by
    rw [closure_prod_eq,closure_closure,closure_Ico hT.ne]
    rfl
  intro p hp
  apply le_on_closure hbelow
    (by rw [hclosure]; exact hc.abs)
    (by fun_prop)
  rwa [hclosure]

end Yau.LeafProofs.L16ExpBoundaryAux
