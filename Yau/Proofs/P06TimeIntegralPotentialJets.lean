import Yau.Blueprint.HodgeContracts
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! Local space-jet control at the genuine initial time. No extension to
negative time and no global bound on derivatives is used. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff
namespace Yau.NodeProofs.P06Aux.TimePotential
set_option backward.isDefEq.respectTransparency false

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Every spatial jet of a positive-time jointly smooth family is jointly
smooth on the same open cylinder. -/
theorem spatialJets_contDiffOn {S : Set E} (hS : IsOpen S)
    {u : ℝ → E → F}
    (hu : ContDiffOn ℝ ∞ (fun p : E × ℝ => u p.2 p.1) (S ×ˢ Ioi 0))
    (j : ℕ) : ContDiffOn ℝ ∞
      (fun p : E × ℝ => iteratedFDeriv ℝ j (u p.2) p.1) (S ×ˢ Ioi 0) := by
  have hopen : IsOpen (S ×ˢ Ioi (0 : ℝ)) := hS.prod isOpen_Ioi
  induction j with
  | zero =>
    intro p hp
    simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_def, LinearIsometryEquiv.coe_coe''] using
      ((hu.contDiffAt (hopen.mem_nhds hp)).continuousLinearMap_comp
        ((continuousMultilinearCurryFin0 ℝ E F).symm : F →L[ℝ] E [×0]→L[ℝ] F)).contDiffWithinAt
  | succ j hj =>
    intro p hp
    have hlocal := hj.contDiffAt (hopen.mem_nhds hp)
    have harg : ContDiffAt ℝ ∞
        (fun q : (E × ℝ) × E => (q.2, q.1.2)) (p, p.1) :=
      contDiffAt_snd.prodMk (contDiffAt_snd.comp (p, p.1) contDiffAt_fst)
    have hcomp := hlocal.comp (p, p.1) harg
    change ContDiffAt ℝ ∞
      (Function.uncurry (fun (q : E × ℝ) (z : E) => iteratedFDeriv ℝ j (u q.2) z))
      (p, p.1) at hcomp
    have hd := hcomp.fderiv (m := ∞) (g := fun q : E × ℝ => q.1)
      contDiffAt_fst (by simp)
    simpa only [iteratedFDeriv_succ_eq_comp_left, Function.comp_def, LinearIsometryEquiv.coe_coe''] using
      (hd.continuousLinearMap_comp
        ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => E) F).symm :
          (E →L[ℝ] E [×j]→L[ℝ] F) →L[ℝ] E [×(j + 1)]→L[ℝ] F)).contDiffWithinAt

/-- All the initial jets give all orders of compact local domination. The
bound depends on the compact spatial set, the order and the finite time. -/
theorem compact_spatialJet_bound {S : Set E} (hS : IsOpen S)
    {u : ℝ → E → F} {f : E → F}
    (hu : ContDiffOn ℝ ∞ (fun p : E × ℝ => u p.2 p.1) (S ×ˢ Ioi 0))
    (hf : ContDiffOn ℝ ∞ f S)
    (hinit : ∀ K : Set E, IsCompact K → K ⊆ S → ∀ j : ℕ,
      ∀ ε > 0, ∃ τ > 0, ∀ s, 0 < s → s < τ → ∀ z ∈ K,
        ‖iteratedFDeriv ℝ j (fun w => u s w - f w) z‖ < ε)
    {K : Set E} (hK : IsCompact K) (hKS : K ⊆ S)
    (j : ℕ) {T : ℝ} (hT : 0 < T) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s, 0 < s → s ≤ T → ∀ z ∈ K,
      ‖iteratedFDeriv ℝ j (u s) z‖ ≤ B := by
  obtain ⟨τ, hτ, hsmall⟩ := hinit K hK hKS j 1 zero_lt_one
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    ((ContinuousOn.continuousOn_iteratedFDeriv hf hS (by simp : (j : ℕ∞ω) ≤ ∞)).mono hKS)
  obtain ⟨D, hD⟩ := (hK.prod isCompact_Icc).exists_bound_of_continuousOn
    ((spatialJets_contDiffOn hS hu j).continuousOn.mono
      (show K ×ˢ Icc τ T ⊆ S ×ˢ Ioi 0 from
        fun p hp => ⟨hKS hp.1, lt_of_lt_of_le hτ hp.2.1⟩))
  refine ⟨max (C + 1) (max D 0), le_trans (le_max_right D 0) (le_max_right _ _), ?_⟩
  intro s hs hsT z hz
  by_cases hst : s < τ
  · have hu_slice : ContDiffAt ℝ (j : ℕ∞ω) (u s) z := by
      have h := hu.contDiffAt ((hS.prod (isOpen_Ioi : IsOpen (Ioi (0 : ℝ)))).mem_nhds (show (z, s) ∈ S ×ˢ Ioi 0 from ⟨hKS hz, hs⟩))
      have ha : ContDiffAt ℝ ∞ (fun w : E => (w, s)) z :=
        contDiffAt_id.prodMk contDiffAt_const
      have hh := h.comp z ha
      simpa only [Function.comp_def, LinearIsometryEquiv.coe_coe''] using hh.of_le (show (j : ℕ∞ω) ≤ ∞ by simp)
    have hf_slice := (hf.contDiffAt (hS.mem_nhds (hKS hz))).of_le (by simp : (j : ℕ∞ω) ≤ ∞)
    have hd := hsmall s hs hst z hz
    change ‖iteratedFDeriv ℝ j (u s - f) z‖ < 1 at hd
    rw [iteratedFDeriv_sub_apply hu_slice hf_slice] at hd
    exact ((norm_le_norm_sub_add _ _).trans
      (add_le_add (le_of_lt hd) (hC z hz))).trans (by linarith [le_max_left (C + 1) (max D 0)])
  · exact (hD (z, s) ⟨hz, le_of_not_gt hst, hsT⟩).trans
      ((le_max_left D 0).trans (le_max_right _ _))

end Yau.NodeProofs.P06Aux.TimePotential
