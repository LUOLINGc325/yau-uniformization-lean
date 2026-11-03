import Yau.Proofs.F01ShortTimeMetricJet
import Yau.Proofs.F01NormalRayleighHeat
import Yau.Proofs.F01NormalContactBudgets
import Yau.Proofs.F01HeatChartNaturality
import Yau.Proofs.F01RayleighMaximumSupport
import Yau.Proofs.F01ClosedTimeSlices
import Yau.Proofs.F01PenalizedContactContradiction

/-! A normal-coordinate contact is excluded using the original scalar
flow potential equation, the genuine intrinsic budgets, and the native heat
subsolution. No independent metric evolution or contact jets are supplied. -/
noncomputable section
open Set TopologicalSpace
open scoped Manifold ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ} (M : ComplexManifold n) (S : Opens M.Carrier) (hS : IsConnected (S : Set M.Carrier))

theorem normal_maximum_excluded
    (g : SmoothMetric M) (hcurv : NonnegBisectional g.form)
    (f : (openConnectedManifold M S hS).Carrier → ℝ) (hf : SmoothFn f)
    (h : ℝ → HermitianField (openConnectedManifold M S hS))
    (u Q : (openConnectedManifold M S hS).Carrier → ℝ → ℝ)
    {Tsol T t a δ c B G : ℝ} (hT : T < Tsol) (ht : 0 < t) (htT : t ≤ T)
    (hh : MetricFamilySmooth h (Icc 0 Tsol)) (hu : SmoothSpaceTime u (Icc 0 Tsol))
    (hpot : ∀ s ∈ Icc 0 Tsol, ∀ x, gMat (h s) x =
      gMat (conformalField (openRestrictedField M S hS g.form) f) x -
      (s : ℂ) • ricci (conformalField (openRestrictedField M S hS g.form) f) x + levi (fun y => u y s) x)
    (hpde : ∀ x s, s ∈ Icc 0 Tsol → HasDerivWithinAt (u x)
      (Real.log ((gMat (h s) x).det.re /
        (gMat (conformalField (openRestrictedField M S hS g.form) f) x).det.re)) (Icc 0 Tsol) s)
    (hQ : SmoothSpaceTime Q (Icc 0 T))
    (e : OpenPartialHomeomorph (ComplexVector n) (openConnectedManifold M S hS).Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    (hs : (0 : ComplexVector n) ∈ e.source)
    (hvalue : pullbackMatrix (openRestrictedField M S hS g.form) e 0 = 1)
    (hjet : ∀ i j, fderiv ℝ (fun w =>
      pullbackMatrix (openRestrictedField M S hS g.form) e w i j) 0 = 0)
    (values : Fin n → ℝ)
    (hdiag : pullbackMatrix (h t) e 0 = Matrix.diagonal (fun i => (values i : ℂ))) (j : Fin n)
    (ha : 0 < a) (hδ : 0 ≤ δ) (hc : 0 ≤ c) (hB : 0 ≤ B) (hG : 0 ≤ G)
    (hQpos : 0 ≤ Q (e 0) t)
    (hlarge : rayleighPenalty a (Q (e 0) t) ≤
      chartLogRayleigh (conformalField (openRestrictedField M S hS g.form) f) h e j (0, t))
    (hgrad : gradNormSq (conformalField (openRestrictedField M S hS g.form) f) f (e 0) ≤ G)
    (hlo : (levi f (e 0) - ((-B : ℝ) : ℂ) •
      gMat (conformalField (openRestrictedField M S hS g.form) f) (e 0)).PosSemidef)
    (hhi : ((B : ℂ) • gMat (conformalField (openRestrictedField M S hS g.form) f) (e 0) -
      levi f (e 0)).PosSemidef)
    (hQheat : c * traceWith (gMat (h t) (e 0))
      (gMat (conformalField (openRestrictedField M S hS g.form) f) (e 0)) ≤
      fieldHeatWithin h (Icc 0 T) (fun s x => Q x s) (e 0) t)
    (hmaxSpace : IsLocalMax (fun w => chartRayleighPenalty
      (conformalField (openRestrictedField M S hS g.form) f) h e j (fun s x => Q x s) f a δ (w, t)) 0)
    (hmaxTime : IsMaxOn (fun s => chartRayleighPenalty
      (conformalField (openRestrictedField M S hS g.form) f) h e j (fun s x => Q x s) f a δ (0, s)) (Icc 0 T) t)
    (hnegative : (3 * B + 3 * G) - c * a + 8 * G + δ * (B + 2 * G) < 0) : False := by
  let g0 := openRestrictedField M S hS g.form
  let α := conformalField g0 f
  let V := chartLogRayleigh α h e j
  let Qc := fun p : ComplexVector n × ℝ => Q (e p.1) p.2
  let fc := fun w : ComplexVector n => f (e w)
  let τ := traceWith (pullbackMatrix (h t) e 0) (pullbackMatrix α e 0)
  have htshort : t ∈ Icc 0 Tsol := ⟨ht.le, htT.trans hT.le⟩
  have htbound : t ∈ Icc 0 T := ⟨ht.le, htT⟩
  have hα : MetricSmooth α := conformalField_metricSmooth
    (openRestrictedField_metricSmooth M S hS (Yau.LeafProofs.L12Aux.metricSmooth_of_smoothMetric g)) hf
  have hv (i : Fin n) : 0 < values i := by
    have hh := pullback_diagonal_pos (h t) e he hei hs i
    simpa only [hdiag, Matrix.diagonal_apply_eq, Complex.ofReal_re] using hh
  have hsingle : (Pi.single j (1 : ℂ) : Fin n → ℂ) ≠ 0 := by
    intro hh
    have hi := congrFun hh j
    simpa using hi
  have hVfull := metricFamily_fixed_log_rayleigh_contDiffOn α hα h hh e he hei hsingle
  have hVbound : ContDiffOn ℝ ∞ V (e.source ×ˢ Icc 0 T) :=
    hVfull.mono (fun p hp => ⟨hp.1, hp.2.1, hp.2.2.trans hT.le⟩)
  obtain ⟨hVspace, hVtime⟩ := closed_slab_slice_jets hVbound e.open_source hs htbound
  obtain ⟨hQspace, hQtime⟩ := closed_slab_slice_jets
    (smoothSpaceTime_holomorphic_chart hQ e he) e.open_source hs htbound
  have hfspace : ContDiffAt ℝ 2 fc 0 :=
    ((smoothFn_comp_holomorphic_chart f hf e he).contDiffAt (e.open_source.mem_nhds hs)).of_le (by simp)
  have hevol := shortTime_potential_chart_real_hasDerivWithinAt α hα h u hu hpot hpde e he hei hs
    (show t ∈ Ioo 0 Tsol from ⟨ht, htT.trans_lt hT⟩) (Icc 0 T) j j
  have hUnique : UniqueDiffWithinAt ℝ (Icc 0 T) t := (uniqueDiffOn_Icc (ht.trans_le htT)) t htbound
  have hq : Real.exp (f (e 0)) ≤ (pullbackMatrix (h t) e 0 j j).re := by
    have hVnonneg : 0 ≤ V (0, t) := (rayleighPenalty_nonneg ha.le hQpos).trans hlarge
    have htime := conformal_single_logRayleigh_time_eq g0 f h e hvalue j
    have hpos := pullback_diagonal_pos (h t) e he hei hs j
    have hlog : 0 ≤ Real.log ((pullbackMatrix (h t) e 0 j j).re / Real.exp (f (e 0))) := by
      simpa only [V, chartLogRayleigh, α, congrFun htime t] using hVnonneg
    have hratio := Real.one_le_exp hlog
    rw [Real.exp_log (div_pos hpos (Real.exp_pos _))] at hratio
    simpa only [one_mul] using (le_div_iff₀ (Real.exp_pos _)).mp hratio
  have hdrift := normal_rayleigh_heat_bound_within M S hS g hcurv f (fun x => u x t) hf
    (smoothSpaceTime_slice hu htshort) h t (metricFamilySmooth_slice hh htshort) (hpot t htshort)
    e he hei hs hvalue hjet values hdiag j B G hB hG hq hgrad hlo hhi hUnique hevol
  obtain ⟨hτ, hg, hftrace⟩ := normal_contact_budgets g0 (h t) f hf e he hei hs hvalue values hdiag j B G hgrad hlo hhi
  have hQlocal : c * τ ≤ diagonalHeatWithin values Qc (Icc 0 T) 0 t := by
    rw [diagonalHeatWithin_holomorphic_chart h (fun s x => Q x s) (Icc 0 T) e he hei hs t
      (smoothSpaceTime_slice hQ htbound) values hdiag]
    simpa only [τ, traceWith_holomorphic_chart (h t) α e he hei hs] using hQheat
  exact penalized_contact_contradiction values hv V Qc fc ht htT ha hδ hτ hc hQpos hlarge
    hUnique hVtime hQtime hVspace hQspace hfspace hmaxSpace hmaxTime hdrift hQlocal hftrace hg hnegative

end Yau.NodeProofs.F01Aux
