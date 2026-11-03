import Yau.Proofs.F01NormalMaximumExclusion
import Yau.Proofs.F01RestrictedRayleighSupport
import Yau.Proofs.F01RayleighPenaltyMaximum
import Yau.Proofs.F01SpaceTimeContinuity
import Yau.Proofs.F01PenaltyLimit

/-! The actual global penalized largest eigenvalue is nonpositive on a
closed comparison slab strictly inside the supplied short-time flow.
Every contact chart and maximizing direction is constructed at its maximum. -/
noncomputable section
open Set TopologicalSpace
open scoped Manifold ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ} (M : ComplexManifold n) (S : Opens M.Carrier) (hS : IsConnected (S : Set M.Carrier))

theorem global_rayleigh_penalty_nonpos
    (g : SmoothMetric M) (hcurv : NonnegBisectional g.form)
    (f : (openConnectedManifold M S hS).Carrier → ℝ) (hf : SmoothFn f)
    (hfnonneg : ∀ x, 0 ≤ f x) (hfproper : ∀ b : ℝ, IsCompact {x | f x ≤ b})
    (h : ℝ → HermitianField (openConnectedManifold M S hS))
    (u Q : (openConnectedManifold M S hS).Carrier → ℝ → ℝ)
    {Tsol T a δ c B G D : ℝ} (hTpos : 0 < T) (hT : T < Tsol)
    (hh : MetricFamilySmooth h (Icc 0 Tsol)) (hu : SmoothSpaceTime u (Icc 0 Tsol))
    (hh0 : h 0 = conformalField (openRestrictedField M S hS g.form) f)
    (hpot : ∀ s ∈ Icc 0 Tsol, ∀ x, gMat (h s) x =
      gMat (conformalField (openRestrictedField M S hS g.form) f) x -
      (s : ℂ) • ricci (conformalField (openRestrictedField M S hS g.form) f) x + levi (fun y => u y s) x)
    (hpde : ∀ x s, s ∈ Icc 0 Tsol → HasDerivWithinAt (u x)
      (Real.log ((gMat (h s) x).det.re /
        (gMat (conformalField (openRestrictedField M S hS g.form) f) x).det.re)) (Icc 0 Tsol) s)
    (hD : 0 < D) (hupper : ∀ s ∈ Icc 0 T, ∀ x,
      ((D : ℂ) • gMat (conformalField (openRestrictedField M S hS g.form) f) x - gMat (h s) x).PosSemidef)
    (hQ : SmoothSpaceTime Q (Icc 0 T)) (hQnonneg : ∀ x t, t ∈ Icc 0 T → 0 ≤ Q x t)
    (ha : 0 < a) (hδ : 0 < δ) (hc : 0 ≤ c) (hB : 0 ≤ B) (hG : 0 ≤ G)
    (hgrad : ∀ x, gradNormSq (conformalField (openRestrictedField M S hS g.form) f) f x ≤ G)
    (hlo : ∀ x, (levi f x - ((-B : ℝ) : ℂ) •
      gMat (conformalField (openRestrictedField M S hS g.form) f) x).PosSemidef)
    (hhi : ∀ x, ((B : ℂ) • gMat (conformalField (openRestrictedField M S hS g.form) f) x - levi f x).PosSemidef)
    (hQheat : ∀ x t, t ∈ Icc 0 T → c * traceWith (gMat (h t) x)
      (gMat (conformalField (openRestrictedField M S hS g.form) f) x) ≤
      fieldHeatWithin h (Icc 0 T) (fun s x => Q x s) x t)
    (hnegative : (3 * B + 3 * G) - c * a + 8 * G + δ * (B + 2 * G) < 0) :
    ∀ x t, t ∈ Icc 0 T → metricRayleighPenalty
      (conformalField (openRestrictedField M S hS g.form) f) h (fun s x => Q x s) f a δ (x, t) ≤ 0 := by
  let g0 := openRestrictedField M S hS g.form
  let α := conformalField g0 f
  have hα : MetricSmooth α := conformalField_metricSmooth
    (openRestrictedField_metricSmooth M S hS (Yau.LeafProofs.L12Aux.metricSmooth_of_smoothMetric g)) hf
  have hhbound : MetricFamilySmooth h (Icc 0 T) := fun p b d =>
    (hh p b d).mono (fun z hz => ⟨hz.1, hz.2.1, hz.2.2.trans hT.le⟩)
  intro x s hs
  by_contra hnot
  have hpos : 0 < metricRayleighPenalty α h (fun t x => Q x t) f a δ (x, s) := lt_of_not_ge hnot
  obtain ⟨⟨y, t⟩, ht, hmax⟩ := exists_metricRayleighPenalty_max α hα h isCompact_Icc hhbound
    (fun t x => Q x t) (smoothSpaceTime_continuousOn hQ)
    (fun p hp => hQnonneg p.1 p.2 hp) f (continuous_of_smoothFn hf) hfproper
    ha.le hD hδ hupper x 0 ⟨le_refl 0, hTpos.le⟩
  have hposMax : 0 < metricRayleighPenalty α h (fun t x => Q x t) f a δ (y, t) :=
    hpos.trans_le (hmax (show (x, s) ∈ univ ×ˢ Icc 0 T from ⟨mem_univ _, hs⟩))
  have htpos : 0 < t := by
    by_contra htn
    have heq : t = 0 := le_antisymm (le_of_not_gt htn) ht.1
    have hinit := metricRayleighPenalty_initial_nonpos α h hh0 (fun t x => Q x t)
      (fun z => hQnonneg z 0 ⟨le_refl 0, hTpos.le⟩) f hfnonneg ha.le hδ.le y
    rw [heq] at hposMax
    exact (not_lt_of_ge hinit) hposMax
  have htsol : t ∈ Icc 0 Tsol := ⟨htpos.le, ht.2.trans hT.le⟩
  obtain ⟨e, values, j, he0, hs0, heSmooth, heiSmooth, hvalue, hjet, hdiag, hj,
      hW, hWle, hcontact, hWvalue⟩ := exists_restricted_conformal_rayleigh_support
    g S hS (h t) (metricFamilySmooth_slice hh htsol) f hf y
  have he := heSmooth.mdifferentiableOn (by simp)
  have hei := heiSmooth.mdifferentiableOn (by simp)
  have hcontact' : matrixRayleigh (pullbackMatrix α e 0) (pullbackMatrix (h t) e 0)
      (Pi.single j 1) = metricLargestRayleigh α (h t) (e 0) := by
    simpa only [he0] using hcontact
  have hmax' : IsMaxOn (metricRayleighPenalty α h (fun t x => Q x t) f a δ)
      (univ ×ˢ Icc 0 T) (e 0, t) := by rw [he0]; exact hmax
  obtain ⟨hmaxSpace, hmaxTime⟩ := actual_rayleigh_support_at_max α h e he hei hs0 j
    (fun t x => Q x t) f a δ t (Icc 0 T) ht hcontact' hmax'
  have hlog : chartLogRayleigh α h e j (0, t) = Real.log (metricLargestRayleigh α (h t) y) :=
    congrArg Real.log hcontact
  have hlarge : rayleighPenalty a (Q (e 0) t) ≤ chartLogRayleigh α h e j (0, t) := by
    rw [hlog, he0]
    change 0 < Real.log (metricLargestRayleigh α (h t) y) - rayleighPenalty a (Q y t) - δ * f y at hposMax
    nlinarith [mul_nonneg hδ.le (hfnonneg y)]
  exact normal_maximum_excluded M S hS g hcurv f hf h u Q hT htpos ht.2 hh hu hpot hpde hQ
    e he hei hs0 hvalue hjet values hdiag j ha hδ.le hc hB hG (hQnonneg (e 0) t ht) hlarge
    (hgrad (e 0)) (hlo (e 0)) (hhi (e 0)) (hQheat (e 0) t ht) hmaxSpace hmaxTime hnegative

end Yau.NodeProofs.F01Aux
