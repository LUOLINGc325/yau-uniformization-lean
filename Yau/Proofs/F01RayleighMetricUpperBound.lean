import Yau.Proofs.F01GlobalRayleighPenalty

/-! The genuine maximum argument gives the actual Hermitian upper order.
The same fixed solution, native subsolution and constants work before every
small properness penalty; it is then removed at each actual point. -/
noncomputable section
open Set TopologicalSpace
open scoped Manifold ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} (M : ComplexManifold n) (S : Opens M.Carrier) (hS : IsConnected (S : Set M.Carrier))

theorem rayleigh_metric_upper_bound
    (g : SmoothMetric M) (hcurv : NonnegBisectional g.form)
    (f : (openConnectedManifold M S hS).Carrier → ℝ) (hf : SmoothFn f)
    (hfnonneg : ∀ x, 0 ≤ f x) (hfproper : ∀ b : ℝ, IsCompact {x | f x ≤ b})
    (h : ℝ → HermitianField (openConnectedManifold M S hS))
    (u Q : (openConnectedManifold M S hS).Carrier → ℝ → ℝ)
    {Tsol T a c B G D : ℝ} (hTpos : 0 < T) (hT : T < Tsol)
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
    (ha : 0 < a) (hc : 0 ≤ c) (hB : 0 ≤ B) (hG : 0 ≤ G)
    (hgrad : ∀ x, gradNormSq (conformalField (openRestrictedField M S hS g.form) f) f x ≤ G)
    (hlo : ∀ x, (levi f x - ((-B : ℝ) : ℂ) •
      gMat (conformalField (openRestrictedField M S hS g.form) f) x).PosSemidef)
    (hhi : ∀ x, ((B : ℂ) • gMat (conformalField (openRestrictedField M S hS g.form) f) x - levi f x).PosSemidef)
    (hQheat : ∀ x t, t ∈ Icc 0 T → c * traceWith (gMat (h t) x)
      (gMat (conformalField (openRestrictedField M S hS g.form) f) x) ≤
      fieldHeatWithin h (Icc 0 T) (fun s x => Q x s) x t)
    (hnegative : ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      (3 * B + 3 * G) - c * a + 8 * G + δ * (B + 2 * G) < 0) :
    ∀ x t, t ∈ Icc 0 T →
      (((Real.exp (rayleighPenalty a (Q x t)) : ℝ) : ℂ) •
        gMat (conformalField (openRestrictedField M S hS g.form) f) x - gMat (h t) x).PosSemidef := by
  let α := conformalField (openRestrictedField M S hS g.form) f
  intro x t ht
  have hlog : Real.log (metricLargestRayleigh α (h t) x) ≤ rayleighPenalty a (Q x t) := by
    apply le_of_all_small_positive_penalties
    intro δ hδ hδone
    exact global_rayleigh_penalty_nonpos M S hS g hcurv f hf hfnonneg hfproper h u Q hTpos hT
      hh hu hh0 hpot hpde hD hupper hQ hQnonneg ha hδ hc hB hG hgrad hlo hhi hQheat
      (hnegative δ hδ hδone) x t ht
  have hEigen : metricLargestRayleigh α (h t) x ≤ Real.exp (rayleighPenalty a (Q x t)) := by
    have hh := Real.exp_le_exp.mpr hlog
    rwa [Real.exp_log (metricLargestRayleigh_pos α (h t) x)] at hh
  exact order_of_largestMatrixRayleigh_le
    (Yau.LeafProofs.L12Aux.hMat_posDef α x (chartPt x x) (mem_extChartAt_target x))
    (Yau.LeafProofs.L12Aux.hMat_posDef (h t) x (chartPt x x) (mem_extChartAt_target x)) hEigen

end Yau.NodeProofs.F01Aux
