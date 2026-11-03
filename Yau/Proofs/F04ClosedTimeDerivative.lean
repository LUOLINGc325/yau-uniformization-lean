import Yau.Proofs.F04ChartContinuity

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold

noncomputable section

namespace Yau.F04Proof

open Yau.Blueprint

variable {n : ℕ} {M : ComplexManifold n}

theorem chart_time_derivativeWithin_Icc {S : ℝ} (hS : 0 < S)
    {v : M.Carrier → ℝ → ℝ} (hv : SmoothSpaceTime v (Icc 0 S))
    (c : M.Carrier) {p : ComplexVector n × ℝ} (hp : p ∈ chartTarget c ×ˢ Icc 0 S) :
    derivWithin (v (chartInv c p.1)) (Icc 0 S) p.2 =
      fderivWithin ℝ (fun q : ComplexVector n × ℝ => v (chartInv c q.1) q.2)
        (chartTarget c ×ˢ Icc 0 S) p (0, 1) := by
  have hF := ((hv c).differentiableOn (by simp) p hp).hasFDerivWithinAt
  have hmap : HasDerivWithinAt (fun s : ℝ => (p.1, s)) (0, 1) (Icc 0 S) p.2 :=
    ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)).hasDerivWithinAt
  have hmapto : MapsTo (fun s : ℝ => (p.1, s)) (Icc 0 S) (chartTarget c ×ˢ Icc 0 S) :=
    fun _ hs => ⟨hp.1, hs⟩
  have hd := hF.comp_hasDerivWithinAt_of_eq p.2 hmap hmapto (by cases p; rfl)
  simpa only [Function.comp_def] using hd.derivWithin (uniqueDiffOn_Icc hS p.2 hp.2)

/-- Actual time-within derivatives remain jointly continuous up to both
physical time faces; the derivatives are taken on the closed interval itself. -/
theorem smoothSpaceTime_timeDerivativeWithin_continuousOn
    {S : ℝ} (hS : 0 < S) {v : M.Carrier → ℝ → ℝ}
    (hv : SmoothSpaceTime v (Icc 0 S)) :
    ContinuousOn (fun p : M.Carrier × ℝ => derivWithin (v p.1) (Icc 0 S) p.2)
      (univ ×ˢ Icc 0 S) := by
  apply chartwise_continuousOn (M := M) (I := Icc 0 S)
    (v := fun x t => derivWithin (v x) (Icc 0 S) t)
  intro c
  have huniq := (isOpen_extChartAt_target (I := ComplexModel n) c).uniqueDiffOn.prod
    (uniqueDiffOn_Icc hS)
  have hF := (hv c).continuousOn_fderivWithin huniq (by simp)
  apply (hF.clm_apply continuousOn_const).congr
  intro p hp
  exact chart_time_derivativeWithin_Icc hS hv c hp

theorem flow_scalarCurvature_continuousOn_closed
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ) {S : ℝ} (hS : 0 < S) :
    ContinuousOn (fun p : Pt X × ℝ => scalarCurvature (h p.2) p.1) (univ ×ˢ Icc 0 S) := by
  have hρ : SmoothSpaceTime ρ (Icc 0 S) := fun c => (hloc.2.2.2.1 c).mono
    (prod_mono (Subset.refl _) (fun _ ht => ht.1))
  apply (smoothSpaceTime_timeDerivativeWithin_continuousOn hS hρ).congr
  intro p hp
  exact (rho_derivWithin_Icc o h U P ρ hloc S hS p.1 p.2 hp.2).symm

end Yau.F04Proof
