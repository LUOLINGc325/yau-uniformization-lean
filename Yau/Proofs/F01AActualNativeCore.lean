import Yau.Proofs.F01AActualLeviLimit
import Yau.Proofs.F01AActualTimeIdentification
import Yau.Proofs.F01PotentialMetricSmooth
import Yau.Proofs.F01ScalarSymbolSmooth

/-! One actual common subsequence determines the native potential flow,
its logarithmic determinant and its scalar sign. Every finite equation,
order and cap below is eventual, as required for expanding sublevels. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Blueprint
variable {n : ℕ}

theorem exists_native_core_of_actual_same_sequence_limits
    (X : KahlerManifold n) (L : ℕ → ℝ) (f p : ℕ → STF X)
    (U : STF X) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (hL : Tendsto L atTop atTop)
    (hU : SmoothSpaceTime U (Ici 0)) (hU0 : ∀ x, U x 0 = 0)
    (hLevi : ∀ x t, 0 ≤ t →
      Tendsto (fun m => levi (fun y => f (σ m) y t) x) atTop
        (𝓝 (levi (fun y => U y t) x)))
    (hOrders : ∀ x t, 0 ≤ t → ∃ ell : ℝ, 0 < ell ∧ ∃ R : ℝ,
      (∀ᶠ m in atTop,
        (nativePotentialMatrix X.metric.form (f (σ m)) t x -
          (ell : ℂ) • gMat X.metric.form x).PosSemidef) ∧
      (∀ᶠ m in atTop,
        ((Real.exp (2 * R / L (σ m)) : ℂ) • gMat X.metric.form x -
          nativePotentialMatrix X.metric.form (f (σ m)) t x).PosSemidef))
    (hFirst : ∀ x (k : ℕ), ∀ t ∈ Icc 0 ((k : ℝ) + 1),
      Tendsto (fun m => derivWithin (f (σ m) x) (Icc 0 ((k : ℝ) + 1)) t) atTop
        (𝓝 (derivWithin (U x) (Icc 0 ((k : ℝ) + 1)) t)))
    (hSecond : ∀ x (k : ℕ), ∀ t ∈ Icc 0 ((k : ℝ) + 1),
      Tendsto
        (fun m => derivWithin
          (fun s => derivWithin (f (σ m) x) (Icc 0 ((k : ℝ) + 1)) s)
          (Icc 0 ((k : ℝ) + 1)) t) atTop
        (𝓝 (derivWithin
          (fun s => derivWithin (U x) (Icc 0 ((k : ℝ) + 1)) s)
          (Icc 0 ((k : ℝ) + 1)) t)))
    (hFinitePDE : ∀ x (k : ℕ), ∀ᶠ m in atTop, ∀ t ∈ Icc 0 ((k : ℝ) + 1),
      HasDerivWithinAt (f (σ m) x) (p (σ m) x t) (Icc 0 ((k : ℝ) + 1)) t)
    (hFiniteLog : ∀ x t, 0 ≤ t → ∀ᶠ m in atTop,
      p (σ m) x t = Real.log
        ((nativePotentialMatrix X.metric.form (f (σ m)) t x).det.re /
          (gMat X.metric.form x).det.re))
    (hPCap : ∀ x t, 0 ≤ t → ∃ a : ℝ, ∀ᶠ m in atTop,
      p (σ m) x t ≤ a / L (σ m) ^ 2)
    (hSecondCap : ∀ x (k : ℕ), ∀ t ∈ Icc 0 ((k : ℝ) + 1), ∃ a : ℝ, ∀ᶠ m in atTop,
      derivWithin (fun s => derivWithin (f (σ m) x) (Icc 0 ((k : ℝ) + 1)) s)
        (Icc 0 ((k : ℝ) + 1)) t ≤
        a / L (σ m) ^ 2) :
    ∃ h : Flow X,
      LocalizedFlowCore X h U (flowLogDetRatio X.metric.form h)
        (fun x t => -flowLogDetRatio X.metric.form h x t) ∧
      ∀ x t, 0 ≤ t → Tendsto (fun m => p (σ m) x t) atTop
        (𝓝 (flowLogDetRatio X.metric.form h x t)) := by
  have hLσ : Tendsto (fun m => L (σ m)) atTop atTop := hL.comp hσ.tendsto_atTop
  have hMatrix (x : Pt X) (t : ℝ) (ht : 0 ≤ t) :
      Tendsto (fun m => nativePotentialMatrix X.metric.form (f (σ m)) t x) atTop
        (𝓝 (nativePotentialMatrix X.metric.form U t x)) :=
    actual_native_potential_matrix_limit X.metric.form (fun m => f (σ m)) U x t (hLevi x t ht)
  have hLimitOrders (x : Pt X) (t : ℝ) (ht : 0 ≤ t) :
      (nativePotentialMatrix X.metric.form U t x).PosDef ∧
        HermLE (nativePotentialMatrix X.metric.form U t x) (gMat X.metric.form x) := by
    obtain ⟨ell, hell, R, hlo, hhi⟩ := hOrders x t ht
    exact actual_native_potential_orders_of_matrix_limit X.metric.form
      (fun m => f (σ m)) U x t hell (fun m => Real.exp (2 * R / L (σ m)))
      (hMatrix x t ht) (actual_rayleigh_upper_factor_tendsto_one hLσ R) hlo hhi
  let hpos : ∀ t ∈ Ici (0 : ℝ), ∀ x,
      (nativePotentialMatrix X.metric.form U t x).PosDef :=
    fun t ht x => (hLimitOrders x t ht).1
  let h : Flow X := assembledPotentialFlow X.metric.form U (Ici 0) hpos
  have hpot (t : ℝ) (ht : 0 ≤ t) (x : Pt X) :
      gMat (h t) x = gMat X.metric.form x - (t : ℂ) • ricci X.metric.form x +
        levi (fun y => U y t) x :=
    assembledPotentialFlow_native_matrix X.metric.form U (Ici 0) hpos ht x
  have hg : MetricSmooth X.metric.form :=
    Yau.LeafProofs.L12Aux.metricSmooth_of_smoothMetric X.metric
  have hh : MetricFamilySmooth h (Ici 0) :=
    assembledPotentialFlow_metricFamilySmooth X.metric.form hg U (Ici 0) hpos
      (uniqueDiffOn_Ici 0) hU
  have hh0 : h 0 = X.metric.form :=
    assembledPotentialFlow_initial X.metric.form U (Ici 0) hpos (by simp) hU0
  have hP : SmoothSpaceTime (flowLogDetRatio X.metric.form h) (Ici 0) :=
    flowLogDetRatio_smoothSpaceTime X.metric.form hg h hh
  have hPlimit (x : Pt X) (t : ℝ) (ht : 0 ≤ t) :
      Tendsto (fun m => p (σ m) x t) atTop
        (𝓝 (flowLogDetRatio X.metric.form h x t)) := by
    have hDet := frobenius_matrix_det_contDiff.continuous.continuousAt.tendsto.comp
      (hMatrix x t ht)
    have hRe := Complex.reCLM.continuous.continuousAt.tendsto.comp hDet
    have hHpos : 0 < (nativePotentialMatrix X.metric.form U t x).det.re := by
      change 0 < (gMat X.metric.form x - (t : ℂ) • ricci X.metric.form x +
        levi (fun y => U y t) x).det.re
      rw [← hpot t ht x]
      exact Yau.LeafProofs.L12Aux.hMat_det_re_pos (h t) x (mem_extChartAt_target x)
    have hGpos : 0 < (gMat X.metric.form x).det.re :=
      Yau.LeafProofs.L12Aux.hMat_det_re_pos X.metric.form x (mem_extChartAt_target x)
    have hLog := (hRe.div_const (gMat X.metric.form x).det.re).log
      (div_ne_zero hHpos.ne' hGpos.ne')
    have hSeq := hLog.congr' ((hFiniteLog x t ht).mono (fun _ hm => hm.symm))
    change Tendsto (fun m => p (σ m) x t) atTop
      (𝓝 (Real.log ((gMat (h t) x).det.re / (gMat X.metric.form x).det.re)))
    rw [hpot t ht x]
    exact hSeq
  have hFirstId (x : Pt X) (k : ℕ) (t : ℝ) (ht : t ∈ Icc 0 ((k : ℝ) + 1)) :
      derivWithin (U x) (Icc 0 ((k : ℝ) + 1)) t = flowLogDetRatio X.metric.form h x t :=
    actual_clock_derivative_eq_of_same_sequence_limits
      (fun m => f (σ m) x) (fun m => p (σ m) x) (U x)
      (flowLogDetRatio X.metric.form h x t) (by positivity) ht (hFirst x k t ht)
      (hPlimit x t ht.1) ((hFinitePDE x k).mono (fun _ hm => hm t ht))
  have hpde (x : Pt X) (t : ℝ) (ht : 0 ≤ t) :
      HasDerivWithinAt (U x) (flowLogDetRatio X.metric.form h x t) (Ici 0) t := by
    obtain ⟨k, hk⟩ := exists_nat_gt t
    let H := (k : ℝ) + 1
    have htH : t ∈ Icc 0 H := ⟨ht, by dsimp only [H]; linarith⟩
    have hUd : DifferentiableWithinAt ℝ (U x) (Icc 0 H) t :=
      (((smoothSpaceTime_time_slice hU x).mono Icc_subset_Ici_self).differentiableOn
        (by simp)) t htH
    have hd := hUd.hasDerivWithinAt
    rw [hFirstId x k t htH] at hd
    exact hasDerivWithinAt_Ici_of_Icc ht (by dsimp only [H]; linarith) hd
  have hPnonpos (x : Pt X) (t : ℝ) (ht : 0 ≤ t) :
      flowLogDetRatio X.metric.form h x t ≤ 0 := by
    obtain ⟨a, hcap⟩ := hPCap x t ht
    exact nonpositive_of_eventual_inverse_square_cap hLσ (hPlimit x t ht) hcap
  have hPt (x : Pt X) (t : ℝ) (ht : 0 ≤ t) :
      derivWithin (flowLogDetRatio X.metric.form h x) (Ici 0) t ≤ 0 := by
    obtain ⟨k, hk⟩ := exists_nat_gt t
    let H := (k : ℝ) + 1
    have htH : t ∈ Icc 0 H := ⟨ht, by dsimp only [H]; linarith⟩
    obtain ⟨a, hcap⟩ := hSecondCap x k t htH
    have hsign := actual_derivWithin_nonpositive_of_second_clock_limit
      (fun m => f (σ m) x) (U x) (flowLogDetRatio X.metric.form h x) hLσ htH
      (fun s hs => hFirstId x k s hs) (hSecond x k t htH) hcap
    have hPd : DifferentiableWithinAt ℝ (flowLogDetRatio X.metric.form h x) (Ici 0) t :=
      (smoothSpaceTime_time_slice hP x).differentiableOn (by simp) t ht
    have htHlt : t < H := by dsimp only [H]; linarith
    rw [actual_derivWithin_Ici_eq_Icc (flowLogDetRatio X.metric.form h x) (H := H)
      ht htHlt hPd]
    exact hsign
  refine ⟨h, native_global_core_of_actual_potential X h U hh0 hh hU ?_ hpot hU0
    hpde hPnonpos hPt, hPlimit⟩
  intro t ht x
  change HermLE (gMat (h t) x) (gMat X.metric.form x)
  rw [hpot t ht x]
  exact (hLimitOrders x t ht).2

end Yau.NodeProofs.F01Aux
