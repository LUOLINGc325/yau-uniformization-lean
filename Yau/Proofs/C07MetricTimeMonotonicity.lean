import Yau.Proofs.C07MetricOrder
import Yau.Proofs.C07StripMonotonicity
import Yau.Proofs.Y03FlowLevi
import Yau.Blueprint.Nodes

/-! E03's actual cotangent/time Levi inequality makes the same flow metrics decrease. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter Set

noncomputable section

namespace Yau.Proofs.C07Aux

open Yau Yau.Blueprint Yau.Blueprint.Alignment
open Yau.Blueprint.Alignment.Y03Proof

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {X : KahlerManifold n} {o : Pt X}
    {h : Flow X} {U P ρ : STF X}

theorem fixed_dualNorm_continuousOn (hflow : FlowStage X o h U P ρ)
    (x : Pt X) (ξ : ComplexVector n) :
    ContinuousOn (fun t => dualNormMat (gMat (h t) x) ξ) (Ici 0) := by
  have hsmooth : MetricFamilySmooth h (Ici 0) := hflow.1.1.2.1
  have hcoeff (i j : Fin n) :
      ContinuousOn (fun t => (gMat (h t) x)⁻¹ i j) (Ici 0) := by
    change ContinuousOn (fun t => (hMat (h t) x (chartPt x x))⁻¹ i j) (Ici 0)
    let q : ℝ → ComplexVector n × ℝ := fun t => (chartPt x x, t)
    have hc : ContinuousOn q (Ici 0) :=
      (continuous_const.prodMk continuous_id).continuousOn
    have hq : Set.MapsTo q (Ici 0) (chartTarget x ×ˢ Ici 0) :=
      fun t ht => ⟨mem_extChartAt_target x, ht⟩
    have hbase : ContinuousOn
        (fun p : ComplexVector n × ℝ => (hMat (h p.2) x p.1)⁻¹ i j)
        (chartTarget x ×ˢ Ici 0) :=
      (metricFamily_hMat_inv_contDiffOn hsmooth x i j).continuousOn
    simpa only [Function.comp_def, q] using hbase.comp (f := q) hc hq
  unfold dualNormMat Matrix.mulVec dotProduct
  apply Complex.continuous_re.comp_continuousOn
  apply continuousOn_finsetSum
  intro i _
  apply continuousOn_const.mul
  apply continuousOn_finsetSum
  intro j _
  exact (hcoeff j i).mul continuousOn_const

theorem joint_dualNorm_interval_maximum (hflow : FlowStage X o h U P ρ)
    (hjoint : JointPositiveClock X h) (x : Pt X) (ξ : ComplexVector n)
    {a b t : ℝ} (ha : 0 < a) (hat : a ≤ t) (htb : t ≤ b) :
    dualNormMat (gMat (h t) x) ξ ≤
      max (dualNormMat (gMat (h a) x) ξ) (dualNormMat (gMat (h b) x) ξ) := by
  let N : ℝ → ℝ := fun s => dualNormMat (gMat (h s) x) ξ
  by_cases hab : a = b
  · have ht : t = a := le_antisymm (htb.trans hab.symm.le) hat
    simpa only [ht] using le_max_left (N a) (N b)
  have hab' : a < b := lt_of_le_of_ne (hat.trans htb) hab
  have hb : 0 < b := ha.trans hab'
  have ht : 0 < t := ha.trans_le hat
  let T := Real.log b - Real.log a
  have hT : 0 < T := sub_pos.mpr (Real.log_lt_log ha hab')
  let γ : ℂ → ComplexVector n × ComplexVector n × ℂ :=
    fun w => (chartPt x x, ξ, ((Real.log a : ℂ) + w) / 2)
  have htime (w : ℂ) : Real.exp (2 * (γ w).2.2.re) = a * Real.exp w.re := by
    have hre : 2 * (γ w).2.2.re = Real.log a + w.re := by
      norm_num [γ, Complex.div_re]
      ring
    rw [hre, Real.exp_add, Real.exp_log ha]
  have hNγ (w : ℂ) :
      dualNormChart (h (Real.exp (2 * (γ w).2.2.re))) x (γ w).1 (γ w).2.1 =
        N (a * Real.exp w.re) := by rw [htime]; rfl
  have hfinish : a * Real.exp T = b := by
    rw [Real.exp_sub, Real.exp_log hb, Real.exp_log ha]
    exact mul_div_cancel₀ b ha.ne'
  have hinside {w : ℂ} (hw₀ : 0 ≤ w.re) (hwT : w.re ≤ T) :
      a * Real.exp w.re ∈ Icc a b := by
    constructor
    · calc
        a = a * Real.exp 0 := by simp
        _ ≤ a * Real.exp w.re := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hw₀) ha.le
    · calc
        a * Real.exp w.re ≤ a * Real.exp T :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hwT) ha.le
        _ = b := hfinish
  have hNc : ContinuousOn N (Icc a b) :=
    (fixed_dualNorm_continuousOn hflow x ξ).mono fun s hs => ha.le.trans hs.1
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hNc
  have hγ : ∀ w : ℂ, ContDiffAt ℂ 2 γ w := by
    have hc : ContDiff ℂ 2 γ := by dsimp only [γ]; fun_prop
    exact fun _ => hc.contDiffAt
  have hbound : ∀ w : ℂ, 0 ≤ w.re → w.re ≤ T →
      dualNormChart (h (Real.exp (2 * (γ w).2.2.re))) x (γ w).1 (γ w).2.1 ≤ B := by
    intro w hw₀ hwT
    rw [hNγ]
    exact (le_abs_self _).trans (hB _ (hinside hw₀ hwT))
  have hleft : ∀ y : ℝ,
      dualNormChart (h (Real.exp (2 * (γ ((y : ℂ) * Complex.I)).2.2.re))) x
        (γ ((y : ℂ) * Complex.I)).1 (γ ((y : ℂ) * Complex.I)).2.1 ≤ max (N a) (N b) := by
    intro y
    rw [hNγ]
    simpa using le_max_left (N a) (N b)
  have hright : ∀ y : ℝ,
      dualNormChart (h (Real.exp (2 * (γ ((T : ℂ) + (y : ℂ) * Complex.I)).2.2.re))) x
        (γ ((T : ℂ) + (y : ℂ) * Complex.I)).1
        (γ ((T : ℂ) + (y : ℂ) * Complex.I)).2.1 ≤ max (N a) (N b) := by
    intro y
    rw [hNγ]
    have hre : ((T : ℂ) + (y : ℂ) * Complex.I).re = T := by simp
    rw [hre, hfinish]
    exact le_max_right _ _
  have hmax := jointPositiveClock_bounded_strip hflow hjoint x γ T (max (N a) (N b)) B hT
    hγ (fun _ _ _ => mem_extChartAt_target x) hbound hleft hright
  have hlog₀ : 0 ≤ Real.log t - Real.log a := sub_nonneg.mpr (Real.log_le_log ha hat)
  have hlogT : Real.log t - Real.log a ≤ T :=
    sub_le_sub_right (Real.log_le_log ht htb) _
  have hAt : a * Real.exp (Real.log t - Real.log a) = t := by
    rw [Real.exp_sub, Real.exp_log ht, Real.exp_log ha]
    exact mul_div_cancel₀ t ha.ne'
  have hfinal := hmax ((Real.log t - Real.log a : ℝ) : ℂ) hlog₀ hlogT
  rw [hNγ, Complex.ofReal_re, hAt] at hfinal
  exact hfinal

theorem joint_metric_antitone (hflow : FlowStage X o h U P ρ)
    (hjoint : JointPositivity X h) (x : Pt X) {t u : ℝ}
    (ht : 0 ≤ t) (htu : t ≤ u) : HermLE (gMat (h u) x) (gMat (h t) x) := by
  have hgpos (k : HermitianField X.manifold) : (gMat k x).PosDef :=
    hMat_posDef k x (chartPt x x) (mem_extChartAt_target x)
  have hmin (ξ : ComplexVector n) (s : ℝ) (hs : 0 < s) :
      dualNormMat (gMat (h 0) x) ξ ≤ dualNormMat (gMat (h s) x) ξ := by
    rcases hflow.1 with ⟨hkrf, _, _, _, hdom, _⟩
    rw [hkrf.1]
    exact (hermLE_iff_dualNormMat_le (hgpos (h s)) (hgpos X.metric.form)).mp
      (hdom s hs.le x) ξ
  have hmono (ξ : ComplexVector n) :
      MonotoneOn (fun s => dualNormMat (gMat (h s) x) ξ) (Ioi 0) :=
    monotoneOn_of_interval_maximum
      ((fixed_dualNorm_continuousOn hflow x ξ).continuousWithinAt (by simp))
      (hmin ξ) (joint_dualNorm_interval_maximum hflow hjoint.1 x ξ)
  by_cases htzero : t = 0
  · rcases hflow.1 with ⟨hkrf, _, _, _, hdom, _⟩
    rw [htzero, hkrf.1]
    exact hdom u (ht.trans htu) x
  · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm htzero)
    exact (hermLE_iff_dualNormMat_le (hgpos (h u)) (hgpos (h t))).mpr
      (fun ξ => hmono ξ htpos (htpos.trans_le htu) htu)

end Yau.Proofs.C07Aux
