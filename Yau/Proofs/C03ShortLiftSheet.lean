import Yau.Proofs.C03ShortLiftCurves
import Yau.Proofs.C03ShortLiftFamilies
import Yau.Proofs.C03ShortLiftInverse
import Yau.Proofs.C03ShortLiftTarget

/-! One actual holomorphic inverse sheet is obtained from the same family of short lifts. -/
noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Set Filter unitInterval
namespace Yau.Proofs.C03Aux.ShortLift
open Yau Yau.Blueprint Yau.LeafProofs L12Aux
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {M : ComplexManifold n}

theorem exists_short_inverse_section
    (k : HermitianField M) (hs : MetricSmooth k)
    (Phi : ComplexVector n → M.Carrier) (r c : ℝ) (hr : 0 < r) (hc : 0 < c)
    (hPhi : IsLocalBiholomorphism Phi r)
    (hlo : ∀ z ∈ Metric.ball 0 r, HermLE ((c : ℂ) • (1 : Herm n)) (pullbackMat k Phi z))
    (ctarget : M.Carrier) (w0 : ComplexVector n) (delta L : ℝ)
    (hdelta : 0 < delta) (hL : 0 < L)
    (hW : Metric.ball w0 delta ⊆ chartTarget ctarget)
    (hp0 : Phi 0 = chartInv ctarget w0)
    (hG : ∀ q ∈ Metric.ball w0 delta, ∀ v : ComplexVector n,
      realMetricInChart k ctarget q v v ≤ L ^ 2 * ‖v‖ ^ 2)
    (hshort : L * delta < Real.sqrt (2 * c) * r) :
    ∃ sigma : ComplexVector n → ComplexVector n,
      sigma w0 = 0 ∧ ContDiffOn ℂ ∞ sigma (Metric.ball w0 delta) ∧
      MapsTo sigma (Metric.ball w0 delta) (Metric.ball 0 r) ∧
      (∀ w ∈ Metric.ball w0 delta, Phi (sigma w) = chartInv ctarget w) ∧
      ∀ w ∈ Metric.ball w0 delta,
        ‖sigma w‖ ≤ (Real.sqrt (2 * c))⁻¹ * (L * ‖w - w0‖) := by
  classical
  let W : Set (ComplexVector n) := Metric.ball w0 delta
  have hF := targetParameter_smooth ctarget w0 delta hW
  have hF0 : targetParameter ctarget w0 0 = Phi 0 := by
    simpa only [targetParameter, add_zero] using hp0.symm
  have hGamma (w : W) :
      ∃ gamma : IntegrableCurve k (Phi 0) (chartInv ctarget w),
        (∀ t ∈ Icc (0 : ℝ) 1, gamma.1 t =
          chartInv ctarget (w0 + t • ((w : ComplexVector n) - w0))) ∧
        curveLength k gamma.1 ≤ L * ‖(w : ComplexVector n) - w0‖ := by
    have hw : ‖(w : ComplexVector n) - w0‖ < delta := by
      simpa only [W, Metric.mem_ball, dist_eq_norm] using w.2
    have hex := exists_radial_curve hs hF0 hF hL
      (fun q hq v => targetParameter_upper k ctarget w0 delta L hW hG q hq v) hw
    have hpoint : targetParameter ctarget w0 ((w : ComplexVector n) - w0) =
        chartInv ctarget w := by
      unfold targetParameter
      congr 1
      abel
    rw [hpoint] at hex
    simpa only [targetParameter] using hex
  choose gamma hgamma hlength using hGamma
  have halpha : 0 < Real.sqrt (2 * c) := Real.sqrt_pos.mpr (by positivity)
  have hEta (w : W) :
      ∃ eta : ℝ → ComplexVector n,
        ContinuousOn eta (Icc (0 : ℝ) 1) ∧ eta 0 = 0 ∧
        (∀ t ∈ Icc (0 : ℝ) 1, eta t ∈ Metric.ball 0 r ∧ Phi (eta t) = (gamma w).1 t) ∧
        (∀ t ∈ Icc (0 : ℝ) 1, ‖eta t‖ ≤
          (Real.sqrt (2 * c))⁻¹ * (∫ u in Icc 0 t, curveSpeed k (gamma w).1 u)) := by
    have hw : ‖(w : ComplexVector n) - w0‖ < delta := by
      simpa only [W, Metric.mem_ball, dist_eq_norm] using w.2
    apply short_curve_lift hr hc hPhi hlo (gamma w)
    exact (hlength w).trans_lt ((mul_lt_mul_of_pos_left hw hL).trans hshort)
  choose eta hetac heta0 hetap hetanorm using hEta
  let g : I × W → ComplexVector n := fun q => eta q.2 q.1
  let coord : I × W → ComplexVector n :=
    fun q => w0 + (q.1 : ℝ) • ((q.2 : ComplexVector n) - w0)
  have hcoord : Continuous coord :=
    continuous_const.add ((continuous_subtype_val.comp continuous_fst).smul
      ((continuous_subtype_val.comp continuous_snd).sub continuous_const))
  have hcoordW (q : I × W) : coord q ∈ W :=
    radial_target_mem q.2.2 q.1.2
  let f : C(I × W, M.Carrier) :=
    ⟨fun q => chartInv ctarget (coord q),
      (contMDiffOn_extChartAt_symm («I» := ComplexModel n) (n := ∞) ctarget).continuousOn.comp_continuous
        hcoord (fun q => hW (hcoordW q))⟩
  have hg : Phi ∘ g = f := by
    funext q
    exact ((hetap q.2) q.1 q.1.2).2.trans (hgamma q.2 q.1 q.1.2)
  have hgmem (q : I × W) : g q ∈ Metric.ball 0 r := ((hetap q.2) q.1 q.1.2).1
  have hg0 : Continuous (fun w : W => g (0, w)) := by
    have heq : (fun w : W => g (0, w)) = (fun _ => 0) := funext heta0
    rw [heq]
    exact continuous_const
  have hgpath (w : W) : Continuous (fun t : I => g (t, w)) :=
    (hetac w).comp_continuous continuous_subtype_val (fun t => t.2)
  have hEnd : Continuous (fun w : W => eta w 1) :=
    continuous_lift_endpoints_on Phi (Metric.ball 0 r) Metric.isOpen_ball
      ⟨0, by simpa using hr⟩
      (fun z hz => C07Aux.local_homeomorph_of_localBiholomorphism hPhi hz)
      f g hgmem hg hg0 hgpath
  let sigma : ComplexVector n → ComplexVector n :=
    fun w => if hw : w ∈ W then eta ⟨w, hw⟩ 1 else 0
  have hsigma (w : W) : sigma w = eta w 1 := by simp [sigma, w.2]
  have hsigmac : ContinuousOn sigma W := by
    apply continuousOn_iff_continuous_restrict.mpr
    convert hEnd using 1
    funext w
    exact hsigma w
  have hsigmamem : MapsTo sigma W (Metric.ball 0 r) := by
    intro w hw
    rw [hsigma ⟨w, hw⟩]
    exact ((hetap ⟨w, hw⟩) 1 ⟨zero_le_one, le_rfl⟩).1
  have hright : ∀ w ∈ W, Phi (sigma w) = chartInv ctarget w := by
    intro w hw
    rw [hsigma ⟨w, hw⟩]
    exact (((hetap ⟨w, hw⟩) 1 ⟨zero_le_one, le_rfl⟩).2).trans (gamma ⟨w, hw⟩).1.finish_eq
  have hnorm : ∀ w ∈ W,
      ‖sigma w‖ ≤ (Real.sqrt (2 * c))⁻¹ * (L * ‖w - w0‖) := by
    intro w hw
    rw [hsigma ⟨w, hw⟩]
    have H := (hetanorm ⟨w, hw⟩) 1 ⟨zero_le_one, le_rfl⟩
    change ‖eta ⟨w, hw⟩ 1‖ ≤
      (Real.sqrt (2 * c))⁻¹ * curveLength k (gamma ⟨w, hw⟩).1 at H
    exact H.trans (mul_le_mul_of_nonneg_left (hlength ⟨w, hw⟩) (inv_nonneg.mpr halpha.le))
  have hw0 : w0 ∈ W := Metric.mem_ball_self hdelta
  have hsigma0 : sigma w0 = 0 := by
    apply norm_eq_zero.mp
    exact le_antisymm (by simpa only [sub_self, norm_zero, mul_zero] using hnorm w0 hw0)
      (norm_nonneg _)
  exact ⟨sigma, hsigma0, section_contDiffOn hPhi ctarget Metric.isOpen_ball sigma
    hsigmac hsigmamem hW hright, hsigmamem, hright, hnorm⟩

end Yau.Proofs.C03Aux.ShortLift

