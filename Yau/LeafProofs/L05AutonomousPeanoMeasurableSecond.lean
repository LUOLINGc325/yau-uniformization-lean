import Yau.LeafProofs.L05AutonomousDifferences
import Mathlib.Analysis.Asymptotics.Lemmas

noncomputable section
open Filter Set MeasureTheory Asymptotics
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

def peanoDyadicStep (j : ℕ) : ℝ := (1/2 : ℝ)^j

theorem peanoDyadicStep_pos (j : ℕ) : 0 < peanoDyadicStep j :=
  pow_pos (by norm_num : (0 : ℝ) < 1/2) j

theorem peanoDyadicStep_tendsto : Tendsto peanoDyadicStep atTop (𝓝[>] (0 : ℝ)) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_,Eventually.of_forall peanoDyadicStep_pos⟩
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

/-- The literal increment remainder of a spatial Peano polynomial. -/
def peanoSpatialRemainder {n : ℕ} (u : Point n → ℝ) (p : Point n)
    (l : Space n →L[ℝ] ℝ) (B : Space n →L[ℝ] Space n →L[ℝ] ℝ)
    (v : Space n) : ℝ :=
  u (p.1+v,p.2)-u p-l v-(1/2 : ℝ)*B v v

theorem peano_second_remainder_identity {n : ℕ} (u : Point n → ℝ) (p : Point n)
    (l : Space n →L[ℝ] ℝ) (B : Space n →L[ℝ] Space n →L[ℝ] ℝ)
    (e : Space n) {h : ℝ} (hh : h ≠ 0) :
    (peanoSpatialRemainder u p l B (h • e)+
      peanoSpatialRemainder u p l B (h • (-e)))/h^2 = autoSecond u e h p-B e e := by
  simp only [peanoSpatialRemainder,autoSecond,smul_neg,map_smul,
    smul_apply,smul_eq_mul,map_neg,neg_apply,neg_neg,sub_eq_add_neg]
  field_simp [hh] <;> ring

/-- A Peano remainder yields every actual centered directional second limit;
no actual second Fréchet derivative is assumed or asserted. -/
theorem peano_second_limit {n : ℕ} {u : Point n → ℝ} {p : Point n}
    {l : Space n →L[ℝ] ℝ} {B : Space n →L[ℝ] Space n →L[ℝ] ℝ}
    (hRem : (fun y => u (y,p.2)-u p-l (y-p.1)-(1/2 : ℝ)*B (y-p.1) (y-p.1))
      =o[𝓝 p.1] (fun y => ‖y-p.1‖^2)) (e : Space n) :
    Tendsto (fun h => autoSecond u e h p) (𝓝[>] (0 : ℝ)) (𝓝 (B e e)) := by
  have hPath (v : Space n) : Tendsto (fun h : ℝ => p.1+h • v)
      (𝓝[>] (0 : ℝ)) (𝓝 p.1) := by
    have hc : Continuous (fun h : ℝ => p.1+h • v) :=
      continuous_const.add (continuous_id.smul continuous_const)
    simpa only [zero_smul,add_zero] using (hc.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hScale (v : Space n) : (fun h : ℝ => ‖p.1+h • v-p.1‖^2)
      =O[𝓝[>] (0 : ℝ)] (fun h => h^2) := by
    apply IsBigO.of_bound (‖v‖^2)
    filter_upwards with h
    simp only [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,abs_mul,abs_sq]
    exact le_of_eq (mul_comm _ _)
  have hInc (v : Space n) : (fun h : ℝ => peanoSpatialRemainder u p l B (h • v))
      =o[𝓝[>] (0 : ℝ)] (fun h => h^2) := by
    have hh := (hRem.comp_tendsto (hPath v)).trans_isBigO (hScale v)
    simpa only [Function.comp_def,add_sub_cancel_left,peanoSpatialRemainder] using hh
  have hZero := ((hInc e).add (hInc (-e))).tendsto_div_nhds_zero
  have hEq : (fun h : ℝ => (peanoSpatialRemainder u p l B (h • e)+
      peanoSpatialRemainder u p l B (h • (-e)))/h^2)
      =ᶠ[𝓝[>] (0 : ℝ)] (fun h => autoSecond u e h p-B e e) := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact peano_second_remainder_identity u p l B e (ne_of_gt hh)
  have hLimit := (hZero.congr' hEq).add_const (B e e)
  simpa only [sub_add_cancel,zero_add] using hLimit

theorem peano_second_dyadic_limit {n : ℕ} {u : Point n → ℝ} {p : Point n}
    {l : Space n →L[ℝ] ℝ} {B : Space n →L[ℝ] Space n →L[ℝ] ℝ}
    (hRem : (fun y => u (y,p.2)-u p-l (y-p.1)-(1/2 : ℝ)*B (y-p.1) (y-p.1))
      =o[𝓝 p.1] (fun y => ‖y-p.1‖^2)) (e : Space n) :
    Tendsto (fun j => autoSecond u e (peanoDyadicStep j) p) atTop (𝓝 (B e e)) :=
  (peano_second_limit hRem e).comp peanoDyadicStep_tendsto

end Yau.LeafProofs.L05AutonomousAux
