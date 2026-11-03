import Yau.LeafProofs.L05ChuFrozenEquation
import Yau.LeafProofs.L16InitialTimeCutoff

noncomputable section

open Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic Yau.ParabolicCandidates

def chuCausalTimeCutoff (l r t : ℝ) : ℝ := L16Aux.initialTimeCutoff (r-l) (t-l)

theorem chuCausalTimeCutoff_contDiff (l r : ℝ) : ContDiff ℝ ∞ (chuCausalTimeCutoff l r) := by
  exact (L16Aux.initialTimeCutoff_contDiff (r-l)).comp (contDiff_id.sub contDiff_const)

theorem chuCausalTimeCutoff_mem_Icc (l r t : ℝ) : chuCausalTimeCutoff l r t ∈ Set.Icc (0:ℝ) 1 :=
  L16Aux.initialTimeCutoff_mem_Icc _ _

theorem chuCausalTimeCutoff_zero_before_quarter {l r t : ℝ} (hlr : l < r)
    (ht : t ≤ l+(r-l)/4) : chuCausalTimeCutoff l r t=0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have hpos : 0 < r-l := sub_pos.mpr hlr
  have hh : (4/(r-l))*(t-l) ≤ 1 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hpos).mpr
    linarith only [ht]
  linarith only [hh]

theorem chuCausalTimeCutoff_eventually_zero {l r t : ℝ} (hlr : l < r)
    (ht : t < l+(r-l)/4) : chuCausalTimeCutoff l r =ᶠ[𝓝 t] (fun _ => 0) := by
  filter_upwards [Iio_mem_nhds ht] with s hs
  exact chuCausalTimeCutoff_zero_before_quarter hlr hs.le

theorem chuCausalTimeCutoff_zero_past {l r t : ℝ} (hlr : l < r) (ht : t ≤ l) :
    chuCausalTimeCutoff l r t=0 :=
  chuCausalTimeCutoff_zero_before_quarter hlr (by linarith only [ht,hlr])

theorem chuCausalTimeCutoff_deriv_zero_past {l r t : ℝ} (hlr : l < r) (ht : t ≤ l) :
    deriv (chuCausalTimeCutoff l r) t=0 := by
  have hh := (chuCausalTimeCutoff_eventually_zero (t := t) hlr (by linarith only [ht,hlr])).deriv_eq
  simpa only [deriv_const] using hh

theorem chuCausalTimeCutoff_one_late {l r t : ℝ} (hlr : l < r) (ht : (l+r)/2 ≤ t) :
    chuCausalTimeCutoff l r t=1 := by
  exact L16Aux.initialTimeCutoff_eq_one (sub_pos.mpr hlr) (by linarith only [ht])

theorem chu_frozen_cutoff_zero_past {n : ℕ} {T : Sym n → Point n → Sym n} {K beta : ℝ}
    (hT : ChuH2 T K beta) (F : Sym n → Point n → ℝ) (A0 : Sym n) (p0 : Point n)
    (hp0 : p0 ∈ backward 1) (phi : Space n → ℝ) (u : Point n → ℝ)
    {l r : ℝ} (hlr : l < r) {p : Point n} (hp : p.2 ≤ l) :
    chuCausalTimeCutoff l r p.2*(phi p.1*u p)=0 ∧
      chuFrozenCutoffSource hT F A0 p0 hp0 phi (chuCausalTimeCutoff l r) u p=0 := by
  rw [chuCausalTimeCutoff_zero_past hlr hp,zero_mul]
  refine ⟨rfl,?_⟩
  unfold chuFrozenCutoffSource
  rw [chuCausalTimeCutoff_zero_past hlr hp,chuCausalTimeCutoff_deriv_zero_past hlr hp]
  ring

end Yau.LeafProofs.L05Aux
