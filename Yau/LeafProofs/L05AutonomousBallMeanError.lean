import Yau.LeafProofs.L05AutonomousBallMeanBoundary
import Yau.LeafProofs.L05AutonomousBallMeanShell

open Set Filter MeasureTheory Metric
open scoped Topology Interval
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic

def autoGreenCutoffError (d : ℕ) (omega r s q1 q2 : ℝ) : ℝ :=
  autoGreenPrimitive d omega r s*q2+
    2*(-autoGreenIntegrand d r s/((d : ℝ)*omega))*q1+
    ((d : ℝ)-1)/s*autoGreenPrimitive d omega r s*q1

theorem auto_green_cutoff_error_weight {d : ℕ} (hd : 1 ≤ d) (omega r : ℝ)
    {s : ℝ} (hs : 0 < s) (q1 q2 : ℝ) :
    s^(d-1)*|autoGreenCutoffError d omega r s q1 q2| ≤
      |s^(d-1)*autoGreenPrimitive d omega r s| *|q2|+
      2*|s^(d-1)*(-autoGreenIntegrand d r s/((d : ℝ)*omega))| *|q1|+
      ((d : ℝ)-1)/s*|s^(d-1)*autoGreenPrimitive d omega r s| *|q1| := by
  have hp : 0 ≤ s^(d-1) := pow_nonneg hs.le _
  have hd0 : 0 ≤ (d : ℝ)-1 := by
    have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hCoeff : 0 ≤ ((d : ℝ)-1)/s := div_nonneg hd0 hs.le
  have h := mul_le_mul_of_nonneg_left
    (abs_add_le (autoGreenPrimitive d omega r s*q2+2*(-autoGreenIntegrand d r s/((d : ℝ)*omega))*q1)
      (((d : ℝ)-1)/s*autoGreenPrimitive d omega r s*q1)) hp
  have hAdd := abs_add_le (autoGreenPrimitive d omega r s*q2)
      (2*(-autoGreenIntegrand d r s/((d : ℝ)*omega))*q1)
  have hTot := h.trans (mul_le_mul_of_nonneg_left (add_le_add hAdd le_rfl) hp)
  dsimp only [autoGreenCutoffError]
  simp only [abs_mul,abs_of_nonneg hp,abs_of_nonneg hCoeff,abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at hTot ⊢
  convert hTot using 1; ring

theorem auto_green_inner_error_bound {d : ℕ} (hd : 1 ≤ d) (omega r : ℝ)
    {eta s v L B1 B2 eps D q1 q2 : ℝ}
    (heta : 0 < eta) (hs : s∈Icc eta (2*eta))
    (hL : 0 ≤ L) (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2) (heps : 0 ≤ eps) (hD : 0 ≤ D)
    (hv : |v| ≤ L*s)
    (hM : |s^(d-1)*autoGreenPrimitive d omega r s| ≤ eps)
    (hN : |s^(d-1)*(-autoGreenIntegrand d r s/((d : ℝ)*omega))| ≤ D)
    (hq1 : |q1| ≤ B1/eta) (hq2 : |q2| ≤ B2/eta^2) :
    s^(d-1)*|v*autoGreenCutoffError d omega r s q1 q2| ≤
      L*eps*(2*B2+((d : ℝ)-1)*B1)/eta+4*L*D*B1 := by
  have hsp : 0 < s := heta.trans_le hs.1
  have hd0 : 0 ≤ (d : ℝ)-1 := by
    have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hCoeff : 0 ≤ ((d : ℝ)-1)/s := div_nonneg hd0 hsp.le
  have hW := auto_green_cutoff_error_weight hd omega r hsp q1 q2
  have hE : s^(d-1)*|autoGreenCutoffError d omega r s q1 q2| ≤
      eps*(B2/eta^2)+2*D*(B1/eta)+((d : ℝ)-1)/s*eps*(B1/eta) := by
    apply hW.trans
    gcongr
  calc
    _ = |v| *(s^(d-1)*|autoGreenCutoffError d omega r s q1 q2|) := by rw [abs_mul]; ring
    _ ≤ (L*s)*(eps*(B2/eta^2)+2*D*(B1/eta)+((d : ℝ)-1)/s*eps*(B1/eta)) := by
      gcongr
    _ = L*eps*B2*s/eta^2+2*L*D*B1*s/eta+L*((d : ℝ)-1)*eps*B1/eta := by
      field_simp [hsp.ne',heta.ne']
    _ ≤ L*eps*B2*(2*eta)/eta^2+2*L*D*B1*(2*eta)/eta+L*((d : ℝ)-1)*eps*B1/eta := by
      gcongr <;> exact hs.2
    _ = _ := by field_simp [heta.ne']; ring

end Yau.LeafProofs.L05AutonomousAux

namespace Yau.LeafProofs.L05AutonomousAux

theorem auto_green_inner_shell_control {d : ℕ} (hd : 2 ≤ d) (omega : ℝ) {r : ℝ} (hr : 0 < r) :
    ∃ D : ℝ, 0 < D ∧ ∀ eps : ℝ, 0 < eps → ∃ delta : ℝ, 0 < delta ∧ delta < r/4 ∧
      ∀ eta : ℝ, 0 < eta → eta < delta → ∀ s∈Icc eta (2*eta),
        |s^(d-1)*autoGreenPrimitive d omega r s| ≤ eps ∧
        |s^(d-1)*(-autoGreenIntegrand d r s/((d : ℝ)*omega))| ≤ D := by
  have hM : Tendsto (fun s : ℝ => |s^(d-1)*autoGreenPrimitive d omega r s|)
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.norm_eq_abs,norm_zero] using (auto_green_inner_value_flux hd omega hr).norm
  have hN : Tendsto (fun s : ℝ => |s^(d-1)*(-autoGreenIntegrand d r s/((d : ℝ)*omega))|)
      (𝓝[>] 0) (𝓝 |-1/((d : ℝ)*omega)|) := by
    simpa only [Real.norm_eq_abs] using (auto_green_inner_derivative_flux (by omega : 0 < d) omega r).norm
  let D : ℝ := |-1/((d : ℝ)*omega)|+1
  have hD : 0 < D := by dsimp only [D]; positivity
  have hNE : ∀ᶠ s : ℝ in 𝓝[>] 0,
      |s^(d-1)*(-autoGreenIntegrand d r s/((d : ℝ)*omega))| < D :=
    (tendsto_order.mp hN).2 D (by dsimp only [D]; linarith)
  obtain ⟨deltaN,hdN,hNsmall⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp hNE
  refine ⟨D,hD,?_⟩
  intro eps heps
  have hME : ∀ᶠ s : ℝ in 𝓝[>] 0, |s^(d-1)*autoGreenPrimitive d omega r s| < eps :=
    (tendsto_order.mp hM).2 eps heps
  obtain ⟨deltaM,hdM,hMsmall⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp hME
  let delta := min (r/8) (min (deltaM/2) (deltaN/2))
  have hdelta : 0 < delta := lt_min (by positivity) (lt_min (by simpa only [mem_Ioi] using half_pos hdM)
    (by simpa only [mem_Ioi] using half_pos hdN))
  refine ⟨delta,hdelta,?_,?_⟩
  · have h := min_le_left (r/8) (min (deltaM/2) (deltaN/2))
    dsimp only [delta] at ⊢
    linarith
  · intro eta heta hed s hs
    have hdM' : delta ≤ deltaM/2 := (min_le_right _ _).trans (min_le_left _ _)
    have hdN' : delta ≤ deltaN/2 := (min_le_right _ _).trans (min_le_right _ _)
    exact ⟨(hMsmall ⟨heta.trans_le hs.1,by linarith [hs.2]⟩).le,
      (hNsmall ⟨heta.trans_le hs.1,by linarith [hs.2]⟩).le⟩

end Yau.LeafProofs.L05AutonomousAux
