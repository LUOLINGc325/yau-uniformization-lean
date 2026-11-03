import Yau.Proofs.C05ScalarHarnack
import Yau.Proofs.C04ClockBasic
import Yau.Proofs.C04Scaling

/-! The center defect is exactly the normalized derivative in the original
RicciWindows sequence. The metric and clock are unchanged. -/

noncomputable section
namespace Yau.Proofs.C05Aux
open Yau Blueprint C04Aux Filter
variable {n : ℕ} {X : KahlerManifold n}

theorem clockSpeed_deriv_eq_scalarHarnackSum (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) {t : ℝ} (ht : 0 < t) :
    deriv (clockSpeed o h) t = t * scalarHarnackSum h o t := by
  have hd := (scalar_contDiffAt X o h U P ρ hf o ht).differentiableAt (by simp)
  have hq := (hasDerivAt_id t).mul hd.hasDerivAt
  change deriv (id * fun s => scalarCurvature (h s) o) t = _
  rw [hq.deriv]
  simp only [id_eq, one_mul]
  dsimp only [scalarHarnackSum]
  field_simp [ht.ne']
  ring

theorem normalized_center_defect_eq_clock_ratio (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) {t : ℝ} (ht : 0 < t)
    (hR : 0 < scalarCurvature (h t) o) :
    scalarHarnackSum h o t / scalarCurvature (h t) o ^ 2 =
      deriv (clockSpeed o h) t /
        (clockSpeed o h t * scalarCurvature (h t) o) := by
  rw [clockSpeed_deriv_eq_scalarHarnackSum o h U P ρ hf ht]
  dsimp only [clockSpeed]
  field_simp [ht.ne', hR.ne']

theorem rescaled_scalar_hasDerivAt (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) (ti R : ℝ) (hR : 0 < R) (x : Pt X)
    (z : ℝ) (ht : 0 < ti + z / R) :
    HasDerivAt (fun s => scalarCurvature (scaleField R hR (h (ti + s / R))) x)
      (deriv (fun s => scalarCurvature (h s) x) (ti + z / R) / R ^ 2) z := by
  have hd := (scalar_contDiffAt X o h U P ρ hf x ht).differentiableAt (by simp)
  have hc := (hd.hasDerivAt.comp z (((hasDerivAt_id z).div_const R).const_add ti)).const_mul R⁻¹
  simp_rw [scalar_scaleField]
  convert hc using 1 <;> try simp only [Function.comp_def, id_eq]
  all_goals field_simp [hR.ne'] <;> ring

theorem normalized_center_defect_tendsto (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) (tw : ℕ → ℝ)
    (htw : ∀ i, 0 < tw i) (hR : ∀ i, 0 < scalarCurvature (h (tw i)) o)
    (hgood : Tendsto (fun i => deriv (clockSpeed o h) (tw i) /
      (clockSpeed o h (tw i) * scalarCurvature (h (tw i)) o)) atTop (nhds 0)) :
    Tendsto (fun i => scalarHarnackSum h o (tw i) /
      scalarCurvature (h (tw i)) o ^ 2) atTop (nhds 0) := by
  convert hgood using 1
  funext i
  exact normalized_center_defect_eq_clock_ratio o h U P ρ hf (htw i) (hR i)

end Yau.Proofs.C05Aux
