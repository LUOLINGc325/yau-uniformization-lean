import Yau.Proofs.C05OriginalFiniteJetTubes
import Yau.Proofs.C04Clock

/-! A fixed positive-time interval and inverse-clock bound follow from
the original monotone scalar clock along the original good sequence. -/
noncomputable section
open Filter Set
open scoped Topology Manifold ContDiff
namespace Yau.Proofs.C05Aux
open Yau Blueprint C04Aux
variable {n : ℕ} {X : KahlerManifold n}

theorem eventual_original_normalized_clock_control (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) (hH : HarnackCompleteness X o h)
    (tw : ℕ → ℝ) (htwinf : Tendsto tw atTop atTop)
    (hRi : ∀ i, 0 < scalarCurvature (h (tw i)) o) {θ : ℝ} (hθ : 0 < θ) :
    ∃ δ : ℝ, 0 < δ ∧ δ < θ ∧ ∃ K : ℝ, 0 < K ∧
      ∀ᶠ i in atTop, ∀ z : ℝ, |z| < δ →
        0 < tw i+z/scalarCurvature (h (tw i)) o ∧
          |(tw i*scalarCurvature (h (tw i)) o+z)⁻¹| ≤ K := by
  obtain ⟨c,hc,hclock⟩ := clockSpeed_positive_lower X o h U P ρ hf hH
  let δ := min (θ/2) (c/2)
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδθ : δ < θ := (min_le_left _ _).trans_lt (by linarith)
  have hδc : δ ≤ c/2 := min_le_right _ _
  refine ⟨δ,hδ,hδθ,2/c,by positivity,?_⟩
  have htwone : ∀ᶠ i in atTop, 1 ≤ tw i := htwinf.eventually (eventually_ge_atTop (1:ℝ))
  filter_upwards [htwone] with i hi
  intro z hz
  have hq : c ≤ tw i*scalarCurvature (h (tw i)) o := hclock (tw i) hi
  have hzlo := (abs_lt.mp hz).1
  have hhalf : c/2 < tw i*scalarCurvature (h (tw i)) o+z := by linarith
  have hqpos : 0 < tw i*scalarCurvature (h (tw i)) o+z := (by positivity : (0:ℝ)<c/2).trans hhalf
  constructor
  · have he : tw i+z/scalarCurvature (h (tw i)) o =
        (tw i*scalarCurvature (h (tw i)) o+z)/scalarCurvature (h (tw i)) o := by
      field_simp [(hRi i).ne']
    rw [he]
    exact div_pos hqpos (hRi i)
  · rw [abs_of_pos (inv_pos.mpr hqpos)]
    calc
      _ ≤ (c/2)⁻¹ := by
        simpa only [one_div] using (one_div_le_one_div_of_le
          (by positivity : (0:ℝ)<c/2) hhalf.le)
      _ = 2/c := by field_simp [hc.ne']

end Yau.Proofs.C05Aux
