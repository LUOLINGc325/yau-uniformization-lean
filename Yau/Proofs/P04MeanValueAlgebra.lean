import Yau.Proofs.P04UnitBallVolume
import Yau.Proofs.P04WeightedBallBound

noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace Yau.Proofs.P04Aux

/-- Extended-real mean-value and actual volume inequalities imply a finite
pointwise bound. Adding one to the norm handles also the zero-norm case. -/
theorem point_bound_of_weighted_meanvalue {u c e p : ℝ}
    (hu : 0 ≤ u) (hc : 0 ≤ c) (he : 0 ≤ e) (hp : 0 ≤ p)
    (I v₀ v : ℝ≥0∞) (hI : I < ⊤) (hv₀ : 0 < v₀) (hv₀fin : v₀ < ⊤)
    (hvolume : v₀ ≤ ENNReal.ofReal p*v)
    (hmean : ENNReal.ofReal u*v ≤ ENNReal.ofReal c*ENNReal.ofReal e*I) :
    u ≤ (c*(I.toReal+1)/v₀.toReal)*e*p := by
  have hJ : 0 ≤ I.toReal+1 := by positivity
  have hIbound : I ≤ ENNReal.ofReal (I.toReal+1) := by
    calc
      _ = ENNReal.ofReal I.toReal := (ENNReal.ofReal_toReal hI.ne).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by linarith)
  have H : ENNReal.ofReal u*v₀ ≤
      ENNReal.ofReal p*(ENNReal.ofReal c*ENNReal.ofReal e*ENNReal.ofReal (I.toReal+1)) := by
    calc
      _ ≤ ENNReal.ofReal u*(ENNReal.ofReal p*v) := mul_le_mul_right hvolume _
      _ = ENNReal.ofReal p*(ENNReal.ofReal u*v) := by ac_rfl
      _ ≤ ENNReal.ofReal p*(ENNReal.ofReal c*ENNReal.ofReal e*I) := mul_le_mul_right hmean _
      _ ≤ _ := by gcongr
  have ht : ENNReal.ofReal p*(ENNReal.ofReal c*ENNReal.ofReal e*ENNReal.ofReal (I.toReal+1)) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top)
  have hreal := ENNReal.toReal_mono ht H
  simp only [ENNReal.toReal_mul,ENNReal.toReal_ofReal hu,ENNReal.toReal_ofReal hc,
    ENNReal.toReal_ofReal he,ENNReal.toReal_ofReal hp,ENNReal.toReal_ofReal hJ] at hreal
  have hvpos : 0 < v₀.toReal := ENNReal.toReal_pos hv₀.ne' hv₀fin.ne
  calc
    _ ≤ (p*(c*e*(I.toReal+1)))/v₀.toReal := (le_div_iff₀ hvpos).mpr hreal
    _ = _ := by ring

end Yau.Proofs.P04Aux
