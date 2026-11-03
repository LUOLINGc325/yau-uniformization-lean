import Yau.Proofs.C04RadialIntegralJetsDerivatives
import Yau.Proofs.C04RadialIntegralJetsLeibniz

/-! All jets of one radial integral, with an order-independent coefficient
for its highest input jet. -/

noncomputable section
open Set MeasureTheory
open scoped ContDiff Topology Interval

namespace Yau.Proofs.C04Aux

universe u
variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

def radialIntegral (f : E → E →L[ℝ] F) (x : E) : F :=
  ∫ t in (0 : ℝ)..1, t • (f (t • x) x)

theorem radialIntegral_integrand_contDiff (f : E → E →L[ℝ] F) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun p : E × ℝ => p.2 • (f (p.2 • p.1) p.1)) := by
  exact contDiff_snd.smul ((hf.comp (contDiff_snd.smul contDiff_fst)).clm_apply contDiff_fst)

theorem radialIntegral_contDiff (f : E → E →L[ℝ] F) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (radialIntegral f) := by
  exact radialIntegral_joint_contDiff _ (radialIntegral_integrand_contDiff f hf)

theorem radialIntegral_iteratedFDeriv_bound (f : E → E →L[ℝ] F) (hf : ContDiff ℝ ∞ f)
    (m : ℕ) {R : ℝ} (hR : 0 ≤ R) (B : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j)
    (hbound : ∀ j, j ≤ m → ∀ x ∈ Metric.closedBall (0 : E) R, ‖iteratedFDeriv ℝ j f x‖ ≤ B j)
    {x : E} (hx : x ∈ Metric.closedBall (0 : E) R) :
    ‖iteratedFDeriv ℝ m (radialIntegral f) x‖ ≤ R * B m + (m : ℝ) * B (m - 1) := by
  let H : E × ℝ → F := fun p => p.2 • (f (p.2 • p.1) p.1)
  have hH : ContDiff ℝ ∞ H := radialIntegral_integrand_contDiff f hf
  change ‖iteratedFDeriv ℝ m (fun y => ∫ t in (0 : ℝ)..1, H (y,t)) x‖ ≤ _
  rw [radialIntegral_iteratedFDeriv H hH m x]
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (C := R * B m + (m : ℝ) * B (m - 1))
    (f := fun t : ℝ => iteratedFDeriv ℝ m (fun y => H (y,t)) x) (fun t ht => by
      have ht' : t ∈ Ioc (0 : ℝ) 1 := by simpa only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
      exact radialIntegral_dilate_jet_bound f hf hR ⟨ht'.1.le, ht'.2⟩ B hB m hbound hx)
  simpa only [sub_zero, abs_one, mul_one] using hh

end Yau.Proofs.C04Aux
