import Yau.Proofs.C04RescaledTubeScaling
import Yau.Proofs.C04RescaledTubePathLength

/-! The original integrated Harnack inequality on the actual rescaled flow. -/
noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory Filter
namespace Yau.Proofs.C04RescaledTubeAux
open Yau Blueprint LeafProofs C04Aux
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {M : ComplexManifold n}

theorem HermLE_scale (c : ℝ) (hc : 0 ≤ c) {A B : Herm n} (hAB : HermLE A B) :
    HermLE ((c : ℂ) • A) ((c : ℂ) • B) := by
  change (((c : ℂ) • B) - ((c : ℂ) • A)).PosSemidef
  rw [← smul_sub]
  exact hAB.smul (Complex.nonneg_iff.2 ⟨hc, by simp⟩)

theorem rescaled_integrated_harnack (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ)
    (H : ℝ) (hHar : ∀ x y t t', 0 < t → t < t' →
      scalarCurvature (h t) x ≤ scalarCurvature (h t') y * (t' / t) *
        Real.exp (H * distFrom (h t) x y ^ 2 / (t' - t)))
    (ti R : ℝ) (hR : 0 < R) (x y : Pt X) {z w : ℝ}
    (ht : 0 < ti + z / R) (hzw : z < w) :
    scalarCurvature (scaleField R hR (h (ti + z / R))) x ≤
      scalarCurvature (scaleField R hR (h (ti + w / R))) y *
        ((ti * R + w) / (ti * R + z)) *
        Real.exp (H * distFrom (scaleField R hR (h (ti + z / R))) x y ^ 2 / (w - z)) := by
  have htime : ti + z / R < ti + w / R := by
    linarith [(div_lt_div_iff_of_pos_right hR).2 hzw]
  have hden : ti * R + z ≠ 0 := by
    have hh := mul_pos ht hR
    have he : (ti + z / R) * R = ti * R + z := by field_simp
    rw [he] at hh
    exact hh.ne'
  have hratio : (ti + w / R) / (ti + z / R) = (ti * R + w) / (ti * R + z) := by
    field_simp
    <;> ring
  have hdist := distance_scale R hR (h (ti + z / R))
    (localizedFlow_metricSmooth X o h U P ρ hf ht.le) x y
  change distFrom (scaleField R hR (h (ti + z / R))) x y =
    Real.sqrt R * distFrom (h (ti + z / R)) x y at hdist
  have hexponent : H * distFrom (h (ti + z / R)) x y ^ 2 /
      ((ti + w / R) - (ti + z / R)) =
      H * distFrom (scaleField R hR (h (ti + z / R))) x y ^ 2 / (w - z) := by
    have hdiff : (ti + w / R) - (ti + z / R) = (w - z) / R := by ring
    rw [hdiff, hdist, mul_pow, Real.sq_sqrt hR.le]
    field_simp [hR.ne', (sub_pos.2 hzw).ne']
    <;> ring
  have hh := mul_le_mul_of_nonneg_left (hHar x y _ _ ht htime) (inv_nonneg.2 hR.le)
  rw [scalar_scaleField, scalar_scaleField]
  calc
    _ ≤ R⁻¹ * (scalarCurvature (h (ti + w / R)) y *
      ((ti + w / R) / (ti + z / R)) *
      Real.exp (H * distFrom (h (ti + z / R)) x y ^ 2 /
        ((ti + w / R) - (ti + z / R)))) := hh
    _ = _ := by rw [hratio, hexponent]; ring

theorem rescaled_distance_monotone (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ)
    (hH : HarnackCompleteness X o h) (ti R : ℝ) (hR : 0 < R)
    {z w : ℝ} (ht : 0 ≤ ti + z / R) (hzw : z ≤ w) (x y : Pt X) :
    distFrom (scaleField R hR (h (ti + w / R))) x y ≤
      distFrom (scaleField R hR (h (ti + z / R))) x y := by
  have htime : ti + z / R ≤ ti + w / R := by
    linarith [div_le_div_of_nonneg_right hzw hR.le]
  have hcomp (p : Pt X) := HermLE_scale R hR.le (hH.2.2.2.2.2.1 p _ _ ht htime)
  have hs := distance_le_of_HermLE
    (scaleField R hR (h (ti + w / R))) (scaleField R hR (h (ti + z / R)))
    (metricSmooth_scale R hR _ (localizedFlow_metricSmooth X o h U P ρ hf (ht.trans htime)))
    (metricSmooth_scale R hR _ (localizedFlow_metricSmooth X o h U P ρ hf ht))
    (c := 1) zero_lt_one (by simpa only [Complex.ofReal_one, one_smul, gMat_scaleField] using hcomp) x y
  simpa only [Real.sqrt_one, one_mul, distFrom, lengthDist] using hs

end Yau.Proofs.C04RescaledTubeAux
