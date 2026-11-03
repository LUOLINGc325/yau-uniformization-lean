import Yau.Proofs.C01ClockSpatialJets
import Yau.Proofs.C01ClockCrossJets

/-! The original scalar differential Harnack inequality, obtained from
the three computed blocks of the same negative log determinant clock. -/

noncomputable section

open scoped Manifold Topology ContDiff Matrix ComplexOrder

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint
open Yau.Blueprint.Alignment.Y03Proof

theorem wirt_stdVec_sum {n : ℕ} (f : ComplexVector n → ℂ)
    (z v : ComplexVector n) :
    wirt f z v = ∑ i, v i * wirt f z (stdVec i) := by
  have hsum : (∑ i, v i • stdVec i) = v := by
    ext i
    simp [stdVec, EuclideanSpace.single, Pi.single_apply]
  calc
    _ = wirt f z (∑ i, v i • stdVec i) := congrArg (wirt f z) hsum.symm
    _ = ∑ i, wirt f z (v i • stdVec i) := wirt_sum_dir Finset.univ f z _
    _ = _ := Finset.sum_congr rfl fun i _ => wirt_complex_smul_dir f z (stdVec i) (v i)

variable {n : ℕ} {X : KahlerManifold n} {o : Pt X}
  {h : Flow X} {U P ρ : STF X}

theorem localizedFlow_scalar_harnack
    (hflow : LocalizedFlow X o h U P ρ) (hjoint : JointPositivity X h)
    (x : Pt X) {t : ℝ} (ht : 0 < t) (V : ComplexVector n) :
    0 ≤ deriv (fun s => scalarCurvature (h s) x) t + t⁻¹ * scalarCurvature (h t) x +
      2 * (∑ i, V i * wirt (fun z => Complex.ofReal (inChart x (scalarCurvature (h t)) z))
        (chartPt x x) (stdVec i)).re +
      (star (WithLp.ofLp V) ⬝ᵥ (ricci (h t) x *ᵥ WithLp.ofLp V)).re := by
  let z := chartPt x x
  let w : ℂ := ((Real.log t / 2 : ℝ) : ℂ)
  let f := negativeLogDetClock h x
  let a : ComplexVector n × ℂ := (V, 0)
  let b : ComplexVector n × ℂ := (0, 1)
  let r := t⁻¹
  let G : ComplexVector n → ℂ :=
    fun u => Complex.ofReal (inChart x (scalarCurvature (h t)) u)
  have hz : z ∈ chartTarget x := mem_extChartAt_target (I := ComplexModel n) x
  have hpoint : chartInv x z = x :=
    (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  have htime : Real.exp (2 * w.re) = t := by
    have he : 2 * w.re = Real.log t := by
      simp only [w, Complex.ofReal_re]
      ring
    rw [he, Real.exp_log ht]
  have hf : ContDiffAt ℝ 2 f (z, w) :=
    (negativeLogDetClock_contDiffAt hflow x (z, w) hz).of_le (by simp)
  have hdir : a + r • b = (V, (r : ℂ)) := by
    simp [a, b, Complex.real_smul]
  have hpos := localizedFlow_negativeLogDetClock_levi_nonneg hflow hjoint x z V hz w (r : ℂ)
  rw [← hdir] at hpos
  rw [mixedLevi_two_real_directions hf a b r] at hpos
  have hspace : (wirt (fun p => wirtBar (fun q => (f q : ℂ)) p a) (z, w) a).re =
      (star (WithLp.ofLp V) ⬝ᵥ (ricci (h t) x *ᵥ WithLp.ofLp V)).re := by
    simpa only [f, a, z, htime] using
      congrArg Complex.re (negativeLogDetClock_mixed_spatial hflow x V w)
  have hcross : (wirt (fun p => wirtBar (fun q => (f q : ℂ)) p b) (z, w) a).re =
      t * (wirt G z V).re := by
    simpa only [f, a, b, G, inChart, htime, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using
      congrArg Complex.re (negativeLogDetClock_mixed_cross hflow x z V hz w)
  have hclock : (wirt (fun p => wirtBar (fun q => (f q : ℂ)) p b) (z, w) b).re =
      t * scalarCurvature (h t) x + t ^ 2 * deriv (fun s => scalarCurvature (h s) x) t := by
    simpa only [f, b, htime, hpoint, pow_two, Complex.add_re, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero,
      sub_zero, add_zero] using
      congrArg Complex.re (negativeLogDetClock_mixed_time hflow x z hz w)
  rw [hspace, hcross, hclock] at hpos
  have halgebra (c g R Rₜ : ℝ) :
      c + 2 * t⁻¹ * (t * g) + (t⁻¹) ^ 2 * (t * R + t ^ 2 * Rₜ) =
        Rₜ + t⁻¹ * R + 2 * g + c := by
    field_simp [ht.ne']
    <;> ring
  change 0 ≤ _ + 2 * t⁻¹ * (t * (wirt G z V).re) +
    (t⁻¹) ^ 2 * (t * scalarCurvature (h t) x +
      t ^ 2 * deriv (fun s => scalarCurvature (h s) x) t) at hpos
  rw [halgebra, wirt_stdVec_sum] at hpos
  exact hpos

end Yau.NodeProofs.C01Aux
