import Yau.Proofs.C03PullbackBounds
import Yau.Proofs.C03FlatComplete
import Yau.Proofs.C07CurveLength

/-! The uniform matrix lower bound gives an actual Euclidean distance fence
and compact sublevels for the extended metric. -/

noncomputable section
open Set
open scoped Manifold Topology ContDiff Matrix ComplexOrder

namespace Yau.Proofs.C03Aux
open Yau Yau.Blueprint Yau.LeafProofs L12Aux L23Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

theorem half_identity_le_scaled_of_lower (H : Herm n) (d : ℝ) (hd : 0 < d)
    (hlo : HermLE ((d : ℂ) • (1 : Herm n)) H) :
    HermLE (((1 / 2 : ℝ) : ℂ) • (1 : Herm n)) (((d⁻¹ : ℝ) : ℂ) • H) := by
  have hdc : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hInv : ((d⁻¹ : ℝ) : ℂ) * (d : ℂ) = 1 := by
    rw [Complex.ofReal_inv, inv_mul_cancel₀ hdc]
  have hs := hlo.smul (Complex.zero_le_real.mpr (inv_nonneg.mpr hd.le))
  have hscale : HermLE (1 : Herm n) (((d⁻¹ : ℝ) : ℂ) • H) := by
    unfold HermLE
    convert hs using 1
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, mul_sub,
      ← mul_assoc, hInv, one_mul]
  have hhalf := scalar_identity_HermLE (n := n) (1 / 2) 1 (by norm_num)
  unfold HermLE at hhalf hscale ⊢
  convert hscale.add hhalf using 1
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Complex.ofReal_one]
  ring

theorem euclidean_le_field_curve_length (hn : 1 ≤ n)
    (k : HermitianField (ComplexEuclideanManifold n hn)) (hk : MetricSmooth k)
    (d : ℝ) (hd : 0 < d)
    (hlo : ∀ z, HermLE ((d : ℂ) • (1 : Herm n)) (gMat k z))
    {x y : ComplexVector n} (γ : IntegrableCurve k x y) :
    dist (x : ComplexVector n) y ≤ Real.sqrt (d⁻¹) * curveLength k γ.1 := by
  have horder (z : (ComplexEuclideanManifold n hn).Carrier) :
      HermLE (gMat (FlatComplete.euclideanHermitianField n hn) z)
        (((d⁻¹ : ℝ) : ℂ) • gMat k z) := by
    rw [FlatComplete.euclidean_gMat]
    exact half_identity_le_scaled_of_lower _ d hd (hlo z)
  obtain ⟨hint, hlength⟩ := C07CurveLengthAux.curve_length_comparison
    (FlatComplete.euclidean_metricSmooth n hn) γ (inv_nonneg.mpr hd.le)
    (fun t _ => horder (γ.1 t))
  let γ₀ : IntegrableCurve (FlatComplete.euclideanHermitianField n hn) x y := ⟨γ.1, hint⟩
  have H := inducedDistance_le_curveLength (FlatComplete.euclideanHermitianField n hn) γ₀
  change lengthDist (FlatComplete.euclideanHermitianField n hn) x y ≤
    curveLength (FlatComplete.euclideanHermitianField n hn) γ.1 at H
  rw [FlatComplete.euclidean_lengthDist] at H
  exact H.trans hlength

theorem euclidean_dist_le_field_distance (hn : 1 ≤ n)
    (k : HermitianField (ComplexEuclideanManifold n hn)) (hk : MetricSmooth k)
    (d : ℝ) (hd : 0 < d)
    (hlo : ∀ z, HermLE ((d : ℂ) • (1 : Herm n)) (gMat k z))
    (x y : ComplexVector n) :
    dist (x : ComplexVector n) y ≤ Real.sqrt (d⁻¹) * inducedDistance k x y := by
  have hC : 0 < Real.sqrt (d⁻¹) := Real.sqrt_pos.mpr (inv_pos.mpr hd)
  obtain ⟨γ₀⟩ := L23Aux.integrable_curve_nonempty k hk x y
  have hne : (Set.range (fun γ : IntegrableCurve k x y => curveLength k γ.1)).Nonempty :=
    ⟨_, Set.mem_range_self γ₀⟩
  have H : dist (x : ComplexVector n) y / Real.sqrt (d⁻¹) ≤ inducedDistance k x y := by
    apply le_csInf hne
    rintro _ ⟨γ, rfl⟩
    exact (div_le_iff₀ hC).mpr (by
      simpa only [mul_comm] using euclidean_le_field_curve_length hn k hk d hd hlo γ)
  simpa only [mul_comm] using (div_le_iff₀ hC).mp H

theorem field_distance_sublevel_isCompact (hn : 1 ≤ n)
    (k : HermitianField (ComplexEuclideanManifold n hn)) (hk : MetricSmooth k)
    (d : ℝ) (hd : 0 < d)
    (hlo : ∀ z, HermLE ((d : ℂ) • (1 : Herm n)) (gMat k z))
    (o : ComplexVector n) (R : ℝ) :
    IsCompact {y : ComplexVector n | inducedDistance k o y ≤ R} := by
  have hc : IsClosed {y : ComplexVector n | inducedDistance k o y ≤ R} :=
    isClosed_le (L23Aux.continuous_distFrom k hk o) continuous_const
  apply (isCompact_closedBall (o : ComplexVector n) (Real.sqrt (d⁻¹) * R)).of_isClosed_subset hc
  intro y hy
  change dist y o ≤ Real.sqrt (d⁻¹) * R
  have H := euclidean_dist_le_field_distance hn k hk d hd hlo o y
  rw [dist_comm] at H
  exact H.trans (mul_le_mul_of_nonneg_left hy (Real.sqrt_nonneg _))

end Yau.Proofs.C03Aux
