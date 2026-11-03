import Yau.Proofs.C07RadialCurve
import Yau.Proofs.C07CurveLength
import Yau.Proofs.C07TinyImageScalar

open scoped Manifold Topology ContDiff Matrix ComplexOrder unitInterval

noncomputable section

namespace Yau.Proofs.C07TinyImageAux

open Yau Yau.Blueprint Set
open C07RadialCurveAux C07CurveLengthAux
open Yau.LeafProofs.L12Aux

variable {n : ℕ} {M : ComplexManifold n}

theorem reverse_exp_metric_order (s : ℝ) {G H : Herm n}
    (h : HermLE ((Real.exp (-2 * s) : ℂ) • G) H) :
    HermLE G ((Real.exp (2 * s) : ℂ) • H) := by
  change (H - (Real.exp (-2 * s) : ℂ) • G).PosSemidef at h
  have hscale := h.smul (a := (Real.exp (2 * s) : ℂ))
    (Complex.nonneg_iff.mpr ⟨(Real.exp_pos _).le, by simp only [Complex.ofReal_im]⟩)
  have hcancel : (Real.exp (2 * s) : ℂ) * (Real.exp (-2 * s) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    have he : 2 * s + -2 * s = 0 := by ring
    rw [he, Real.exp_zero]
    rfl
  change ((Real.exp (2 * s) : ℂ) • H - G).PosSemidef
  simpa only [smul_sub, smul_smul, hcancel, one_smul] using hscale

/-- A small chart radial segment cannot leave the fixed initial-distance
neighborhood on which the reverse metric comparison is available. -/
theorem image_mem_of_metric_lower (g : SmoothMetric M) {k : HermitianField M}
    (hk : MetricSmooth k) {o : M.Carrier} {Φ : ComplexVector n → M.Carrier}
    {r c C q s : ℝ} (hC : 0 < C) (hΦ : UnitaryChart k o Φ r c C)
    (hq : 0 < q) (K : Set M.Carrier)
    (hnear : ∀ x, inducedDistance g.form o x ≤ q → x ∈ K)
    (hlower : ∀ x ∈ K, HermLE ((Real.exp (-2 * s) : ℂ) • gMat g.form x) (gMat k x))
    {z : ComplexVector n} (hz : ‖z‖ < r)
    (hshort : Real.exp s * (Real.sqrt (2 * C) * ‖z‖) < q) : Φ z ∈ K := by
  let D : I → ℝ := fun a => inducedDistance g.form o (Φ ((a : ℝ) • z))
  have hrad : Continuous (fun a : I => Φ ((a : ℝ) • z)) :=
    hΦ.1.1.continuousOn.comp_continuous (continuous_subtype_val.smul continuous_const)
      (fun a => radial_point_mem hz a.2)
  have hD : Continuous D := (continuous_inducedDistance g).comp
    (continuous_const.prodMk hrad)
  have hD0 : D 0 = 0 := by
    change inducedDistance g.form o (Φ ((0 : ℝ) • z)) = 0
    rw [zero_smul, hΦ.2.1]
    exact g.induced_distance_eq_zero.mpr rfl
  have hbound : ∀ τ : I, (∀ a : I, a ≤ τ → D a ≤ q) → D τ < q := by
    intro τ hprefix
    let w := (τ : ℝ) • z
    have hnorm : ‖w‖ ≤ ‖z‖ := by
      dsimp only [w]
      rw [norm_smul, Real.norm_of_nonneg τ.2.1]
      exact mul_le_of_le_one_left (norm_nonneg z) τ.2.2
    have hw : ‖w‖ < r := hnorm.trans_lt hz
    have hrefl : ∀ y, HermLE (gMat k y) (gMat k y) := by
      intro y
      change (gMat k y - gMat k y).PosSemidef
      rw [sub_self]
      exact Matrix.PosSemidef.zero
    obtain ⟨γ, hγ, hγlength⟩ := exists_radial_curve hk hrefl hC hΦ hw
    have htrace : ∀ u ∈ Icc (0 : ℝ) 1, γ.1 u ∈ K := by
      intro u hu
      have hprod : u * (τ : ℝ) ≤ τ := mul_le_of_le_one_left τ.2.1 hu.2
      let a : I := ⟨u * (τ : ℝ), ⟨mul_nonneg hu.1 τ.2.1, hprod.trans τ.2.2⟩⟩
      have haτ : a ≤ τ := hprod
      have heq : γ.1 u = Φ ((a : ℝ) • z) := by
        rw [hγ u hu]
        change Φ ((u : ℝ) • ((τ : ℝ) • z)) = Φ ((u * (τ : ℝ)) • z)
        rw [smul_smul]
      apply hnear
      rw [heq]
      exact hprefix a haτ
    obtain ⟨hint, hlength⟩ := curve_length_comparison (metricSmooth_of_smoothMetric g)
      γ (Real.exp_pos (2 * s)).le
      (fun u hu => reverse_exp_metric_order s (hlower _ (htrace u hu)))
    have hdist : D τ ≤ curveLength g.form γ.1 :=
      inducedDistance_le_curveLength g.form ⟨γ.1, hint⟩
    have hroot : Real.sqrt (Real.exp (2 * s)) = Real.exp s := by
      rw [← Real.exp_half]
      congr 1
      ring
    calc
      D τ ≤ curveLength g.form γ.1 := hdist
      _ ≤ Real.sqrt (Real.exp (2 * s)) * curveLength k γ.1 := hlength
      _ = Real.exp s * curveLength k γ.1 := by rw [hroot]
      _ ≤ Real.exp s * (Real.sqrt (2 * C) * ‖w‖) :=
        mul_le_mul_of_nonneg_left hγlength (Real.exp_pos _).le
      _ ≤ Real.exp s * (Real.sqrt (2 * C) * ‖z‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hnorm (Real.sqrt_nonneg _)) (Real.exp_pos _).le
      _ < q := hshort
  have hend : inducedDistance g.form o (Φ z) < q := by
    have h := below_of_prefix_bound hD hD0 hq hbound (1 : I)
    change inducedDistance g.form o (Φ ((1 : ℝ) • z)) < q at h
    simpa only [one_smul] using h
  exact hnear _ hend.le

end Yau.Proofs.C07TinyImageAux
