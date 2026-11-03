import Yau.Blueprint.Nodes

/-! Compactness gives one relative comparison radius for an actual continuous positive quadratic family. -/
noncomputable section
open scoped Topology Matrix ComplexOrder
open Set Filter Metric
namespace Yau.Proofs.C03Aux.EnvelopeSmoothing
open Yau Yau.Blueprint
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

/-- This is only continuity, homogeneity and compactness; no spectral estimate is assumed. -/
theorem exists_uniform_relative_quadratic_radius
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (q : E → E → ℝ) (hq : Continuous (fun p : E × E => q p.1 p.2))
    (K : Set E) (hK : IsCompact K)
    (hpos : ∀ z ∈ K, ∀ v, v ≠ 0 → 0 < q z v)
    (hhom : ∀ z v (r : ℝ), q z (r • v) = r ^ 2 * q z v) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ K, ∀ y, dist y z < δ →
      ∀ v, (1 / 2 : ℝ) * q z v ≤ q y v := by
  let S : Set E := sphere 0 1
  have hS : IsCompact S := isCompact_sphere _ _
  obtain ⟨m, hm, hmlower⟩ := (hK.prod hS).exists_forall_le' hq.continuousOn
    (fun p hp => hpos p.1 hp.1 p.2 (by
      intro hz
      have hh := hp.2
      simp [S, hz] at hh))
  let D : Set E := cthickening 1 K
  have hD : IsCompact D := hK.cthickening
  have huc := (hD.prod hS).uniformContinuousOn_of_continuous hq.continuousOn
  obtain ⟨d, hd, hdist⟩ := Metric.uniformContinuousOn_iff.mp huc (m / 2) (half_pos hm)
  refine ⟨min 1 d, lt_min zero_lt_one hd, ?_⟩
  intro z hz y hy v
  have hzD : z ∈ D := self_subset_cthickening K hz
  have hyD : y ∈ D := closedBall_subset_cthickening hz 1
    ((hy.trans_le (min_le_left _ _)).le)
  have hunit : ∀ w ∈ S, (1 / 2 : ℝ) * q z w ≤ q y w := by
    intro w hw
    have hmz : m ≤ q z w := hmlower (z, w) ⟨hz, hw⟩
    have hpair : dist (y, w) (z, w) < d := by
      simpa only [Prod.dist_eq, dist_self, max_eq_left dist_nonneg] using hy.trans_le (min_le_right _ _)
    have hh := hdist (y, w) ⟨hyD, hw⟩ (z, w) ⟨hzD, hw⟩ hpair
    have habs : |q y w - q z w| < m / 2 := by simpa only [Real.dist_eq] using hh
    have hl := (abs_lt.mp habs).1
    linarith
  by_cases hv : v = 0
  · have hz0 : q z 0 = 0 := by simpa using hhom z 0 0
    have hy0 : q y 0 = 0 := by simpa using hhom y 0 0
    simp [hv, hz0, hy0]
  · have hnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
    let w : E := ‖v‖⁻¹ • v
    have hw : w ∈ S := by
      simp only [S, mem_sphere, dist_zero_right, w, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hnorm), inv_mul_cancel₀ hnorm.ne']
    have hvw : ‖v‖ • w = v := by
      dsimp only [w]
      rw [smul_smul, mul_inv_cancel₀ hnorm.ne', one_smul]
    have hzscale : q z v = ‖v‖ ^ 2 * q z w := by
      calc
        q z v = q z (‖v‖ • w) := congrArg (q z) hvw.symm
        _ = _ := hhom z w ‖v‖
    have hyscale : q y v = ‖v‖ ^ 2 * q y w := by
      calc
        q y v = q y (‖v‖ • w) := congrArg (q y) hvw.symm
        _ = _ := hhom y w ‖v‖
    calc
      (1 / 2 : ℝ) * q z v = ‖v‖ ^ 2 * ((1 / 2 : ℝ) * q z w) := by rw [hzscale]; ring
      _ ≤ ‖v‖ ^ 2 * q y w := mul_le_mul_of_nonneg_left (hunit w hw) (sq_nonneg _)
      _ = q y v := hyscale.symm

def matrixQuadratic {n : ℕ} (H : Herm n) (v : ComplexVector n) : ℝ :=
  (star (WithLp.ofLp v) ⬝ᵥ (H *ᵥ WithLp.ofLp v)).re

theorem matrixQuadratic_continuous {n : ℕ} (H : ComplexVector n → Herm n)
    (hH : ∀ i j, Continuous (fun z => H z i j)) :
    Continuous (fun p : ComplexVector n × ComplexVector n => matrixQuadratic (H p.1) p.2) := by
  have hHC : Continuous H := continuous_pi fun i => continuous_pi fun j => hH i j
  unfold matrixQuadratic dotProduct Matrix.mulVec
  fun_prop

theorem matrixQuadratic_real_smul {n : ℕ} (H : Herm n) (v : ComplexVector n) (r : ℝ) :
    matrixQuadratic H (r • v) = r ^ 2 * matrixQuadratic H v := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  have hstar : star ((r : ℂ) • WithLp.ofLp v) = (r : ℂ) • star (WithLp.ofLp v) := by
    ext i
    simp
  change (star ((r : ℂ) • WithLp.ofLp v) ⬝ᵥ (H *ᵥ ((r : ℂ) • WithLp.ofLp v))).re = _
  rw [hstar, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul]
  simp only [smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  dsimp only [matrixQuadratic]
  ring

theorem matrixQuadratic_sub {n : ℕ} (H A : Herm n) (v : ComplexVector n) :
    matrixQuadratic (H - A) v = matrixQuadratic H v - matrixQuadratic A v := by
  simp only [matrixQuadratic, Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re]

theorem matrixQuadratic_real_matrix_smul {n : ℕ} (r : ℝ) (H : Herm n)
    (v : ComplexVector n) :
    matrixQuadratic ((r : ℂ) • H) v = r * matrixQuadratic H v := by
  simp only [matrixQuadratic, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

theorem exists_uniform_relative_matrix_radius {n : ℕ}
    (H : ComplexVector n → Herm n) (hHc : ∀ i j, Continuous (fun z => H z i j))
    (hHp : ∀ z, (H z).PosDef) (K : Set (ComplexVector n)) (hK : IsCompact K) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ K, ∀ y, dist y z < δ → ∀ v,
      (1 / 2 : ℝ) * matrixQuadratic (H z) v ≤ matrixQuadratic (H y) v := by
  apply exists_uniform_relative_quadratic_radius (fun z v => matrixQuadratic (H z) v)
    (matrixQuadratic_continuous H hHc) K hK
  · intro z _ v hv
    have hne : WithLp.ofLp v ≠ 0 := by
      intro hz
      apply hv
      apply WithLp.ofLp_injective 2
      simpa using hz
    exact (Complex.pos_iff.mp ((hHp z).dotProduct_mulVec_pos hne)).1
  · exact fun z v r => matrixQuadratic_real_smul (H z) v r

end Yau.Proofs.C03Aux.EnvelopeSmoothing
