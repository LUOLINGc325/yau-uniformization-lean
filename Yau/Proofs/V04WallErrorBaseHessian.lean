import Yau.Proofs.V04WallErrorScalarBounds
import Yau.Proofs.P07DistanceLeviRankOne
import Yau.Proofs.V03LeviMatrix
import Yau.Proofs.V03DiscScalars

/-! The exhaustion controls the actual reciprocal base-wall Levi form
relative to the initial metric, with one constant for every wall index. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
noncomputable section
namespace Yau.Blueprint.V04Proof.WallErrorAux
open Yau Yau.Blueprint V03Proof Yau.NodeProofs.P07DistanceLevi

variable {n q : ℕ} {X : KahlerManifold n}

theorem leviDirection_real_smul (A : Matrix (Fin n) (Fin n) ℂ) (c : ℝ)
    (v : ComplexVector n) : leviDirection ((c : ℂ) • A) v = c * leviDirection A v := by
  simp [leviDirection, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.mul_re]

theorem leviDirection_sub (A B : Matrix (Fin n) (Fin n) ℂ) (v : ComplexVector n) :
    leviDirection (A - B) v = leviDirection A v - leviDirection B v := by
  simp only [leviDirection, Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re]

theorem direction_le_of_hermLE {A B : Matrix (Fin n) (Fin n) ℂ}
    (hAB : HermLE A B) (v : ComplexVector n) : leviDirection A v ≤ leviDirection B v := by
  have h := hAB.re_dotProduct_nonneg (WithLp.ofLp v)
  change 0 ≤ leviDirection (B - A) v at h
  rw [leviDirection_sub] at h
  linarith

theorem hermLE_of_direction_le {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hAB : ∀ v : ComplexVector n, leviDirection A v ≤ leviDirection B v) : HermLE A B := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hB.sub hA)
  intro v
  apply Complex.nonneg_iff.mpr
  constructor
  · have h := hAB (WithLp.toLp 2 v)
    change leviDirection A (WithLp.toLp 2 v) ≤ leviDirection B (WithLp.toLp 2 v) at h
    simpa only [leviDirection, Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re] using sub_nonneg.mpr h
  · exact ((hB.sub hA).im_star_dotProduct_mulVec_self v).symm

theorem baseWall_direction_abs_bound
    {d : VariationData X q} (hd : VariationSetup d)
    {C M : ℝ} (hC : 0 < C)
    (hEx : ∀ x, C⁻¹ * (1 + distFrom X.metric.form d.o x) ≤ d.u x ∧
      d.u x ≤ C * (1 + distFrom X.metric.form d.o x) ∧
      gradNormSq X.metric.form d.u x ≤ C ^ 2 ∧
      HermLE ((-(C / d.u x) : ℂ) • gMat X.metric.form x) (levi d.u x) ∧
      HermLE (levi d.u x) (((C / d.u x : ℝ) : ℂ) • gMat X.metric.form x))
    (hM : 1 ≤ M)
    (hDer : ∀ r ∈ Set.Icc (0 : ℝ) 1,
      |deriv d.profileBase r| ≤ M ∧ |deriv (deriv d.profileBase) r| ≤ M)
    (j : ℕ) (x : Pt X) (hx : d.u x < d.A j) (v : ComplexVector n) :
    |leviDirection (levi (wallBase d j) x) v| ≤
      (M * C + (2 * M ^ 2 + M) * (2 * C ^ 2)) *
        (deltaBase d j x ^ 3)⁻¹ * leviDirection (gMat X.metric.form x) v := by
  have hux : 1 ≤ d.u x := hd.2.2.2.1.2.2.1 x
  have hA : 1 ≤ d.A j := hux.trans hx.le
  have hA0 : 0 < d.A j := zero_lt_one.trans_le hA
  have hr : d.u x / d.A j ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (zero_le_one.trans hux) hA0.le, (div_le_one hA0).2 hx.le⟩
  have hProfile := (setup_wallProfiles hd).2.2.1 (d.u x / d.A j)
  have hδ : 0 < d.profileBase (d.u x / d.A j) :=
    hProfile.2.2.1.mpr ((div_lt_one hA0).2 hx)
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hw0 : 0 ≤ (deltaBase d j x ^ 3)⁻¹ := by unfold deltaBase; positivity
  have hD := wallScalar_derivative_bounds (setup_wallProfiles hd).1 hM hA hδ hProfile.2.1
    (hDer _ hr).1 (hDer _ hr).2
  have hG := gMat_posDef X.metric.form x
  have hGv : 0 ≤ leviDirection (gMat X.metric.form x) v := hG.posSemidef.re_dotProduct_nonneg _
  have hcu : C / d.u x ≤ C :=
    (div_le_iff₀ (zero_lt_one.trans_le hux)).2 (le_mul_of_one_le_right hC.le hux)
  have hlo := direction_le_of_hermLE (hEx x).2.2.2.1 v
  have hhi := direction_le_of_hermLE (hEx x).2.2.2.2 v
  simp only [← Complex.ofReal_div, ← Complex.ofReal_neg, leviDirection_real_smul] at hlo hhi
  have hLu : |leviDirection (levi d.u x) v| ≤ C * leviDirection (gMat X.metric.form x) v := by
    apply abs_le.mpr
    constructor
    · nlinarith [mul_le_mul_of_nonneg_right hcu hGv]
    · exact hhi.trans (mul_le_mul_of_nonneg_right hcu hGv)
  have hRank0 := directionalRankOne_nonneg (inChart x d.u) (chartPt x x) v
  have hRank := directionalRankOne_inChart_le X.metric.form hd.2.2.2.1.1 x v
  have hRank' : directionalRankOne (inChart x d.u) (chartPt x x) v ≤
      2 * C ^ 2 * leviDirection (gMat X.metric.form x) v := by
    exact hRank.trans (mul_le_mul_of_nonneg_right (by nlinarith [(hEx x).2.2.1]) hGv)
  have hround : chartInv x (chartPt x x) = x :=
    (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  have hu : ContDiffAt ℝ 2 (inChart x d.u) (chartPt x x) :=
    ((hd.2.2.2.1.1 x).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds
        (mem_extChartAt_target x))).of_le (by simp)
  have hval : inChart x d.u (chartPt x x) = d.u x := congrArg d.u hround
  have hF : ContDiffAt ℝ 2 (wallScalar d.profileBase (d.A j)) (d.u x) :=
    (((setup_wallProfiles hd).1.comp (contDiff_id.div_const (d.A j))).contDiffAt.of_le
      (by simp)).inv hδ.ne' |>.sub contDiffAt_const
  have hF' : ContDiffAt ℝ 2 (wallScalar d.profileBase (d.A j))
      (inChart x d.u (chartPt x x)) := by rw [hval]; exact hF
  have hchain := leviDirection_scalar_comp hu hF' v
  rw [hval] at hchain
  change leviDirection (levi (wallBase d j) x) v =
    deriv (wallScalar d.profileBase (d.A j)) (d.u x) * leviDirection (levi d.u x) v +
      deriv (deriv (wallScalar d.profileBase (d.A j))) (d.u x) *
        directionalRankOne (inChart x d.u) (chartPt x x) v at hchain
  rw [hchain]
  calc
    |deriv (wallScalar d.profileBase (d.A j)) (d.u x) * leviDirection (levi d.u x) v +
        deriv (deriv (wallScalar d.profileBase (d.A j))) (d.u x) *
          directionalRankOne (inChart x d.u) (chartPt x x) v| ≤
        |deriv (wallScalar d.profileBase (d.A j)) (d.u x)| * |leviDirection (levi d.u x) v| +
          |deriv (deriv (wallScalar d.profileBase (d.A j))) (d.u x)| *
            directionalRankOne (inChart x d.u) (chartPt x x) v := by
      simpa only [abs_mul, abs_of_nonneg hRank0] using abs_add_le
        (deriv (wallScalar d.profileBase (d.A j)) (d.u x) * leviDirection (levi d.u x) v)
        (deriv (deriv (wallScalar d.profileBase (d.A j))) (d.u x) *
          directionalRankOne (inChart x d.u) (chartPt x x) v)
    _ ≤ (M * (deltaBase d j x ^ 3)⁻¹) * (C * leviDirection (gMat X.metric.form x) v) +
        ((2 * M ^ 2 + M) * (deltaBase d j x ^ 3)⁻¹) *
          (2 * C ^ 2 * leviDirection (gMat X.metric.form x) v) := by
      apply add_le_add
      · exact mul_le_mul hD.1 hLu (abs_nonneg _) (mul_nonneg hM0 hw0)
      · exact mul_le_mul hD.2 hRank' hRank0 (mul_nonneg (by nlinarith [sq_nonneg M]) hw0)
    _ = _ := by ring

end Yau.Blueprint.V04Proof.WallErrorAux
