import Yau.Proofs.V03Dirichlet
import Mathlib.Analysis.Normed.Lp.lpHolder

/-! A bounded Fourier multiplier recovers the weighted half-order vector
from the angular derivative. Its norm bound is independent of the trace. -/

open scoped Topology lp
open MeasureTheory AddCircle

noncomputable section
namespace Yau.Blueprint.V03Proof

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

def inverseAngularMultiplier (k : ℤ) : ℂ :=
  if k = 0 then 0 else (Real.sqrt |(k : ℝ)| : ℂ) / (Complex.I * (k : ℂ))

theorem inverseAngularMultiplier_norm_le (k : ℤ) : ‖inverseAngularMultiplier k‖ ≤ 1 := by
  by_cases hk : k = 0
  · simp [inverseAngularMultiplier, hk]
  have hn : 1 ≤ k.natAbs := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hk)
  have hnr : (1 : ℝ) ≤ (k.natAbs : ℝ) := by exact_mod_cast hn
  have hr : (1 : ℝ) ≤ |(k : ℝ)| := by
    simpa only [Nat.cast_natAbs, Int.cast_abs] using hnr
  have hs : Real.sqrt |(k : ℝ)| ≤ |(k : ℝ)| := Real.sqrt_le_self_iff.mpr (Or.inr hr)
  have hnorm : ‖(k : ℂ)‖ = |(k : ℝ)| := by
    rw [← Complex.ofReal_intCast]
    simp only [Complex.norm_real, Real.norm_eq_abs]
  rw [inverseAngularMultiplier, if_neg hk, norm_div, norm_mul, Complex.norm_I, one_mul,
    Complex.norm_of_nonneg (Real.sqrt_nonneg _), hnorm]
  exact (div_le_one (by linarith : 0 < |(k : ℝ)|)).mpr hs

def inverseAngularMap : ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ) :=
  lp.mapCLM 2 (fun k : ℤ => inverseAngularMultiplier k • ContinuousLinearMap.id ℂ ℂ)
    zero_le_one (fun k => by simpa only [norm_smul, ContinuousLinearMap.norm_id, mul_one] using inverseAngularMultiplier_norm_le k)

theorem inverseAngularMap_norm_le : ‖inverseAngularMap‖ ≤ 1 :=
  lp.norm_mapCLM_le 2 _ zero_le_one _

def dirichletFromAngular :
    Lp ℂ 2 (haarAddCircle (T := 2 * Real.pi)) →L[ℂ] ℓ²(ℤ, ℂ) :=
  inverseAngularMap.comp (fourierBasis.repr.toContinuousLinearEquiv.toContinuousLinearMap)

theorem dirichletFromAngular_apply (u : Lp ℂ 2 (haarAddCircle (T := 2 * Real.pi))) (k : ℤ) :
    dirichletFromAngular u k = inverseAngularMultiplier k * fourierCoeff u k := by
  change inverseAngularMultiplier k * (fourierBasis.repr u) k = _
  rw [fourierBasis_repr]

theorem dirichletFromAngular_norm_le (u : Lp ℂ 2 (haarAddCircle (T := 2 * Real.pi))) :
    ‖dirichletFromAngular u‖ ≤ ‖u‖ := by
  change ‖inverseAngularMap (fourierBasis.repr u)‖ ≤ ‖u‖
  have hh := inverseAngularMap.le_of_opNorm_le inverseAngularMap_norm_le (fourierBasis.repr u)
  simpa only [one_mul, LinearIsometryEquiv.norm_map] using hh

end Yau.Blueprint.V03Proof
