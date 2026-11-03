import Yau.Proofs.P04NormLeviPositivity
import Yau.Proofs.P04HolomorphicNormSmooth

noncomputable section
open Set Filter
open scoped Topology Manifold ContDiff Matrix ComplexOrder MatrixOrder

namespace Yau.Proofs.P04Aux
open Yau Yau.LeafProofs
variable {n : ℕ} {M : ComplexManifold n}

/-- At a positive norm the actual logarithmic Levi is exactly the original
Ricci matrix, with its original sign and normalization. -/
theorem canonical_log_norm_levi (g : SmoothMetric M) (S : CanonicalSection M)
    (hS : IsHolomorphicCanonical S) (x : M.Carrier) (hpos : 0 < canonicalNormSq g.form S x) :
    levi (fun y => Real.log (canonicalNormSq g.form S y)) x=ricci g.form x := by
  let z₀ := chartPt x x
  have hz : z₀ ∈ chartTarget x := mem_extChartAt_target x
  have hi : chartInv x z₀=x := (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  have hne : canonicalCoeff S x z₀ ≠ 0 := by
    intro hzero
    have H : canonicalNormSq g.form S x=0 := by
      change ‖canonicalCoeff S x z₀‖^2/(gMat g.form x).det.re=0
      rw [hzero,norm_zero,zero_pow (by norm_num : 2 ≠ 0),zero_div]
    linarith
  have hfAll := L17Holomorphic.contDiffOn_of_complexDiff (isOpen_extChartAt_target x) (hS x)
  have hf : ContDiffAt ℂ 2 (canonicalCoeff S x) z₀ :=
    (hfAll.contDiffAt ((isOpen_extChartAt_target x).mem_nhds hz)).of_le (by simp)
  have hfr : ContDiffAt ℝ 2 (canonicalCoeff S x) z₀ := hf.restrict_scalars ℝ
  have hlogf : ContDiffAt ℝ 2 (fun z => Real.log (‖canonicalCoeff S x z‖^2)) z₀ :=
    (ContDiffAt.norm_sq (𝕜 := ℝ) hfr).log (pow_ne_zero 2 (norm_ne_zero_iff.mpr hne))
  have hD : ContDiffAt ℝ 2 (logDet g.form x) z₀ :=
    ((L18Aux.logDet_contDiffOn g x).contDiffAt ((isOpen_extChartAt_target x).mem_nhds hz)).of_le (by simp)
  have hnear : ∀ᶠ z in 𝓝 z₀, canonicalCoeff S x z ≠ 0 :=
    hf.continuousAt.eventually ((isOpen_ne_fun continuous_id continuous_const).mem_nhds hne)
  have heq : inChart x (fun y => Real.log (canonicalNormSq g.form S y)) =ᶠ[𝓝 z₀]
      (fun z => Real.log (‖canonicalCoeff S x z‖^2)+(-1)*logDet g.form x z) := by
    filter_upwards [hnear,(isOpen_extChartAt_target x).mem_nhds hz] with z hnz hzt
    change Real.log (inChart x (canonicalNormSq g.form S) z)=_
    rw [canonicalNormSq_inChart g.form S x hzt,
      Real.log_div (pow_ne_zero 2 (norm_ne_zero_iff.mpr hnz)) (L18Aux.hMat_det_re_pos g.form x hzt).ne']
    simp only [logDet,neg_mul,one_mul,sub_eq_add_neg]
  change leviC (inChart x (fun y => Real.log (canonicalNormSq g.form S y))) z₀=_
  have hhololog : leviC (fun z => Real.log (‖canonicalCoeff S x z‖^2)) z₀=0 := by
    simpa only [Complex.normSq_eq_norm_sq] using L17Aux.leviC_log_normSq_holomorphic hf hne
  rw [L22Aux.leviC_congr_of_eventuallyEq heq,
    L17Aux.leviC_add hlogf (contDiffAt_const.mul hD),L17Aux.leviC_const_mul hD (-1),
    hhololog,zero_add]
  simp only [ricci,Complex.ofReal_neg,Complex.ofReal_one,neg_smul,one_smul]
  rfl

/-- The actual norm is Levi semipositive also at its zeros. At a zero it
is a smooth local minimum; logarithms are used only in the positive case. -/
theorem canonicalNormSq_levi_posSemidef (g : SmoothMetric M)
    (hRic : ∀ x, (ricci g.form x).PosSemidef) (S : CanonicalSection M)
    (hS : IsHolomorphicCanonical S) (x : M.Carrier) :
    (levi (canonicalNormSq g.form S) x).PosSemidef := by
  let f := inChart x (canonicalNormSq g.form S)
  let z₀ := chartPt x x
  have hz : z₀ ∈ chartTarget x := mem_extChartAt_target x
  have hi : chartInv x z₀=x := (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  have hf : ContDiffAt ℝ 2 f z₀ :=
    (((canonicalNormSq_smooth g S hS) x).contDiffAt
      ((isOpen_extChartAt_target x).mem_nhds hz)).of_le (by simp)
  have hcenter : f z₀=canonicalNormSq g.form S x := congrArg (canonicalNormSq g.form S) hi
  by_cases hzero : canonicalNormSq g.form S x=0
  · apply leviC_posSemidef_of_localMin hf
    change ∀ᶠ z in 𝓝 z₀, f z₀ ≤ f z
    rw [hcenter,hzero]
    exact Eventually.of_forall (fun z => canonicalNormSq_nonneg g.form S (chartInv x z))
  · have hpos : 0 < canonicalNormSq g.form S x :=
      lt_of_le_of_ne (canonicalNormSq_nonneg g.form S x) (Ne.symm hzero)
    apply leviC_posSemidef_of_log hf (hcenter ▸ hpos)
    change (levi (fun y => Real.log (canonicalNormSq g.form S y)) x).PosSemidef
    rw [canonical_log_norm_levi g S hS x hpos]
    exact hRic x

theorem traceWith_nonneg (H A : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.PosSemidef) (hA : A.PosSemidef) : 0 ≤ traceWith H A := by
  let T := CFC.sqrt H⁻¹
  have hT : T.IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg H⁻¹)).isHermitian
  have hTT : T*T=H⁻¹ := CFC.sqrt_mul_sqrt_self H⁻¹ hH.inv.nonneg
  have hp : (T*A*T).PosSemidef := by simpa only [hT.eq] using hA.conjTranspose_mul_mul_same T
  have heq : Matrix.trace (T*A*T)=Matrix.trace (H⁻¹*A) := by rw [Matrix.trace_mul_cycle,hTT]
  exact (Complex.nonneg_iff.mp (heq ▸ hp.trace_nonneg)).1

theorem canonicalNormSq_subharmonic (g : SmoothMetric M)
    (hRic : ∀ x, (ricci g.form x).PosSemidef) (S : CanonicalSection M)
    (hS : IsHolomorphicCanonical S) :
    SmoothFn (canonicalNormSq g.form S) ∧
      ∀ x, 0 ≤ canonicalNormSq g.form S x ∧ 0 ≤ laplacian g.form (canonicalNormSq g.form S) x := by
  refine ⟨canonicalNormSq_smooth g S hS,fun x => ⟨canonicalNormSq_nonneg g.form S x,?_⟩⟩
  exact traceWith_nonneg _ _ (gMat_posDef g.form x).posSemidef
    (canonicalNormSq_levi_posSemidef g hRic S hS x)

end Yau.Proofs.P04Aux
