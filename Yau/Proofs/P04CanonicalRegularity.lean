import Yau.Proofs.P04CanonicalNorm

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder InnerProductSpace ENNReal
open Bundle Module MeasureTheory

namespace Yau.Proofs.P04Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

theorem holomorphicTop_iff (u : BundleDbar.NQForm (CanonicalCoefficients M) 0) :
    BundleDbar.HolomorphicTopForm (r := 1) (CanonicalCoefficients M) u ↔
      IsHolomorphicCanonical (topToCanonical u) := by
  constructor
  · intro H a
    have HH := H a 0
    rw [coefficient_localDomain] at HH
    simpa only [← coefficient_topToCanonical] using HH
  · intro H a α
    have hα : α=(0 : Fin 1) := Subsingleton.elim _ _
    subst α
    rw [coefficient_localDomain]
    simpa only [← coefficient_topToCanonical] using H a

theorem canonicalToTop_zero_at (S : CanonicalSection M) (x : M.Carrier) :
    canonicalToTop S x = (0 : BundleDbar.NQForm (CanonicalCoefficients M) 0) x ↔ S x=0 := by
  constructor
  · intro H
    ext v
    have HH := congrArg (fun A => ((A : BundleDbar.MixedTensor (CanonicalCoefficients M) x 0)
      Fin.elim0 v) 0) (congrArg Subtype.val H)
    change scalarToCoefficient ((S x) v) 0 = (0 : ComplexVector 1) 0 at HH
    rw [scalarToCoefficient_apply] at HH
    change (S x) v = 0 at HH
    change (S x) v = 0
    exact HH
  · intro H
    apply Subtype.ext
    apply AlternatingMap.ext
    intro w
    have hw : w=Fin.elim0 := Subsingleton.elim _ _
    rw [hw]
    apply AlternatingMap.ext
    intro v
    ext i
    simp [canonicalToTop,H,scalarToCoefficient,Yau.LeafProofs.L14Aux.nqForm_zero_apply]

theorem canonicalNormSq_eq_zero_iff (g : HermitianField M) (S : CanonicalSection M) (x : M.Carrier) :
    canonicalNormSq g S x=0 ↔ S x=0 := by
  rw [← formNormSq_canonicalToTop,
    Yau.LeafProofs.L14Aux.formNormSq_top_eq_zero_iff,canonicalToTop_zero_at]

theorem weightedNormSq_canonicalToTop (g : HermitianField M) (S : CanonicalSection M)
    (μ : Measure M.Carrier) (φ : M.Carrier → ℝ) :
    BundleDbar.weightedNormSq (r := 1) (CanonicalCoefficients M) g flatMetric μ φ (canonicalToTop S) =
      ∫⁻ x, ENNReal.ofReal (canonicalNormSq g S x*Real.exp (-φ x)) ∂μ := by
  simp only [BundleDbar.weightedNormSq,formNormSq_canonicalToTop]

/-- The CR construction produces these actual smooth chart coefficients;
the norm remains smooth at the zeros of its holomorphic section. -/
theorem canonicalNormSq_smooth_of_smoothForm (g : SmoothMetric M) (S : CanonicalSection M)
    (hS : BundleDbar.SmoothForm (r := 1) (CanonicalCoefficients M) (canonicalToTop S)) :
    SmoothFn (canonicalNormSq g.form S) := by
  intro a
  have hc := hS a Fin.elim0 0
  rw [coefficient_localDomain] at hc
  simp_rw [coefficient_canonicalToTop] at hc
  have hd : ContDiffOn ℝ ∞ (fun z => (hMat g.form a z).det.re) (chartTarget a) :=
    Complex.reCLM.contDiff.comp_contDiffOn
      (Yau.LeafProofs.L18Aux.contDiffOn_matrix_det (Yau.LeafProofs.L18Aux.hMat_contDiffOn g a))
  have hnorm : ContDiffOn ℝ ∞ (fun z => ‖canonicalCoeff S a z‖^2) (chartTarget a) :=
    ContDiffOn.norm_sq (𝕜 := ℝ) hc
  have HH := hnorm.div hd (fun z hz => (Yau.LeafProofs.L18Aux.hMat_det_re_pos g.form a hz).ne')
  apply HH.congr
  intro z hz
  exact canonicalNormSq_inChart g.form S a hz

end Yau.Proofs.P04Aux
