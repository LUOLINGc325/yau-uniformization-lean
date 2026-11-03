import Yau.Proofs.P04CutoffModel

noncomputable section
open Set Filter
open scoped Topology ContDiff Manifold ENNReal
open MeasureTheory

namespace Yau.Proofs.P04Aux
open Yau Yau.LeafProofs
variable {n : ℕ} {M : ComplexManifold n}

def cutoffCoefficient (χ : ComplexVector n → ℝ) (z : ComplexVector n) : ComplexVector 1 :=
  scalarToCoefficient (χ z : ℂ)

def cutoffTop (p : M.Carrier) (χ : ComplexVector n → ℝ) :
    BundleDbar.NQForm (CanonicalCoefficients M) 0 :=
  L14Aux.topFormPushforward (CanonicalCoefficients M) p (cutoffCoefficient χ)

def cutoffDbar (p : M.Carrier) (χ : ComplexVector n → ℝ) :
    BundleDbar.NQForm (CanonicalCoefficients M) 1 :=
  L14Aux.oneFormPushforward (CanonicalCoefficients M) p (L14Aux.modelTopDbar (cutoffCoefficient χ))

theorem cutoffCoefficient_smooth {χ : ComplexVector n → ℝ} (hχ : ContDiff ℝ ∞ χ) :
    ContDiff ℝ ∞ (cutoffCoefficient χ) :=
  (scalarToCoefficient.restrictScalars ℝ).contDiff.comp (Complex.ofRealCLM.contDiff.comp hχ)

theorem cutoffCoefficient_tsupport {χ : ComplexVector n → ℝ} :
    tsupport (cutoffCoefficient χ) ⊆ tsupport χ := by
  apply closure_mono
  intro z hz hzero
  exact hz (by simp only [cutoffCoefficient,hzero,Complex.ofReal_zero,map_zero])

theorem cutoffCoefficient_compact {χ : ComplexVector n → ℝ} (hχ : HasCompactSupport χ) :
    HasCompactSupport (cutoffCoefficient χ) :=
  hχ.of_isClosed_subset (isClosed_tsupport _) cutoffCoefficient_tsupport

theorem cutoffTop_smooth (p : M.Carrier) {χ : ComplexVector n → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ chartTarget p) :
    BundleDbar.SmoothForm (r := 1) (CanonicalCoefficients M) (cutoffTop p χ) := by
  apply L14Aux.topFormPushforward_smooth (CanonicalCoefficients M) coefficient_holomorphic p
    (cutoffCoefficient χ) (cutoffCoefficient_smooth hχ) (cutoffCoefficient_compact hc)
  rw [coefficient_localDomain]
  exact cutoffCoefficient_tsupport.trans hs

theorem cutoff_isDbarOf (p : M.Carrier) {χ : ComplexVector n → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ chartTarget p) :
    BundleDbar.IsDbarOf (r := 1) (CanonicalCoefficients M) (cutoffTop p χ) (cutoffDbar p χ) := by
  apply L14Aux.topFormPushforward_isDbarOf (CanonicalCoefficients M) coefficient_holomorphic p
    (cutoffCoefficient χ) (cutoffCoefficient_smooth hχ) (cutoffCoefficient_compact hc)
  rw [coefficient_localDomain]
  exact cutoffCoefficient_tsupport.trans hs

theorem cutoffDbar_smooth (p : M.Carrier) {χ : ComplexVector n → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ chartTarget p) :
    BundleDbar.SmoothForm (r := 1) (CanonicalCoefficients M) (cutoffDbar p χ) :=
  L14Aux.smoothForm_of_isDbarOf (CanonicalCoefficients M) _ _
    (cutoffTop_smooth p hχ hc hs) (cutoff_isDbarOf p hχ hc hs)

theorem cutoff_weakDbar (p : M.Carrier) {χ : ComplexVector n → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ chartTarget p) :
    BundleDbar.WeakDbar (r := 1) (CanonicalCoefficients M) (cutoffTop p χ) (cutoffDbar p χ) :=
  L14Aux.weakDbar_of_smooth_isDbarOf (CanonicalCoefficients M) _ _
    (cutoffTop_smooth p hχ hc hs) (cutoffDbar_smooth p hχ hc hs) (cutoff_isDbarOf p hχ hc hs)

theorem cutoff_weaklyClosed (p : M.Carrier) {χ : ComplexVector n → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ chartTarget p) :
    BundleDbar.WeaklyClosed (r := 1) (CanonicalCoefficients M) (cutoffDbar p χ) :=
  L14Aux.weakDbar_weaklyClosed_top (CanonicalCoefficients M) _ _ (cutoff_weakDbar p hχ hc hs)

theorem cutoffTop_coefficient (p : M.Carrier) {χ : ComplexVector n → ℝ}
    {z : ComplexVector n} (hz : z ∈ chartTarget p) :
    BundleDbar.coefficients (r := 1) (CanonicalCoefficients M) (cutoffTop p χ) p z Fin.elim0 0 =
      (χ z : ℂ) := by
  have hz' : z ∈ BundleDbar.localDomain (r := 1) (CanonicalCoefficients M) p := by
    rwa [coefficient_localDomain]
  change (BundleDbar.coefficients (CanonicalCoefficients M)
    (L14Aux.topFormPushforward (CanonicalCoefficients M) p (cutoffCoefficient χ)) p z Fin.elim0) 0 = _
  rw [L14Aux.topFormPushforward_coefficients (CanonicalCoefficients M) p (cutoffCoefficient χ) z hz']
  exact scalarToCoefficient_apply _ 0

theorem cutoffTop_weightedL2 (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (p : M.Carrier) {χ : ComplexVector n → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ chartTarget p) :
    BundleDbar.WeightedL2 (r := 1) (CanonicalCoefficients M) g.form flatMetric μ φ (cutoffTop p χ) := by
  apply L14Aux.topFormPushforward_weightedL2 (CanonicalCoefficients M) g μ hμ flatMetric flatMetric_smooth
    φ hφ coefficient_holomorphic p (cutoffCoefficient χ)
    (cutoffCoefficient_smooth hχ) (cutoffCoefficient_compact hc)
  rw [coefficient_localDomain]
  exact cutoffCoefficient_tsupport.trans hs

theorem cutoffDbar_compact (p : M.Carrier) {χ : ComplexVector n → ℝ}
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ chartTarget p) :
    IsCompact (closure {x | cutoffDbar p χ x ≠ (0 : BundleDbar.NQForm (CanonicalCoefficients M) 1) x}) := by
  let F := cutoffCoefficient χ
  have hcF : HasCompactSupport F := cutoffCoefficient_compact hc
  have hsF : tsupport F ⊆ BundleDbar.localDomain (r := 1) (CanonicalCoefficients M) p := by
    rw [coefficient_localDomain]
    exact cutoffCoefficient_tsupport.trans hs
  have hcD : HasCompactSupport (L14Aux.modelTopDbar F) :=
    hcF.of_isClosed_subset (isClosed_tsupport _) (L14Aux.tsupport_modelTopDbar_subset F)
  have hsD := (L14Aux.tsupport_modelTopDbar_subset F).trans hsF
  have hK : IsCompact (chartInv p '' tsupport (L14Aux.modelTopDbar F)) := hcD.image_of_continuousOn
    ((continuousOn_extChartAt_symm (I := ComplexModel n) p).mono (hsD.trans inter_subset_left))
  exact hK.of_isClosed_subset isClosed_closure
    (L14Aux.oneFormPushforward_support (CanonicalCoefficients M) p (L14Aux.modelTopDbar F) hcD hsD)

end Yau.Proofs.P04Aux
