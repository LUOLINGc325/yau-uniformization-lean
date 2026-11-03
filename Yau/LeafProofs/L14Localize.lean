import Yau.LeafProofs.L14SquarePartition
import Yau.LeafProofs.L14Dbar
import Yau.LeafProofs.L14CoefficientTransitions

noncomputable section
open scoped Manifold Topology ContDiff ComplexOrder ENNReal Matrix
open MeasureTheory Bundle Filter Module

namespace Yau.LeafProofs.L14Aux
open BundleDbar

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

def compactOneChartCoefficients (η : M.Carrier → ℝ) (u : NQForm E 1) (a : M.Carrier)
    (z : ComplexVector n) (i : Fin n) : ComplexVector r :=
  Complex.ofReal (L18Aux.chartPullbackZero a η z) • coefficients (r := r) E u a z (fun _ => i)

theorem compactOneChartCoefficients_properties (η : M.Carrier → ℝ) (hη : SmoothFn η)
    (hcη : HasCompactSupport η) (u : NQForm E 1) (hu : SmoothForm (r := r) E u)
    (a : M.Carrier) (hηa : tsupport η ⊆ bundleChartSource (r := r) E a) :
    ContDiff ℝ ∞ (compactOneChartCoefficients (r := r) E η u a) ∧
      HasCompactSupport (compactOneChartCoefficients (r := r) E η u a) ∧
        tsupport (compactOneChartCoefficients (r := r) E η u a) ⊆ localDomain (r := r) E a := by
  let ψ := L18Aux.chartPullbackZero a η
  let F := compactOneChartCoefficients (r := r) E η u a
  have hηchart : tsupport η ⊆ (extChartAt (ComplexModel n) a).source := hηa.trans Set.inter_subset_left
  obtain ⟨hcψ, hψ, hsψ⟩ := L18Aux.chartPullbackZero_smoothFn a hη hcη hηchart
  have hsψO : tsupport ψ ⊆ localDomain (r := r) E a := by
    intro z hz
    rcases L18Aux.chartPullbackZero_tsupport_subset a hcη hηchart hz with ⟨x, hx, rfl⟩
    refine ⟨(extChartAt (ComplexModel n) a).map_source (hηa hx).1, ?_⟩
    change chartInv a (chartPt a x) ∈ (localTriv (r := r) E a).baseSet
    rw [chartInv_chartPt_of_mem a x (by simpa only [extChartAt_source] using (hηa hx).1)]
    exact (hηa hx).2
  have hFs : tsupport F ⊆ tsupport ψ := by
    apply closure_minimal _ (isClosed_tsupport ψ)
    intro z hz
    by_contra hn
    have hψz : ψ z = 0 := image_eq_zero_of_notMem_tsupport hn
    apply hz
    funext i
    change (ψ z : ℂ) • coefficients (r := r) E u a z (fun _ => i) = 0
    rw [hψz, Complex.ofReal_zero, zero_smul]
  have hFOn (i : Fin n) (α : Fin r) :
      ContDiffOn ℝ ∞ (fun z => F z i α) (localDomain (r := r) E a) := by
    change ContDiffOn ℝ ∞ (fun z => Complex.ofReal (ψ z) *
      coefficients (r := r) E u a z (fun _ => i) α) _
    exact ((Complex.ofRealCLM.contDiff.comp hψ).contDiffOn).mul (hu a (fun _ => i) α)
  refine ⟨?_, hcψ.of_isClosed_subset (isClosed_tsupport F) hFs, hFs.trans hsψO⟩
  apply contDiff_pi.mpr
  intro i
  apply (contDiff_piLp 2).mpr
  intro α
  apply contDiff_of_contDiffOn_of_tsupport_subset (localDomain_isOpen E a) _ (hFOn i α)
  exact (tsupport_comp_subset (g := fun V : Fin n → ComplexVector r => V i α) (by rfl) F).trans
    (hFs.trans hsψO)

theorem oneTensorCoordinates_at_chartPt (u : NQForm E 1) (a x : M.Carrier)
    (hx : x ∈ bundleChartSource (r := r) E a) (i : Fin n) (α : Fin r) :
    oneTensorCoordinates (r := r) E a x hx (u x) (i, α) =
      coefficients (r := r) E u a (chartPt a x) (fun _ => i) α := by
  have hInv : chartInv a (chartPt a x) = x :=
    chartInv_chartPt_of_mem a x (by simpa only [extChartAt_source] using hx.1)
  have hz : chartPt a x ∈ localDomain (r := r) E a := by
    refine ⟨(extChartAt (ComplexModel n) a).map_source hx.1, ?_⟩
    change chartInv a (chartPt a x) ∈ (localTriv (r := r) E a).baseSet
    rw [hInv]
    exact hx.2
  rw [coefficients_at_chartPt E u a x hx.1]
  simp only [oneTensorCoordinates, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp,
    bundleFrameBasis_repr, chartFrameBasis_apply]
  have hb : (chartFrameBasis a x hx.1) = (fun k => chartVec a x (stdVec k)) :=
    funext (fun k => chartFrameBasis_apply a x hx.1 k)
  rw [hb]

theorem oneTensorCoordinates_multiplyForm (η : M.Carrier → ℂ) (u : NQForm E 1)
    (a x : M.Carrier) (hx : x ∈ bundleChartSource (r := r) E a) :
    oneTensorCoordinates (r := r) E a x hx (multiplyForm E η u x) =
      η x • oneTensorCoordinates (r := r) E a x hx (u x) := by
  ext p
  simp only [oneTensorCoordinates, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp,
    multiplyForm, AlternatingMap.smul_apply, map_smul, Finsupp.smul_apply,
    PiLp.smul_apply, smul_eq_mul]

set_option backward.isDefEq.respectTransparency false in
theorem multiplyForm_eq_oneFormPushforward (η : M.Carrier → ℝ) (u : NQForm E 1)
    (a : M.Carrier) (hηa : tsupport η ⊆ bundleChartSource (r := r) E a) :
    multiplyForm E (fun x => (η x : ℂ)) u =
      oneFormPushforward (r := r) E a (compactOneChartCoefficients (r := r) E η u a) := by
  classical
  funext x
  by_cases hx : x ∈ bundleChartSource (r := r) E a
  · have hF : (oneFormPushforward (r := r) E a (compactOneChartCoefficients (r := r) E η u a) x :
        antiComplexSubmodule E x 1) = oneTensorFromCoefficients (r := r) E a x hx
          (compactOneChartCoefficients (r := r) E η u a (chartPt a x)) := by
      exact dif_pos hx
    rw [hF]
    apply oneTensorCoordinates_injective E a x hx
    ext p
    rcases p with ⟨i, α⟩
    rw [oneTensorCoordinates_fromCoefficients]
    rw [oneTensorCoordinates_multiplyForm]
    change (η x : ℂ) * oneTensorCoordinates (r := r) E a x hx (u x) (i, α) = _
    rw [oneTensorCoordinates_at_chartPt E u a x hx i α]
    change _ = Complex.ofReal (L18Aux.chartPullbackZero a η (chartPt a x)) *
      coefficients (r := r) E u a (chartPt a x) (fun _ => i) α
    rw [L18Aux.chartPullbackZero_chartPt a η hx.1]
  · have hηzero : η x = 0 := by
      by_contra hn
      exact hx (hηa (subset_tsupport η hn))
    change multiplyForm E (fun x => (η x : ℂ)) u x =
      if hx : x ∈ bundleChartSource (r := r) E a then
        oneTensorFromCoefficients (r := r) E a x hx
          (compactOneChartCoefficients (r := r) E η u a (chartPt a x)) else 0
    rw [dif_neg hx]
    apply Subtype.ext
    simp only [multiplyForm, hηzero, Complex.ofReal_zero, zero_smul]
    rfl

end Yau.LeafProofs.L14Aux
