import Yau.Proofs.B01Forms
import Yau.Proofs.B01Image
import Yau.LeafProofs.L14Gauge

open scoped Manifold Topology ContDiff
open Bundle

noncomputable section

namespace Yau.Proofs.B01Aux
open Yau Yau.Blueprint Yau.Blueprint.BundlePresentation

variable {M : ComplexManifold 1} {r : ℕ}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

def cutoffSourceLinear (c : DiscCoordinate M) (s : Section E) (χ : M.Carrier → ℝ)
    (x : M.Carrier) : TangentVector M x →ₗ[ℝ]
      ((TangentVector M x) [⋀^Fin 1]→ₗ[ℂ] E x) :=
  let b : TangentVector M x →ₗ[ℝ] ℂ := discDbarScalar c χ x •
    (Complex.conjCLE.toLinearMap.comp ((discDerivative c x).restrictScalars ℝ))
  let Q := (sectionTopForm E c s x).1 Fin.elim0
  { toFun := fun v => b v • Q
    map_add' := by
      intro u v
      ext w
      change b (u + v) • Q w = b u • Q w + b v • Q w
      rw [map_add, add_smul]
    map_smul' := by
      intro a v
      ext w
      change b (a • v) • Q w = a • (b v • Q w)
      rw [map_smul, smul_assoc] }

theorem cutoffSourceLinear_apply (c : DiscCoordinate M) (s : Section E) (χ : M.Carrier → ℝ)
    (x : M.Carrier) (v : TangentVector M x) (w : Fin 1 → TangentVector M x) :
    (cutoffSourceLinear E c s χ x v) w =
      (discDbarScalar c χ x * star (discDerivative c x v) * discDerivative c x (w 0)) • s x := by
  change (discDbarScalar c χ x * star (discDerivative c x v)) •
    (discDerivative c x (w 0) • s x) = _
  rw [smul_smul]

def cutoffSourceForm (c : DiscCoordinate M) (s : Section E) (χ : M.Carrier → ℝ) :
    BundleDbar.NQForm E 1 := fun x =>
  ⟨AlternatingMap.ofSubsingleton ℝ (TangentVector M x)
    ((TangentVector M x) [⋀^Fin 1]→ₗ[ℂ] E x) (0 : Fin 1)
      (cutoffSourceLinear E c s χ x), by
    intro v i a
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    apply AlternatingMap.ext
    intro w
    change (cutoffSourceLinear E c s χ x (a • v 0)) w =
      star a • (cutoffSourceLinear E c s χ x (v 0)) w
    rw [cutoffSourceLinear_apply, cutoffSourceLinear_apply, map_smul,
      smul_eq_mul, star_mul, smul_smul]
    congr 1
    ring⟩

theorem cutoffSourceForm_spec (c : DiscCoordinate M) (s : Section E) (χ : M.Carrier → ℝ) :
    IsCutoffSourceForm E c s χ (cutoffSourceForm E c s χ) := by
  intro x v w
  exact cutoffSourceLinear_apply E c s χ x (v 0) w

theorem cutoffSourceForm_eq (c : DiscCoordinate M) (s : Section E) (χ : M.Carrier → ℝ)
    (f : BundleDbar.NQForm E 1) (hf : IsCutoffSourceForm E c s χ f) :
    f = cutoffSourceForm E c s χ := by
  funext x
  apply Subtype.ext
  apply AlternatingMap.ext
  intro v
  apply AlternatingMap.ext
  intro w
  exact (hf x v w).trans (cutoffSourceForm_spec E c s χ x v w).symm

theorem weaklyClosed_one_of_locallyL2 (f : BundleDbar.NQForm E 1)
    (hf : BundleDbar.LocallyL2 (r := r) E f) : BundleDbar.WeaklyClosed (r := r) E f := by
  refine ⟨hf, ?_⟩
  intro a I α ψ _ _ _
  have hI : I = fun _ : Fin 2 => (0 : Fin 1) := Subsingleton.elim _ _
  rw [hI]
  simp [Fin.sum_univ_two]

include r E in
theorem smoothFn_in_disc (c : DiscCoordinate M) (hc : IsDiscCoordinate c)
    (χ : M.Carrier → ℝ) (hχ : SmoothFn χ) :
    ContDiffOn ℝ ∞ (fun z : ℂ => χ (c.symm z)) puncturedUnitDisc := by
  intro z hz
  let a := c.symm z
  have hm : z ∈ imageFrameDomain (r := r) E c a := by
    simpa only [a, disc_right_inv c hc hz] using imageFrameDomain_self (r := r) E c a
  have hb := (baseChange_contDiffAt (r := r) E c hc a hm).restrict_scalars ℝ
  have hx := ((hχ a).contDiffAt ((isOpen_extChartAt_target (I := ComplexModel 1) a).mem_nhds
    (baseChange_mem_localDomain (r := r) E c hc a hm).1)).comp z hb
  have he : (fun w : ℂ => χ (c.symm w)) =ᶠ[𝓝 z]
      (fun w => χ (chartInv a (baseChange c a w))) := by
    filter_upwards [(imageFrameDomain_isOpen (r := r) E c hc a).mem_nhds hm] with w hw
    rw [chartInv_baseChange (r := r) E c hc a hw]
  exact (hx.congr_of_eventuallyEq he).contDiffWithinAt

theorem discDbarScalar_inChart_contDiffOn (c : DiscCoordinate M) (hc : IsDiscCoordinate c)
    (χ : M.Carrier → ℝ) (hχ : SmoothFn χ) (a : M.Carrier) :
    ContDiffOn ℝ ∞ (fun z => discDbarScalar c χ (chartInv a z))
      (BundleDbar.localDomain (r := r) E a) := by
  have hreal := smoothFn_in_disc (r := r) E c hc χ hχ
  have hcomplex : ContDiffOn ℝ ∞ (fun z : ℂ => (χ (c.symm z) : ℂ)) puncturedUnitDisc :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hreal
  have hw := LeafProofs.L14Aux.wirtBar_contDiffOn puncturedUnitDisc_isOpen _ hcomplex (1 : ℂ)
  have hF : ContDiffOn ℝ ∞ (fun w => c (chartInv a w)) (BundleDbar.localDomain (r := r) E a) :=
    fun z hz => ((disc_inChart_contDiffAt c hc a hz.1).restrict_scalars ℝ).contDiffWithinAt
  exact hw.comp hF (fun z _ => disc_mem c hc (chartInv a z))

theorem cutoffSourceForm_coefficients (c : DiscCoordinate M) (hc : IsDiscCoordinate c)
    (s : Section E) (χ : M.Carrier → ℝ) (a : M.Carrier) (z : ComplexVector 1)
    (hz : z ∈ BundleDbar.localDomain (r := r) E a) (I : Fin 1 → Fin 1) :
    BundleDbar.coefficients (r := r) E (cutoffSourceForm E c s χ) a z I =
      (discDbarScalar c χ (chartInv a z) *
        star (wirt (fun w => c (chartInv a w)) z (stdVec 0)) *
          wirt (fun w => c (chartInv a w)) z (stdVec 0)) •
            sectionCoefficients (r := r) E s a z := by
  have hI : I = fun _ : Fin 1 => (0 : Fin 1) := Subsingleton.elim _ _
  rw [hI]
  unfold BundleDbar.coefficients
  rw [cutoffSourceForm_spec E c s χ, map_smul]
  have hd : (show ℂ from mfderiv (ComplexModel 1) 𝓘(ℂ, ℂ) c (chartInv a z)
      (chartVec a (chartInv a z) (stdVec 0))) =
      wirt (fun w => c (chartInv a w)) z (stdVec 0) := by
    exact (disc_inChart_fderiv c hc a hz.1 (stdVec 0)).symm.trans
      (LeafProofs.L14Aux.wirt_eq_fderiv_of_complex_differentiable
        _ _ _ ((disc_inChart_contDiffAt c hc a hz.1).differentiableAt (by simp))).symm
  change (_ * star (show ℂ from mfderiv (ComplexModel 1) 𝓘(ℂ, ℂ) c (chartInv a z)
    (chartVec a (chartInv a z) (stdVec 0))) *
      (show ℂ from mfderiv (ComplexModel 1) 𝓘(ℂ, ℂ) c (chartInv a z)
        (chartVec a (chartInv a z) (stdVec 0)))) • sectionCoefficients (r := r) E s a z = _
  rw [hd]

theorem cutoffSourceForm_coefficients_normSq (c : DiscCoordinate M) (hc : IsDiscCoordinate c)
    (s : Section E) (χ : M.Carrier → ℝ) (a : M.Carrier) (z : ComplexVector 1)
    (hz : z ∈ BundleDbar.localDomain (r := r) E a) (I : Fin 1 → Fin 1) :
    BundleDbar.coefficients (r := r) E (cutoffSourceForm E c s χ) a z I =
      (discDbarScalar c χ (chartInv a z) *
        (Complex.normSq (wirt (fun w => c (chartInv a w)) z (stdVec 0)) : ℂ)) •
          sectionCoefficients (r := r) E s a z := by
  rw [cutoffSourceForm_coefficients E c hc s χ a z hz I]
  congr 1
  rw [mul_assoc, mul_comm (star _) _, Complex.star_def, Complex.mul_conj]

theorem cutoffSourceForm_smooth (c : DiscCoordinate M) (hc : IsDiscCoordinate c)
    (s : Section E) (hs : HolomorphicSection (r := r) E s)
    (χ : M.Carrier → ℝ) (hχ : SmoothFn χ) :
    BundleDbar.SmoothForm (r := r) E (cutoffSourceForm E c s χ) := by
  intro a I α
  have hb := discDbarScalar_inChart_contDiffOn (r := r) E c hc χ hχ a
  have hF : ContDiffOn ℝ ∞ (fun w => c (chartInv a w)) (BundleDbar.localDomain (r := r) E a) :=
    fun z hz => ((disc_inChart_contDiffAt c hc a hz.1).restrict_scalars ℝ).contDiffWithinAt
  have hJ := LeafProofs.L14Aux.wirt_contDiffOn (LeafProofs.L14Aux.localDomain_isOpen (r := r) E a)
    _ hF (stdVec 0)
  have hS := (holomorphic_contDiffOn_one (hs a) (LeafProofs.L14Aux.localDomain_isOpen (r := r) E a)).restrict_scalars ℝ
  have hα := (contDiffOn_piLp 2).mp hS α
  have hJc : ContDiffOn ℝ ∞ (fun z => star (wirt (fun w => c (chartInv a w)) z (stdVec 0)))
      (BundleDbar.localDomain (r := r) E a) := Complex.conjCLE.contDiff.comp_contDiffOn hJ
  have ht := (((hb.mul hJc).mul hJ).mul hα)
  apply ht.congr
  intro z hz
  exact congrArg (fun v : ComplexVector r => v α) (cutoffSourceForm_coefficients E c hc s χ a z hz I)

theorem cutoffSourceFormRealization : CutoffSourceFormRealization (r := r) E := by
  intro c hc _ s χ hs hχ
  have hf := cutoffSourceForm_smooth E c hc s hs χ hχ
  exact ⟨cutoffSourceForm E c s χ, cutoffSourceForm_spec E c s χ, hf,
    weaklyClosed_one_of_locallyL2 E _ (LeafProofs.L14Aux.smoothForm_locallyL2 E _ hf)⟩

end Yau.Proofs.B01Aux
