import Yau.Proofs.D03ApproximationEstimate
import Yau.Proofs.D03RepresentativeBundle

set_option backward.isDefEq.respectTransparency false

noncomputable section

open MeasureTheory Filter Set Bundle
open scoped Topology ContDiff Manifold ENNReal

namespace Yau.Proofs.D03Aux
open Yau Yau.BundleDbar Yau.Blueprint.BundlePresentation
open Yau.LeafProofs.L14Aux

variable {M : ComplexManifold 1} {r : ℕ}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (Bundle.TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

/-- Compact tests pair integrably with the actual locally L² coefficients. -/
theorem locallyL2_test_integrable {q : ℕ}
    (u : NQForm E q) (hu : LocallyL2 (r := r) E u)
    (a : M.Carrier) (I : Fin q → Fin 1) (α : Fin r)
    (ψ : ComplexVector 1 → ℂ) (hψ : Continuous ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ localDomain (r := r) E a) :
    Integrable (fun z => coefficients (r := r) E u a z I α * ψ z) (Yau.lebesgueC 1) := by
  have hp : IntegrableOn (fun z => coefficients (r := r) E u a z I α * ψ z)
      (tsupport ψ) (Yau.lebesgueC 1) :=
    test_mul_integrable_of_memLp ((Yau.lebesgueC 1).restrict (tsupport ψ)) _ ψ
      (locallyL2_coefficients_memLp (r := r) E u hu a I α (tsupport ψ) hc hs)
      (compact_test_memLp ψ hψ hc (tsupport ψ))
  exact (integrableOn_iff_integrable_of_support_subset
    ((Function.support_mul_subset_right _ _).trans (subset_tsupport ψ))).mp hp

/-- Subtracting two actual weak solutions of the same source gives a weakly
closed original top form, with all compact-test integrability justified. -/
theorem weakDbar_difference_zero
    (u v : NQForm E 0) (f : NQForm E 1)
    (hu : WeakDbar (r := r) E u f) (hv : WeakDbar (r := r) E v f) :
    WeakDbar (r := r) E (u + (-1 : ℂ) • v) 0 := by
  apply (weakDbar_zero_iff_component_tests (r := r) E _ _).mpr
  refine ⟨locallyL2_add (r := r) E u _ hu.1 (locallyL2_smul (r := r) E (-1) v hv.1),
    locallyL2_zero (r := r) E 1, ?_⟩
  intro a i α ψ hψ hcψ hsψ
  have htu := ((weakDbar_zero_iff_component_tests (r := r) E u f).mp hu).2.2 a i α ψ hψ hcψ hsψ
  have htv := ((weakDbar_zero_iff_component_tests (r := r) E v f).mp hv).2.2 a i α ψ hψ hcψ hsψ
  have hI : (∫ z, coefficients (r := r) E u a z Fin.elim0 α *
      wirtBar ψ z (stdVec i) ∂Yau.lebesgueC 1) =
      ∫ z, coefficients (r := r) E v a z Fin.elim0 α *
        wirtBar ψ z (stdVec i) ∂Yau.lebesgueC 1 := neg_injective (htu.symm.trans htv)
  have htest := wirtBar_contDiff ψ hψ (stdVec i)
  have hctest := wirtBar_hasCompactSupport ψ hcψ (stdVec i)
  have hstest : tsupport (fun z => wirtBar ψ z (stdVec i)) ⊆ localDomain (r := r) E a :=
    (Yau.LeafProofs.L21Aux.tsupport_wirtBar_subset ψ (stdVec i)).trans hsψ
  have hIntu := locallyL2_test_integrable E u hu.1 a Fin.elim0 α _ htest.continuous hctest hstest
  have hIntv := locallyL2_test_integrable E v hv.1 a Fin.elim0 α _ htest.continuous hctest hstest
  simp only [coefficients_zero, zero_mul, integral_zero]
  simp only [coefficients_add, coefficients_smul, add_mul, mul_assoc]
  rw [integral_add hIntu (hIntv.const_mul (-1)), integral_const_mul, hI]
  ring

/-- The original section multiplied by the chosen cutoff. -/
def cutoffSection (c : DiscCoordinate M) (s : Section E) (n : ℕ) : Section E :=
  fun x => (cutoff c n x : ℂ) • s x

theorem sectionCoefficients_smul_function
    (s : Section E) (η : M.Carrier → ℂ) (a : M.Carrier) (z : ComplexVector 1) :
    sectionCoefficients (r := r) E (fun x => η x • s x) a z =
      η (chartInv a z) • sectionCoefficients (r := r) E s a z := by
  exact map_smul ((localTriv (r := r) E a).continuousLinearMapAt ℂ (chartInv a z))
    (η (chartInv a z)) (s (chartInv a z))

theorem sectionCoefficients_cutoffSection
    (c : DiscCoordinate M) (s : Section E) (n : ℕ) (a : M.Carrier) (z : ComplexVector 1) :
    sectionCoefficients (r := r) E (cutoffSection E c s n) a z =
      (cutoff c n (chartInv a z) : ℂ) • sectionCoefficients (r := r) E s a z :=
  sectionCoefficients_smul_function (r := r) E s (fun x => (cutoff c n x : ℂ)) a z

/-- The cutoff top form is smooth in every original chart and frame. -/
theorem cutoff_topForm_smooth
    (c : DiscCoordinate M) (hc : IsDiscCoordinate c) (s : Section E)
    (hs : HolomorphicSection (r := r) E s) (n : ℕ) :
    SmoothForm (r := r) E (B01Aux.sectionTopForm E c (cutoffSection E c s n)) := by
  intro a I α
  have hI : I = Fin.elim0 := Subsingleton.elim _ _
  subst I
  have hC : ContDiffOn ℝ ∞ (fun z => c (chartInv a z)) (localDomain (r := r) E a) :=
    fun z hz => ((B01Aux.disc_inChart_contDiffAt c hc a hz.1).restrict_scalars ℝ).contDiffWithinAt
  have hJ := wirt_contDiffOn (localDomain_isOpen (r := r) E a) _ hC (stdVec 0)
  have hχ : ContDiffOn ℝ ∞ (fun z => (cutoff c n (chartInv a z) : ℂ)) (localDomain (r := r) E a) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn ((cutoff_smooth c hc n a).mono inter_subset_left)
  have hS := (B01Aux.holomorphic_contDiffOn_one (hs a) (localDomain_isOpen (r := r) E a)).restrict_scalars ℝ
  apply ((hJ.mul hχ).mul ((contDiffOn_piLp 2).mp hS α)).congr
  intro z hz
  rw [sectionTopForm_coefficients E c hc _ a z hz]
  rw [sectionCoefficients_cutoffSection E c s n a z]
  simp only [PiLp.smul_apply, smul_eq_mul]
  ring

include r E in
/-- The scalar chain rule in the actual global base coordinate. -/
theorem chart_dbar_cutoff
    (c : DiscCoordinate M) (hc : IsDiscCoordinate c) (n : ℕ)
    (a : M.Carrier) (z : ComplexVector 1) (hz : z ∈ chartTarget a) :
    wirtBar (fun w => (cutoff c n (chartInv a w) : ℂ)) z (stdVec 0) =
      discDbarScalar c (cutoff c n) (chartInv a z) *
        star (wirt (fun w => c (chartInv a w)) z (stdVec 0)) := by
  let T : ComplexVector 1 → ℂ := fun w => c (chartInv a w)
  let H : ℂ → ℂ := fun w => (cutoff c n (c.symm w) : ℂ)
  have hT := (B01Aux.disc_inChart_contDiffAt c hc a hz).differentiableAt (by simp)
  have hH : DifferentiableAt ℝ H (T z) := by
    have hm := B01Aux.disc_mem c hc (chartInv a z)
    have hHC : ContDiffOn ℝ ∞ H Yau.Blueprint.puncturedUnitDisc :=
      Complex.ofRealCLM.contDiff.comp_contDiffOn
        (B01Aux.smoothFn_in_disc (r := r) E c hc (cutoff c n) (cutoff_smooth c hc n))
    exact ((hHC.differentiableOn (by simp)) (T z) hm).differentiableAt
      (B01Aux.puncturedUnitDisc_isOpen.mem_nhds hm)
  have heq : (fun w => (cutoff c n (chartInv a w) : ℂ)) =ᶠ[𝓝 z] (fun w => H (T w)) := by
    apply Eventually.of_forall
    intro w
    dsimp only [H, T]
    rw [B01Aux.disc_left_inv c hc]
  rw [show wirtBar (fun w => (cutoff c n (chartInv a w) : ℂ)) z (stdVec 0) =
      wirtBar (fun w => H (T w)) z (stdVec 0) from by
        unfold wirtBar; rw [heq.fderiv_eq]]
  rw [wirtBar_comp_complex_differentiable T H z (stdVec 0) hT hH]
  have hd : fderiv ℂ T z (stdVec 0) = wirt T z (stdVec 0) :=
    (wirt_eq_fderiv_of_complex_differentiable T z (stdVec 0) hT).symm
  rw [hd]
  have he : wirt T z (stdVec 0) = wirt T z (stdVec 0) • (1 : ℂ) := by simp
  rw [he, wirtBar_smul_direction]
  dsimp only [H, T, discDbarScalar]
  ring

end Yau.Proofs.D03Aux
