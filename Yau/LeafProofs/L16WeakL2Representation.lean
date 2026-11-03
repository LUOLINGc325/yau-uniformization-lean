import Yau.Analysis.RangeRiesz
import Yau.LeafProofs.L16WeakLocalization

open MeasureTheory Filter
open scoped Topology ContDiff
noncomputable section
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

/-- The actual smooth compactly supported test functions in `U`. -/
def testFunctionSpace {n : ℕ} (U : Set (Point n)) : Submodule ℝ (Point n → ℝ) where
  carrier := {φ | Test U φ}
  zero_mem' := ⟨contDiff_const, HasCompactSupport.zero, by simp⟩
  add_mem' := by
    intro φ ψ hφ hψ
    exact ⟨hφ.1.add hψ.1, hφ.2.1.add hψ.2.1,
      (tsupport_add φ ψ).trans (Set.union_subset hφ.2.2 hψ.2.2)⟩
  smul_mem' := by
    intro c φ hφ
    refine ⟨contDiff_const.smul hφ.1, ?_, ?_⟩
    · exact hφ.2.1.smul_left (f := fun _ => c)
    · exact (tsupport_smul_subset_right (fun _ => c) φ).trans hφ.2.2

/-- A genuine test function belongs to the restricted `L²` space. -/
theorem test_memLp {n : ℕ} {U : Set (Point n)} {φ : Point n → ℝ}
    (hφ : Test U φ) : MemLp φ 2 (volume.restrict U) :=
  (hφ.1.continuous.memLp_of_hasCompactSupport hφ.2.1).restrict U

/-- Sending a test function to its actual `L²` class is linear. -/
def testToL2 {n : ℕ} (U : Set (Point n)) :
    testFunctionSpace U →ₗ[ℝ] Lp ℝ 2 (volume.restrict U) where
  toFun φ := (test_memLp φ.2).toLp φ.1
  map_add' φ ψ := by
    exact MemLp.toLp_add (test_memLp φ.2) (test_memLp ψ.2)
  map_smul' c φ := by
    exact MemLp.toLp_const_smul c (test_memLp φ.2)

/-- Directional differentiation preserves the genuine test function space. -/
def testDirectionalDerivative {n : ℕ} (U : Set (Point n)) (e : Point n) :
    testFunctionSpace U →ₗ[ℝ] testFunctionSpace U where
  toFun φ := ⟨fun p => fderiv ℝ φ.1 p e, test_directionalDerivative φ.2 e⟩
  map_add' φ ψ := by
    apply Subtype.ext
    funext p
    exact congrArg (fun L : Point n →L[ℝ] ℝ => L e)
      (fderiv_add (φ.2.1.differentiable (by simp) p)
        (ψ.2.1.differentiable (by simp) p))
  map_smul' c φ := by
    apply Subtype.ext
    funext p
    exact congrArg (fun L : Point n →L[ℝ] ℝ => L e)
      (fderiv_const_smul (φ.2.1.differentiable (by simp) p) c)

/-- The `L²` pairing with a test class is the integral against its raw function. -/
theorem inner_testToL2 {n : ℕ} {U : Set (Point n)}
    (g : Lp ℝ 2 (volume.restrict U)) (φ : testFunctionSpace U) :
    inner ℝ g (testToL2 U φ) = ∫ p, g p * φ.1 p ∂volume.restrict U := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(test_memLp φ.2).coeFn_toLp] with p hp
  simp only [testToL2, LinearMap.coe_mk, AddHom.coe_mk] at hp ⊢
  simp only [hp, RCLike.inner_apply, conj_trivial, mul_comm]

/-- A bounded distributional directional derivative has an actual `L²`
representative with the same bound; no density assumption is needed. -/
theorem exists_memLp_weak_directionalDerivative_of_bound {n : ℕ}
    {U : Set (Point n)} (_hU : IsOpen U) (e : Point n) (u : Point n → ℝ)
    (hu : MemLp u 2 (volume.restrict U)) (C : ℝ) (hC : 0 ≤ C)
    (hBound : ∀ φ : Point n → ℝ, Test U φ →
      |∫ p, u p * fderiv ℝ φ p e ∂volume.restrict U| ≤
        C * (eLpNorm φ 2 (volume.restrict U)).toReal) :
    ∃ g : Point n → ℝ, MemLp g 2 (volume.restrict U) ∧
      eLpNorm g 2 (volume.restrict U) ≤ ENNReal.ofReal C ∧
      ∀ φ : Point n → ℝ, Test U φ →
        (∫ p, u p * fderiv ℝ φ p e ∂volume.restrict U) =
          -(∫ p, g p * φ p ∂volume.restrict U) := by
  let f : testFunctionSpace U →ₗ[ℝ] ℝ :=
    -((innerSL ℝ (hu.toLp u)).toLinearMap.comp
      ((testToL2 U).comp (testDirectionalDerivative U e)))
  have hf (φ : testFunctionSpace U) :
      f φ = -(∫ p, u p * fderiv ℝ φ.1 p e ∂volume.restrict U) := by
    change -inner ℝ (hu.toLp u) (testToL2 U (testDirectionalDerivative U e φ)) = _
    rw [inner_testToL2]
    congr 1
    apply integral_congr_ae
    filter_upwards [hu.coeFn_toLp] with p hp
    simp only [testDirectionalDerivative, LinearMap.coe_mk, AddHom.coe_mk]
    rw [hp]
  have hfBound (φ : testFunctionSpace U) : ‖f φ‖ ≤ C * ‖testToL2 U φ‖ := by
    rw [hf, norm_neg, Real.norm_eq_abs]
    change _ ≤ C * ‖(test_memLp φ.2).toLp φ.1‖
    rw [Lp.norm_toLp]
    exact hBound φ.1 φ.2
  obtain ⟨g, hg, hgTest⟩ := Yau.Analysis.exists_norm_le_inner_eq_of_range_bound
    (testToL2 U) f C hC hfBound
  refine ⟨g, Lp.memLp g, ?_, ?_⟩
  · exact (ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top g)).symm ▸ ENNReal.ofReal_le_ofReal hg
  · intro φ hφ
    have h := hgTest ⟨φ,hφ⟩
    rw [inner_testToL2, hf] at h
    linarith

end Yau.LeafProofs.L16Aux
