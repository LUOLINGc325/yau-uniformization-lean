import Yau.LeafProofs.L16InteriorDirichletPatch
import Yau.LeafProofs.L16WholeSpaceLinearFactory
import Yau.LeafProofs.L16PatchSourceOperators

open MeasureTheory Filter Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates
local instance interiorLinearFactory_group {n : ℕ} (α : ℝ) (O : Set (Space n)) (T : ℝ) :
    NormedAddCommGroup (compatibleHolderGraph α O T) := inferInstance
local instance interiorLinearFactory_space {n : ℕ} (α : ℝ) (O : Set (Space n)) (T : ℝ) :
    NormedSpace ℝ (compatibleHolderGraph α O T) := inferInstance

/-- The actual interior source CLM and actual linear whole-space inverse
compose to a genuine source-linear physical patch factory. All constants
precede time, interpolation scale, coefficient fields and forcing. -/
theorem interiorDirichlet_linear_factory_uniform_short {n : ℕ} {O : Set (Space n)}
    {α M lam upper P : ℝ} (hα : 0 < α) (hα1 : α < 1) (hM : 0 ≤ M) (hP : 0 ≤ P)
    (z : Space n) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hInside : Metric.closedBall z (4*r) ⊆ O)
    (ψ : Space n → ℝ)
    (hψ : HolderBound α (cylinder univ 0 1) (fun p => ψ p.1) P)
    (hPlateau : ∀ x, outerPatchBump r hr z x*ψ x = ψ x) :
    ∃ δ C : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < C ∧
      ∀ (ρ T : ℝ) (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ),
      0 < ρ → ρ ≤ 1 → 0 < T → T ≤ δ → T ≤ ρ^2 →
      Elliptic (cylinder (closure O) 0 T) a lam upper →
      HolderBound α (cylinder (closure O) 0 T) a M →
      (∀ i, HolderBound α (cylinder (closure O) 0 T) (fun p => b p i) M) →
      ∃ V : compatibleHolderGraph α O T → Point n → ℝ,
        (∀ f g p, p ∈ cylinder univ 0 T → V (f+g) p = V f p+V g p) ∧
        (∀ (a : ℝ) f p, p ∈ cylinder univ 0 T → V (a • f) p = a*V f p) ∧
        ∀ f,
          let v := V f
          let w := interiorDirichletPatch z r hr v
          SchauderBound α (cylinder univ 0 T) v (C*‖f‖) ∧
          HolderBound α (cylinder univ 0 T) (fun p => (v p,spatialD v p)) (C*‖f‖*ρ^(1-α)) ∧
          (∀ y, v (y,0) = 0) ∧
          SchauderBound α (cylinder univ 0 T) w (C*‖f‖) ∧
          HolderBound α (cylinder univ 0 T) (fun p => (w p,spatialD w p)) (C*‖f‖*ρ^(1-α)) ∧
          (∀ x, w (x,0) = 0) ∧
          (∀ x ∈ frontier O, ∀ t ∈ Icc 0 T, w (x,t) = 0) ∧
          ∀ p ∈ cylinder (closure O) 0 T,
            linearOp (cylinder (closure O) 0 T) a b w p = ψ p.1*compatibleHolderFun f p-
              spatialCutoffCommutator a b (outerPatchBump r hr z) v p := by
  obtain ⟨J,hJ,hCoefficients⟩ := interiorDirichlet_coefficient_extension
    (lam := lam) (upper := upper) hα hα1 hM z hr hInside
  obtain ⟨CG,hCG,hTransport⟩ := interiorDirichlet_transport hα hα1 z hr hr1 hInside
  have hSupport : tsupport ψ ⊆ closure O := by
    change closure (Function.support ψ) ⊆ closure O
    apply closure_minimal _ isClosed_closure
    intro x hx
    have hφNonzero : outerPatchBump r hr z x ≠ 0 := by
      intro hZero
      have h := hPlateau x
      rw [hZero,zero_mul] at h
      exact (Function.mem_support.mp hx) h.symm
    have hxφ := subset_tsupport (outerPatchBump r hr z : Space n → ℝ) (Function.mem_support.mpr hφNonzero)
    rw [(outerPatchBump r hr z).tsupport_eq] at hxφ
    have hxBall : x ∈ Metric.closedBall z (2*r) := hxφ
    exact subset_closure (hInside ((Metric.closedBall_subset_closedBall (by linarith : 2*r ≤ 4*r)) hxBall))
  obtain ⟨δ,C0,hδ,hδ1,hC0,hInverse⟩ := exists_uniform_short_linear_schauder_inverse_holder_only
    (M := J) (lam := min lam 1) (upper := max upper 1) hα hα1 (isCompact_closedBall z (3*r))
  let A : ℝ := 1+C0*(2*P)
  let C : ℝ := 1+17*A+17*CG*A
  have hA : 0 < A := by dsimp only [A]; positivity
  have hCGA : 0 ≤ CG*A := mul_nonneg hCG.le hA.le
  have hC : 0 < C := by dsimp only [C]; positivity
  have hAC : A ≤ C := by dsimp only [C]; nlinarith only [hA,hCGA]
  have h16AC : 16*A ≤ C := by dsimp only [C]; nlinarith only [hA,hCGA]
  have h17GC : 17*CG*A ≤ C := by dsimp only [C]; linarith only [hA]
  have h16GC : 16*CG*A ≤ C := by dsimp only [C]; nlinarith only [hA,hCGA]
  refine ⟨δ,C,hδ,hδ1,hC,?_⟩
  intro ρ T a b hρ hρ1 hT hTδ hTρ hEll ha hb
  have hT1 : T ≤ 1 := hTδ.trans hδ1
  have hCoeff := hCoefficients T a b hEll ha hb
  have hψT : HolderBound α (cylinder univ 0 T) (fun p => ψ p.1) P :=
    holderBound_mono hψ (cylinder_mono_time hT1)
  obtain ⟨L,hL,hLEq⟩ := interior_patch_source_operator hα hT.le hψT hSupport
  obtain ⟨U,hUAdd,hUSmul,hU⟩ := hInverse T
    (interiorDirichletPrincipalExtension z r hr a) (interiorDirichletDriftExtension z r hr b)
    hT hTδ hCoeff.2.1 hCoeff.2.2.1 hCoeff.1
    (fun p hp hOut => (hCoeff.2.2.2.1 p hp hOut).1)
  let V : compatibleHolderGraph α O T → Point n → ℝ := fun f => U (L f)
  refine ⟨V,?_,?_,?_⟩
  · intro f g p hp
    change U (L (f+g)) p = _
    rw [L.map_add]
    exact hUAdd _ _ p hp
  · intro a f p hp
    change U (L (a • f)) p = _
    rw [L.map_smul]
    exact hUSmul a _ p hp
  · intro f
    let v := V f
    obtain ⟨hV,hVLow,hV0,hVPDE0⟩ := hU (L f)
    have hVPDE : ∀ p ∈ cylinder univ 0 T,
        linearOp (cylinder univ 0 T) (interiorDirichletPrincipalExtension z r hr a)
          (interiorDirichletDriftExtension z r hr b) v p = ψ p.1*compatibleHolderFun f p := by
      intro p hp
      exact (hVPDE0 p hp).trans (hLEq f hp)
    have hModelBudget : C0*‖L f‖ ≤ A*‖f‖ := by
      have hLf : ‖L f‖ ≤ (2*P)*‖f‖ := (L.le_opNorm f).trans
        (mul_le_mul_of_nonneg_right hL (norm_nonneg f))
      calc
        _ ≤ C0*((2*P)*‖f‖) := mul_le_mul_of_nonneg_left hLf hC0.le
        _ ≤ A*‖f‖ := by dsimp only [A]; nlinarith only [norm_nonneg f]
    have hVA := schauderBound_mono_const hV hModelBudget
    have hSmall := zero_initial_schauder_lowPair_small hα hα1 hT hρ hρ1 hTρ hVA hV0
    have hPatch := hTransport ψ hPlateau T (A*‖f‖) (16*(A*‖f‖)*ρ^(1-α))
      a b (compatibleHolderFun f) v hT1 hVA hSmall hV0 hVPDE
    have hPower0 : 0 ≤ ρ^(1-α) := Real.rpow_nonneg hρ.le _
    have hPower1 : ρ^(1-α) ≤ 1 := Real.rpow_le_one hρ.le hρ1 (by linarith only [hα1])
    have hModelHigh : A*‖f‖ ≤ C*‖f‖ := mul_le_mul_of_nonneg_right hAC (norm_nonneg f)
    have hModelLow : 16*(A*‖f‖)*ρ^(1-α) ≤ C*‖f‖*ρ^(1-α) := by
      calc
        _ = (16*A)*(‖f‖*ρ^(1-α)) := by ring
        _ ≤ C*(‖f‖*ρ^(1-α)) := mul_le_mul_of_nonneg_right h16AC (mul_nonneg (norm_nonneg f) hPower0)
        _ = _ := by ring
    have hSum : A*‖f‖+16*(A*‖f‖)*ρ^(1-α) ≤ 17*(A*‖f‖) := by
      have h := mul_le_mul_of_nonneg_left hPower1 (by positivity : 0 ≤ 16*(A*‖f‖))
      nlinarith only [h]
    have hPatchHigh : CG*(A*‖f‖+16*(A*‖f‖)*ρ^(1-α)) ≤ C*‖f‖ := by
      calc
        _ ≤ CG*(17*(A*‖f‖)) := mul_le_mul_of_nonneg_left hSum hCG.le
        _ = (17*CG*A)*‖f‖ := by ring
        _ ≤ C*‖f‖ := mul_le_mul_of_nonneg_right h17GC (norm_nonneg f)
    have hPatchLow : CG*(16*(A*‖f‖)*ρ^(1-α)) ≤ C*‖f‖*ρ^(1-α) := by
      calc
        _ = (16*CG*A)*(‖f‖*ρ^(1-α)) := by ring
        _ ≤ C*(‖f‖*ρ^(1-α)) := mul_le_mul_of_nonneg_right h16GC (mul_nonneg (norm_nonneg f) hPower0)
        _ = _ := by ring
    exact ⟨schauderBound_mono_const hVA hModelHigh,holderBound_mono_const hSmall hModelLow,hV0,
      schauderBound_mono_const hPatch.1 hPatchHigh,holderBound_mono_const hPatch.2.1 hPatchLow,
      hPatch.2.2.1,hPatch.2.2.2.1,hPatch.2.2.2.2⟩

end Yau.LeafProofs.L16Aux
