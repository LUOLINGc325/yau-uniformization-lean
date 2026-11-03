import Yau.LeafProofs.L16CurvedBoundaryPatch
import Yau.LeafProofs.L16HalfSpaceLinearFactory
import Yau.LeafProofs.L16PatchSourceOperators

open MeasureTheory Filter Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates
local instance curvedLinearFactory_group {n : ℕ} (α : ℝ) (O : Set (Space n)) (T : ℝ) :
    NormedAddCommGroup (compatibleHolderGraph α O T) := inferInstance
local instance curvedLinearFactory_space {n : ℕ} (α : ℝ) (O : Set (Space n)) (T : ℝ) :
    NormedSpace ℝ (compatibleHolderGraph α O T) := inferInstance

/-- The actual model source CLM, actual linear half-space inverse and actual
curved-patch transport give a genuine source-linear physical patch factory.
All constants precede coefficients, time, interpolation scale and forcing. -/
theorem curvedBoundaryPatch_linear_factory_uniform_short {n : ℕ} {O : Set (Space n)}
    {α M lam upper P : ℝ} (hα : 0 < α) (hα1 : α < 1) (hM : 0 ≤ M) (hP : 0 ≤ P)
    (z : Space n) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (e : Space n) (he : ‖e‖ = 1) (c : OpenPartialHomeomorph (Space n) (Space n))
    {q : ℝ} (hq : 0 < q) (hSource : Metric.closedBall z (4*r) ⊆ c.source)
    (hImage : MapsTo c (Metric.closedBall z (4*r)) (Metric.ball 0 (q/2)))
    (hTarget : Metric.closedBall (0 : Space n) (4*q) ⊆ c.target)
    (hc : ContDiffOn ℝ 3 c c.source) (hci : ContDiffOn ℝ 3 c.symm c.target)
    (hFaces : ∀ x ∈ c.source, (x ∈ closure O ↔ 0 ≤ inner ℝ e (c x)) ∧
      (x ∈ frontier O ↔ inner ℝ e (c x) = 0))
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
          let w := curvedBoundaryPatch c (outerPatchBump r hr z) v
          SchauderBound α (cylinder univ 0 T) v (C*‖f‖) ∧
          HolderBound α (cylinder univ 0 T) (fun p => (v p,spatialD v p)) (C*‖f‖*ρ^(1-α)) ∧
          (∀ y, v (y,0) = 0) ∧
          SchauderBound α (cylinder univ 0 T) w (C*‖f‖) ∧
          HolderBound α (cylinder univ 0 T) (fun p => (w p,spatialD w p)) (C*‖f‖*ρ^(1-α)) ∧
          (∀ x, w (x,0) = 0) ∧
          (∀ x ∈ frontier O, ∀ t ∈ Icc 0 T, w (x,t) = 0) ∧
          ∀ p ∈ cylinder (closure O) 0 T,
            linearOp (cylinder (closure O) 0 T) a b w p = ψ p.1*compatibleHolderFun f p-
              spatialCutoffCommutator a b (outerPatchBump r hr z) (chartSpaceTimePullback c v) p := by
  obtain ⟨D,J,hD,hJ,hCoefficients⟩ := boundary_chart_compact_coefficient_extension
    hα hα1 e c hc hci (fun x hx => (hFaces x hx).1) hq hTarget
  obtain ⟨CS,hCS,hSourceMap⟩ := boundary_patch_source_operator hα hα1 e he c hci hFaces hq hTarget
  obtain ⟨CG,hCG,hTransport⟩ := curvedBoundaryPatch_transport hα hα1 z hr hr1 e c hq
    hSource hImage hc hFaces
  let H : Set (Space n) := {y | 0 ≤ inner ℝ e y}
  let Core := H∩Metric.closedBall (0 : Space n) (2*q)
  have hCore : IsCompact Core := (isCompact_closedBall 0 (2*q)).inter_left
    (isClosed_le continuous_const (innerSL ℝ e).continuous)
  obtain ⟨δ,C0,hδ,hδ1,hC0,hInverse⟩ := halfSpaceHolderInverse_linear_exists_uniform_short
    (M := J*(M+1)) (lam := min (lam/D^2) 1) (upper := max (upper*D^2) 1)
    hα hα1 e he hCore inter_subset_left
  let A : ℝ := 1+C0*CS*P
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
  have hCoeff := hCoefficients T lam upper M a b hM hEll ha hb
  have hψT : HolderBound α (cylinder univ 0 T) (fun p => ψ p.1) P :=
    holderBound_mono hψ (cylinder_mono_time hT1)
  obtain ⟨L,hL,hLEq⟩ := hSourceMap T P ψ hT.le hψT
  obtain ⟨U,hUAdd,hUSmul,hU⟩ := hInverse T
    (chartPrincipalCutoffExtension c a q hq) (chartDriftCutoffExtension c a b q hq)
    hT hTδ hCoeff.2.1 hCoeff.2.2.1 hCoeff.1
    (fun p hp hOut => (hCoeff.2.2.2.2 p hp hOut).1)
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
    obtain ⟨hV,hVLow,hV0,hVB,hVPDE0⟩ := hU (L f)
    have hVPDE : ∀ p ∈ cylinder H 0 T,
        linearOp (cylinder H 0 T) (chartPrincipalCutoffExtension c a q hq)
          (chartDriftCutoffExtension c a b q hq) v p =
            curvedBoundaryPatchSource c q hq ψ (compatibleHolderFun f) p := by
      intro p hp
      exact (hVPDE0 p hp).trans (hLEq f hp)
    have hModelBudget : C0*‖L f‖ ≤ A*‖f‖ := by
      have hLf : ‖L f‖ ≤ (CS*P)*‖f‖ := (L.le_opNorm f).trans
        (mul_le_mul_of_nonneg_right hL (norm_nonneg f))
      calc
        _ ≤ C0*((CS*P)*‖f‖) := mul_le_mul_of_nonneg_left hLf hC0.le
        _ ≤ A*‖f‖ := by dsimp only [A]; nlinarith only [norm_nonneg f]
    have hVA := schauderBound_mono_const hV hModelBudget
    have hSmall := zero_initial_schauder_lowPair_small hα hα1 hT hρ hρ1 hTρ hVA hV0
    have hPatch := hTransport ψ hPlateau T (A*‖f‖) (16*(A*‖f‖)*ρ^(1-α))
      a b (compatibleHolderFun f) v hT1 hVA hSmall hV0 hVB hVPDE
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
