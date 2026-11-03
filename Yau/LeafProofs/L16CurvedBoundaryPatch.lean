import Yau.LeafProofs.L16HalfSpaceHolderInverse
import Yau.LeafProofs.L16ChartCoefficientExtension
import Yau.LeafProofs.L16ChartCutoffSchauder
import Yau.LeafProofs.L16BoundaryChartSource

open MeasureTheory Filter Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates
local instance curvedBoundaryPatch_dualGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance curvedBoundaryPatch_dualSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance
local instance curvedBoundaryPatch_hessianGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance
local instance curvedBoundaryPatch_hessianSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance

/-- The literal physical cutoff of the actual model solution. -/
def curvedBoundaryPatch {n : ℕ} (c : OpenPartialHomeomorph (Space n) (Space n))
    (φ : Space n → ℝ) (v : Point n → ℝ) : Point n → ℝ :=
  fun p => φ p.1*v (c p.1,p.2)

/-- Only the artificial chart edges of the actual pulled source are cut off. -/
def curvedBoundaryPatchSource {n : ℕ} (c : OpenPartialHomeomorph (Space n) (Space n))
    (q : ℝ) (hq : 0 < q) (ψ : Space n → ℝ) (g : Point n → ℝ) : Point n → ℝ :=
  fun p => innerPatchBump q hq 0 p.1*(ψ (c.symm p.1)*g (c.symm p.1,p.2))

/-- The true model drift already contains both physical drift and chart
curvature. Its physical error is exactly the cutoff commutator. -/
theorem curvedBoundaryPatch_operator {n : ℕ} {O : Set (Space n)} {e : Space n} {T : ℝ}
    (c : OpenPartialHomeomorph (Space n) (Space n)) (hc : ContDiffOn ℝ 3 c c.source)
    {q : ℝ} (hq : 0 < q) (φ ψ : Space n → ℝ) (hφ : ContDiff ℝ 2 φ)
    (hSupport : tsupport φ ⊆ c.source)
    (hImage : MapsTo c (tsupport φ) (Metric.closedBall 0 q))
    (hFaces : ∀ x ∈ c.source, x ∈ closure O ↔ 0 ≤ inner ℝ e (c x))
    (hPlateau : ∀ x, φ x*ψ x = ψ x)
    (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ) (g v : Point n → ℝ)
    (hv : C2 (cylinder univ 0 T) v)
    (hPDE : ∀ p ∈ cylinder {y | 0 ≤ inner ℝ e y} 0 T,
      linearOp (cylinder {y | 0 ≤ inner ℝ e y} 0 T)
        (chartPrincipalCutoffExtension c a q hq) (chartDriftCutoffExtension c a b q hq) v p =
          curvedBoundaryPatchSource c q hq ψ g p) :
    ∀ p ∈ cylinder (closure O) 0 T,
      linearOp (cylinder (closure O) 0 T) a b (curvedBoundaryPatch c φ v) p =
        ψ p.1*g p-spatialCutoffCommutator a b φ (chartSpaceTimePullback c v) p := by
  intro p hp
  by_cases hx : p.1 ∈ tsupport φ
  · have hxC : p.1 ∈ c.source := hSupport hx
    have hyH : 0 ≤ inner ℝ e (c p.1) := (hFaces p.1 hxC).mp hp.1
    have hη : innerPatchBump q hq 0 (c p.1) = 1 := innerPatchBump_eq_one hq (by
      simpa only [Metric.mem_closedBall,dist_zero_right,sub_zero] using hImage hx)
    have hVAt : ContDiffAt ℝ 2 (fun y => v (y,p.2)) (c p.1) :=
      hv.2.2.2.2.1 (c p.1,p.2) ⟨mem_univ _,hp.2⟩
    have hCAt : ContDiffAt ℝ 2 c p.1 := (hc.contDiffAt (c.open_source.mem_nhds hxC)).of_le (by norm_num)
    have hModel : linearOp (cylinder {y | 0 ≤ inner ℝ e y} 0 T)
        (chartTransformedPrincipal c a) (chartTransformedDrift c a b) v (c p.1,p.2) = ψ p.1*g p := by
      have h := hPDE (c p.1,p.2) ⟨hyH,hp.2⟩
      simpa only [linearOp,chartPrincipalCutoffExtension,chartDriftCutoffExtension,
        curvedBoundaryPatchSource,hη,c.left_inv hxC,one_smul,sub_self,zero_smul,add_zero,
        one_mul,Prod.eta] using h
    have hPhysical : linearOp (cylinder (closure O) 0 T) a b (chartSpaceTimePullback c v) p = ψ p.1*g p := by
      rw [linearOp_actual_chart_coefficients (S := {y | 0 ≤ inner ℝ e y}) c a b hp.1 hxC hyH hCAt hVAt]
      exact hModel
    have hPullAt : ContDiffAt ℝ 2 (fun x => chartSpaceTimePullback c v (x,p.2)) p.1 :=
      hVAt.comp p.1 hCAt
    have h := linearOp_spatial_mul (Q := cylinder (closure O) 0 T) (a := a) (b := b)
      (u := chartSpaceTimePullback c v) hφ.contDiffAt hPullAt
    rw [hPhysical] at h
    change linearOp (cylinder (closure O) 0 T) a b
      (fun p => φ p.1*chartSpaceTimePullback c v p) p = _
    rw [h]
    dsimp only [spatialCutoffCommutator]
    rw [←mul_assoc,hPlateau]
    ring
  · have hZero := spatial_cutoff_jets_zero_of_notMem_tsupport (cylinder (closure O) 0 T)
      φ (chartSpaceTimePullback c v) hx
    have hφ0 := image_eq_zero_of_notMem_tsupport hx
    have hψ0 : ψ p.1 = 0 := by
      have h := hPlateau p.1
      rw [hφ0,zero_mul] at h
      exact h.symm
    have hDφ := fderiv_of_notMem_tsupport (𝕜 := ℝ) hx
    have hDDφ := fderiv_of_notMem_tsupport (𝕜 := ℝ)
      (show p.1 ∉ tsupport (fderiv ℝ φ) from fun h => hx (tsupport_fderiv_subset ℝ h))
    change linearOp (cylinder (closure O) 0 T) a b
      (fun p => φ p.1*chartSpaceTimePullback c v p) p = _
    simp only [linearOp,hZero.2.1,hZero.2.2.1,hZero.2.2.2,hψ0,
      spatialCutoffCommutator,hDφ,hDDφ,zero_apply,zero_mul,mul_zero,
      Finset.sum_const_zero,add_zero,sub_zero]

/-- Any actual model solution gives a genuine ambient physical patch. The
geometric constant precedes time, coefficients, data and the chosen solution;
the lower Holder budget retains its independent small input. -/
theorem curvedBoundaryPatch_transport {n : ℕ} {O : Set (Space n)} {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (z : Space n) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (e : Space n) (c : OpenPartialHomeomorph (Space n) (Space n)) {q : ℝ} (hq : 0 < q)
    (hSource : Metric.closedBall z (4*r) ⊆ c.source)
    (hImage : MapsTo c (Metric.closedBall z (4*r)) (Metric.ball 0 (q/2)))
    (hc : ContDiffOn ℝ 3 c c.source)
    (hFaces : ∀ x ∈ c.source, (x ∈ closure O ↔ 0 ≤ inner ℝ e (c x)) ∧
      (x ∈ frontier O ↔ inner ℝ e (c x) = 0)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ψ : Space n → ℝ),
      (∀ x, outerPatchBump r hr z x*ψ x = ψ x) →
      ∀ (T K L : ℝ) (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ) (g v : Point n → ℝ),
      T ≤ 1 → SchauderBound α (cylinder univ 0 T) v K →
      HolderBound α (cylinder univ 0 T) (fun p => (v p,spatialD v p)) L →
      (∀ x, v (x,0) = 0) →
      (∀ y, inner ℝ e y = 0 → ∀ t ∈ Icc 0 T, v (y,t) = 0) →
      (∀ p ∈ cylinder {y | 0 ≤ inner ℝ e y} 0 T,
        linearOp (cylinder {y | 0 ≤ inner ℝ e y} 0 T)
          (chartPrincipalCutoffExtension c a q hq) (chartDriftCutoffExtension c a b q hq) v p =
            curvedBoundaryPatchSource c q hq ψ g p) →
      let w := curvedBoundaryPatch c (outerPatchBump r hr z) v
      SchauderBound α (cylinder univ 0 T) w (C*(K+L)) ∧
      HolderBound α (cylinder univ 0 T) (fun p => (w p,spatialD w p)) (C*L) ∧
      (∀ x, w (x,0) = 0) ∧
      (∀ x ∈ frontier O, ∀ t ∈ Icc 0 T, w (x,t) = 0) ∧
      ∀ p ∈ cylinder (closure O) 0 T,
        linearOp (cylinder (closure O) 0 T) a b w p = ψ p.1*g p-
          spatialCutoffCommutator a b (outerPatchBump r hr z) (chartSpaceTimePullback c v) p := by
  let φ : Space n → ℝ := outerPatchBump r hr z
  let S : Set (Space n) := Metric.ball z (3*r)
  let Kp : Set (Space n) := Metric.closedBall z (4*r)
  have hSupport : tsupport φ ⊆ S := by
    dsimp only [φ,S]
    rw [(outerPatchBump r hr z).tsupport_eq]
    exact Metric.closedBall_subset_ball (by linarith : 2*r < 3*r)
  have hSK : S ⊆ Kp := Metric.ball_subset_closedBall.trans
    (Metric.closedBall_subset_closedBall (by linarith : 3*r ≤ 4*r))
  have hφ : ContDiff ℝ 2 φ := (outerPatchBump r hr z).contDiff
  obtain ⟨J,hJ,hJets⟩ := patchBumps_uniform_three_holderBounds (n := n) hα hα1
  let E0 := cutoffJetBudget α J r 0
  let E1 := cutoffJetBudget α J r 1
  let E2 := cutoffJetBudget α J r 2
  let E := 1+E0+E1+E2
  have hE0 : 0 ≤ E0 := by dsimp only [E0,cutoffJetBudget]; positivity
  have hE1 : 0 ≤ E1 := by dsimp only [E1,cutoffJetBudget]; positivity
  have hE2 : 0 ≤ E2 := by dsimp only [E2,cutoffJetBudget]; positivity
  have hE0' : E0 ≤ E := by dsimp only [E]; linarith
  have hE1' : E1 ≤ E := by dsimp only [E]; linarith
  have hE2' : E2 ≤ E := by dsimp only [E]; linarith
  have hJet := hJets r hr hr1 1 z φ (Or.inr rfl)
  have hφ0 : HolderBound α (cylinder univ 0 1) (fun p => φ p.1) E := by
    apply holderBound_mono_const hJet.1
    simpa only [E0,cutoffJetBudget,Nat.zero_add,pow_one] using hE0'
  have hφ1 : HolderBound α (cylinder univ 0 1) (fun p => fderiv ℝ φ p.1) E := by
    exact holderBound_mono_const hJet.2.1 hE1'
  have hφ2 : HolderBound α (cylinder univ 0 1) (fun p => fderiv ℝ (fderiv ℝ φ) p.1) E := by
    exact holderBound_mono_const hJet.2.2 hE2'
  obtain ⟨C,hC,hChart⟩ := compact_chart_cutoff_full_schauder hα hα1 c.open_source
    (isCompact_closedBall z (4*r)) (convex_closedBall z (4*r)) hSource
    (Metric.isOpen_ball) hSK hc hφ hSupport hφ0 hφ1 hφ2
  refine ⟨C,hC,?_⟩
  intro ψ hPlateau T K L a b g v hT1 hv hvLow hv0 hvB hvPDE
  have hReg := hChart T K L v hT1 hv hvLow
  have hSupportC : tsupport φ ⊆ c.source := hSupport.trans (hSK.trans hSource)
  refine ⟨hReg.1,hReg.2,fun x => chart_cutoff_initial_zero φ c hv0 x,?_,?_⟩
  · exact chart_cutoff_lateral_zero c hSupportC (fun x hx hxF => (hFaces x hx).2.mp hxF) hvB
  · apply curvedBoundaryPatch_operator c hc hq φ ψ hφ hSupportC _
      (fun x hx => (hFaces x hx).1) hPlateau a b g v hv.1 hvPDE
    intro x hx
    exact Metric.ball_subset_closedBall ((Metric.ball_subset_ball (by linarith : q/2 ≤ q))
      (hImage ((hSupport.trans hSK) hx)))


/-- An actual uniformly controlled curved boundary patch. Both constants
precede coefficients, the forcing, the secant scale and the time horizon.
Only the original first corner compatibility is imposed. -/
theorem curvedBoundaryPatch_exists_uniform_short {n : ℕ} {O : Set (Space n)}
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
      ∀ (ρ T : ℝ) (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ)
        (g : Point n → ℝ) (F : ℝ),
      0 < ρ → ρ ≤ 1 → 0 < T → T ≤ δ → T ≤ ρ^2 →
      Elliptic (cylinder (closure O) 0 T) a lam upper →
      HolderBound α (cylinder (closure O) 0 T) a M →
      (∀ i, HolderBound α (cylinder (closure O) 0 T) (fun p => b p i) M) →
      HolderBound α (cylinder (closure O) 0 T) g F →
      (∀ x ∈ frontier O, g (x,0) = 0) → ∃ v w : Point n → ℝ,
      w = curvedBoundaryPatch c (outerPatchBump r hr z) v ∧
      SchauderBound α (cylinder univ 0 T) v (C*F) ∧
      HolderBound α (cylinder univ 0 T) (fun p => (v p,spatialD v p)) (C*F*ρ^(1-α)) ∧
      (∀ y, v (y,0) = 0) ∧
      (∀ y, inner ℝ e y = 0 → ∀ t ∈ Icc 0 T, v (y,t) = 0) ∧
      (∀ p ∈ cylinder {y | 0 ≤ inner ℝ e y} 0 T,
        linearOp (cylinder {y | 0 ≤ inner ℝ e y} 0 T)
          (chartPrincipalCutoffExtension c a q hq) (chartDriftCutoffExtension c a b q hq) v p =
            curvedBoundaryPatchSource c q hq ψ g p) ∧
      SchauderBound α (cylinder univ 0 T) w (C*F) ∧
      HolderBound α (cylinder univ 0 T) (fun p => (w p,spatialD w p)) (C*F*ρ^(1-α)) ∧
      (∀ x, w (x,0) = 0) ∧
      (∀ x ∈ frontier O, ∀ t ∈ Icc 0 T, w (x,t) = 0) ∧
      ∀ p ∈ cylinder (closure O) 0 T,
        linearOp (cylinder (closure O) 0 T) a b w p = ψ p.1*g p-
          spatialCutoffCommutator a b (outerPatchBump r hr z) (chartSpaceTimePullback c v) p := by
  obtain ⟨D,J,hD,hJ,hCoefficients⟩ := boundary_chart_compact_coefficient_extension
    hα hα1 e c hc hci (fun x hx => (hFaces x hx).1) hq hTarget
  obtain ⟨CS,hCS,hSourceBound⟩ := boundary_chart_cutoff_source_holder hα hα1 e c hci hFaces hq hTarget
  obtain ⟨CG,hCG,hTransport⟩ := curvedBoundaryPatch_transport hα hα1 z hr hr1 e c hq
    hSource hImage hc hFaces
  let H : Set (Space n) := {y | 0 ≤ inner ℝ e y}
  let Core := H∩Metric.closedBall (0 : Space n) (2*q)
  have hCore : IsCompact Core := (isCompact_closedBall 0 (2*q)).inter_left
    (isClosed_le continuous_const (innerSL ℝ e).continuous)
  obtain ⟨δ,C0,hδ,hδ1,hC0,hInverse⟩ := halfSpaceHolderInverse_exists_uniform_short
    (M := J*(M+1)) (lam := min (lam/D^2) 1) (upper := max (upper*D^2) 1)
    hα hα1 e he hCore inter_subset_left
  let A : ℝ := 1+C0*CS*(2*P)
  let C : ℝ := 1+17*A+17*CG*A
  have hA : 0 < A := by dsimp only [A]; positivity
  have hCGA : 0 ≤ CG*A := mul_nonneg hCG.le hA.le
  have hC : 0 < C := by dsimp only [C]; positivity
  have hAC : A ≤ C := by dsimp only [C]; nlinarith only [hA,hCGA]
  have h16AC : 16*A ≤ C := by dsimp only [C]; nlinarith only [hA,hCGA]
  have h17GC : 17*CG*A ≤ C := by dsimp only [C]; linarith only [hA]
  have h16GC : 16*CG*A ≤ C := by dsimp only [C]; nlinarith only [hA,hCGA]
  refine ⟨δ,C,hδ,hδ1,hC,?_⟩
  intro ρ T a b g F hρ hρ1 hT hTδ hTρ hEll ha hb hg hCorner
  have hT1 : T ≤ 1 := hTδ.trans hδ1
  have hF : 0 ≤ F := hg.1
  have hCoeff := hCoefficients T lam upper M a b hM hEll ha hb
  have hψT : HolderBound α (cylinder (closure O) 0 T) (fun p => ψ p.1) P :=
    holderBound_mono hψ (fun p hp => ⟨mem_univ _,hp.2.1,hp.2.2.trans hT1⟩)
  have hProduct := holderBound_mul hψT hg
  have hProductCorner : ∀ x ∈ frontier O, ψ x*g (x,0) = 0 := by
    intro x hx
    rw [hCorner x hx,mul_zero]
  have hModelSource := hSourceBound T (2*P*F) (fun p => ψ p.1*g p) hProduct hProductCorner
  obtain ⟨v,hV,hVLow,hV0,hVB,hVPDE⟩ := hInverse T
    (chartPrincipalCutoffExtension c a q hq) (chartDriftCutoffExtension c a b q hq)
    hT hTδ hCoeff.2.1 hCoeff.2.2.1 hCoeff.1
    (fun p hp hOut => (hCoeff.2.2.2.2 p hp hOut).1)
    (curvedBoundaryPatchSource c q hq ψ g) (CS*(2*P*F)) hModelSource.1 hModelSource.2
  have hModelBudget : C0*(CS*(2*P*F)) ≤ A*F := by
    dsimp only [A]
    nlinarith only [hF]
  have hVA := schauderBound_mono_const hV hModelBudget
  have hSmall := zero_initial_schauder_lowPair_small hα hα1 hT hρ hρ1 hTρ hVA hV0
  have hPatch := hTransport ψ hPlateau T (A*F) (16*(A*F)*ρ^(1-α)) a b g v
    hT1 hVA hSmall hV0 hVB hVPDE
  have hPower0 : 0 ≤ ρ^(1-α) := Real.rpow_nonneg hρ.le _
  have hPower1 : ρ^(1-α) ≤ 1 := Real.rpow_le_one hρ.le hρ1 (by linarith only [hα1])
  have hModelHigh : A*F ≤ C*F := mul_le_mul_of_nonneg_right hAC hF
  have hModelLow : 16*(A*F)*ρ^(1-α) ≤ C*F*ρ^(1-α) := by
    calc
      _ = (16*A)*(F*ρ^(1-α)) := by ring
      _ ≤ C*(F*ρ^(1-α)) := mul_le_mul_of_nonneg_right h16AC (mul_nonneg hF hPower0)
      _ = _ := by ring
  have hSum : A*F+16*(A*F)*ρ^(1-α) ≤ 17*(A*F) := by
    have h := mul_le_mul_of_nonneg_left hPower1 (by positivity : 0 ≤ 16*(A*F))
    nlinarith only [h]
  have hPatchHigh : CG*(A*F+16*(A*F)*ρ^(1-α)) ≤ C*F := by
    calc
      _ ≤ CG*(17*(A*F)) := mul_le_mul_of_nonneg_left hSum hCG.le
      _ = (17*CG*A)*F := by ring
      _ ≤ C*F := mul_le_mul_of_nonneg_right h17GC hF
  have hPatchLow : CG*(16*(A*F)*ρ^(1-α)) ≤ C*F*ρ^(1-α) := by
    calc
      _ = (16*CG*A)*(F*ρ^(1-α)) := by ring
      _ ≤ C*(F*ρ^(1-α)) := mul_le_mul_of_nonneg_right h16GC (mul_nonneg hF hPower0)
      _ = _ := by ring
  exact ⟨v,curvedBoundaryPatch c (outerPatchBump r hr z) v,rfl,
    schauderBound_mono_const hVA hModelHigh,holderBound_mono_const hSmall hModelLow,
    hV0,hVB,hVPDE,schauderBound_mono_const hPatch.1 hPatchHigh,
    holderBound_mono_const hPatch.2.1 hPatchLow,hPatch.2.2.1,hPatch.2.2.2.1,hPatch.2.2.2.2⟩

end Yau.LeafProofs.L16Aux
