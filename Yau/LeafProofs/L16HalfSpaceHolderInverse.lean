import Yau.LeafProofs.L16HalfSpaceFiniteParametrix
import Yau.LeafProofs.L16HalfSpaceResidualRates
import Yau.LeafProofs.L16CompatibleHolderGraph
import Yau.LeafProofs.L16EllipticLocalizationOn
import Yau.LeafProofs.L16DefiningFlattening

open MeasureTheory Filter Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

local instance halfSpaceHolderInverse_dualGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance halfSpaceHolderInverse_dualSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance
local instance halfSpaceHolderInverse_hessianGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance
local instance halfSpaceHolderInverse_hessianSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance

/-- The actual finite half-space kernels on the separated spatial partition,
including the genuine exterior patch. -/
def localizedHalfSpaceParametrix {n : ℕ} (s : Finset (Space n)) {r : ℝ} (hr : 0 < r)
    (B : Space n → Space n ≃L[ℝ] Space n) (Bext : Space n ≃L[ℝ] Space n)
    (e : Space n) (T : ℝ) (f : Point n → ℝ) : Point n → ℝ :=
  halfSpaceFiniteParametrix (localizationIndices s) (localizationEquiv B Bext) e T
    (localizationOuter s hr) (localizationSource s hr) f

/-- Actual ambient regularity and both zero data faces for the partitioned
half-space parametrix, using forcing compatibility only on the initial plane. -/
theorem halfSpaceHolderInverse_data {n : ℕ} {α T F : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1)
    (s : Finset (Space n)) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hSep : ∀ c ∈ s, ∀ d ∈ s, c ≠ d → r ≤ ‖c-d‖)
    (B : Space n → Space n ≃L[ℝ] Space n) (Bext : Space n ≃L[ℝ] Space n)
    (a : Point n → Mat n) (hGram : localizationGramIdentity s B Bext a)
    (e : Space n) (he : ‖e‖ = 1) {f : Point n → ℝ}
    (hf : HolderBound α (cylinder {x | 0 ≤ inner ℝ e x} 0 T) f F)
    (hCorner : ∀ x, inner ℝ e x = 0 → f (x,0) = 0) :
    C2 (cylinder univ 0 T) (localizedHalfSpaceParametrix s hr B Bext e T f) ∧
    (∀ x, localizedHalfSpaceParametrix s hr B Bext e T f (x,0) = 0) ∧
    ∀ x, inner ℝ e x = 0 → ∀ t ∈ Icc 0 T,
      localizedHalfSpaceParametrix s hr B Bext e T f (x,t) = 0 := by
  obtain ⟨P,hP,hSource⟩ := localizationSource_holderBound (n := n) hα hα1
  exact halfSpaceFiniteParametrix_data _ _ (localizationFrozenMatrix a) he _ _ hα hα1 hT hT1
    (fun i _ => localizationOuter_contDiff s hr i)
    (fun i _ => holderBound_mono (hSource s r hr hr1 hSep T i)
      (fun _ hp => ⟨mem_univ _,hp.2⟩)) hf hCorner hGram

/-- The literal operator residual agrees with the already estimated actual
localized residual. The global partition identity cancels the uncovered term. -/
theorem halfSpaceHolderInverse_residual_eq {n : ℕ} {α T F : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1)
    (s : Finset (Space n)) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hSep : ∀ c ∈ s, ∀ d ∈ s, c ≠ d → r ≤ ‖c-d‖)
    (B : Space n → Space n ≃L[ℝ] Space n) (Bext : Space n ≃L[ℝ] Space n)
    (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ)
    (hGram : localizationGramIdentity s B Bext a) (e : Space n) (he : ‖e‖ = 1)
    {f : Point n → ℝ} (hf : HolderBound α (cylinder {x | 0 ≤ inner ℝ e x} 0 T) f F)
    (hCorner : ∀ x, inner ℝ e x = 0 → f (x,0) = 0)
    {p : Point n} (hp : p ∈ cylinder {x | 0 ≤ inner ℝ e x} 0 T) :
    halfSpaceFiniteResidual T (localizationIndices s) (localizationEquiv B Bext) e
      (localizationOuter s hr) (localizationSource s hr) a b f p =
      localizedHalfSpaceResidual T s r hr B Bext e a b f p := by
  obtain ⟨P,hP,hSource⟩ := localizationSource_holderBound (n := n) hα hα1
  have hPartition : (∑ i ∈ localizationIndices s,
      localizationOuter s hr i p.1*localizationSource s hr i p.1) = 1 := by
    rw [localizationIndices_sum]
    exact patchCutoffs_partition s hr p.1
  rw [halfSpaceFiniteResidual_eq _ _ (localizationFrozenMatrix a) he _ _ a b hα hα1 hT hT1
    (fun i _ => localizationOuter_contDiff s hr i)
    (fun i _ => holderBound_mono (hSource s r hr hr1 hSep T i)
      (fun _ hq => ⟨mem_univ _,hq.2⟩)) hf hCorner hGram hp,
    hPartition,sub_self,zero_mul,zero_add,localizationIndices_sum]
  rfl

theorem halfSpaceHolderInverse_uniform_full_regularity {n : ℕ} {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (N : ℝ) (hN0 : 0 ≤ N) (s : Finset (Space n)) {r : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hSep : ∀ c ∈ s, ∀ d ∈ s, c ≠ d → r ≤ ‖c-d‖)
    :
    ∃ C : ℝ, 0 < C ∧
      ∀ (B : Space n → Space n ≃L[ℝ] Space n) (Bext : Space n ≃L[ℝ] Space n),
      (∀ c, constantHeatNormFactor α (B c) ≤ N) →
      constantHeatNormFactor α Bext ≤ N →
      ∀ a : Point n → Mat n, localizationGramIdentity s B Bext a →
      ∀ e : Space n, ‖e‖ = 1 → ∀ T F : ℝ, 0 < T → T ≤ 1 → ∀ f : Point n → ℝ,
      HolderBound α (cylinder {x | 0 ≤ inner ℝ e x} 0 T) f F →
      (∀ x, inner ℝ e x = 0 → f (x,0) = 0) →
      SchauderBound α (cylinder Set.univ 0 T) (localizedHalfSpaceParametrix s hr B Bext e T f) (C*F) ∧
      HolderBound α (cylinder Set.univ 0 T)
        (fun p => (localizedHalfSpaceParametrix s hr B Bext e T f p,
          spatialD (localizedHalfSpaceParametrix s hr B Bext e T f) p)) (C*F) := by
  obtain ⟨Cφ,hCφ,hCut⟩ := patchBumps_uniform_three_holderBounds (n := n) hα hα1
  obtain ⟨E0,E1,E2,hE0,hE1,hE2,hExt0,hExt1,hExt2⟩ := exteriorCutoff_holder_jets hα hα1 s hr
  obtain ⟨P,hP,hSource⟩ := localizationSource_holderBound (n := n) hα hα1
  let I0 := cutoffJetBudget α Cφ r 0
  let I1 := cutoffJetBudget α Cφ r 1
  let I2 := cutoffJetBudget α Cφ r 2
  have hI0 : 0 ≤ I0 := by dsimp only [I0,cutoffJetBudget]; positivity
  have hI1 : 0 ≤ I1 := by dsimp only [I1,cutoffJetBudget]; positivity
  have hI2 : 0 ≤ I2 := by dsimp only [I2,cutoffJetBudget]; positivity
  let E : ℝ := 1+I0+I1+I2+E0+E1+E2
  have hE : 0 < E := by dsimp only [E]; linarith
  have hIE0 : I0 ≤ E := by dsimp only [E]; linarith
  have hIE1 : I1 ≤ E := by dsimp only [E]; linarith
  have hIE2 : I2 ≤ E := by dsimp only [E]; linarith
  have hEE0 : E0 ≤ E := by dsimp only [E]; linarith
  have hEE1 : E1 ≤ E := by dsimp only [E]; linarith
  have hEE2 : E2 ≤ E := by dsimp only [E]; linarith
  have hφ0 (i : Option (Space n)) : HolderBound α (cylinder Set.univ 0 1)
      (fun p => localizationOuter s hr i p.1) E := by
    cases i with
    | none => exact holderBound_mono_const hExt0 hEE0
    | some c =>
      have h := (hCut r hr hr1 1 c _ (Or.inr rfl)).1
      apply holderBound_mono_const h
      simpa only [I0,cutoffJetBudget,Nat.zero_add,pow_one] using hIE0
  have hφ1 (i : Option (Space n)) : HolderBound α (cylinder Set.univ 0 1)
      (fun p => fderiv ℝ (localizationOuter s hr i) p.1) E := by
    cases i with
    | none => exact holderBound_mono_const hExt1 hEE1
    | some c =>
      exact holderBound_mono_const (hCut r hr hr1 1 c _ (Or.inr rfl)).2.1 hIE1
  have hφ2 (i : Option (Space n)) : HolderBound α (cylinder Set.univ 0 1)
      (fun p => fderiv ℝ (fderiv ℝ (localizationOuter s hr i)) p.1) E := by
    cases i with
    | none => exact holderBound_mono_const hExt2 hEE2
    | some c =>
      exact holderBound_mono_const (hCut r hr hr1 1 c _ (Or.inr rfl)).2.2 hIE2
  have hPS : 0 < P*r⁻¹*r^(1-α) := by positivity
  obtain ⟨C,hC,hUniform⟩ := halfSpaceFiniteParametrix_uniform_full_regularity
    (N := N) hα hα1 hN0 (localizationIndices s)
    (localizationOuter s hr) (localizationSource s hr) hE hPS
    (fun i _ => localizationOuter_contDiff s hr i) (fun i _ => hφ0 i)
    (fun i _ => hφ1 i) (fun i _ => hφ2 i)
  refine ⟨C,hC,?_⟩
  intro B Bext hB hBext a hGram e he T F hT hT1 f hf hCorner
  have hFactor : ∀ i ∈ localizationIndices s,
      constantHeatNormFactor α (localizationEquiv B Bext i) ≤ N := by
    intro i _
    cases i with
    | none => exact hBext
    | some c => exact hB c
  exact hUniform (localizationEquiv B Bext) hFactor (localizationFrozenMatrix a) hGram e he
    (fun i _ => holderBound_mono (hSource s r hr hr1 hSep 1 i)
      (fun _ hp => ⟨mem_univ _,hp.2⟩)) T F hT hT1 f hf hCorner


/-- The actual finite residual acts on the closed first-corner-compatible
source space; its proved two norms give an actual Neumann correction.
The bound hypotheses of this intermediate lemma are discharged below by the
proved half-space residual scales and actual finite-kernel regularity. -/
theorem halfSpaceHolderInverse_weighted {n : ℕ} {α T : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1)
    (s : Finset (Space n)) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hSep : ∀ c ∈ s, ∀ d ∈ s, c ≠ d → r ≤ ‖c-d‖)
    (B : Space n → Space n ≃L[ℝ] Space n) (Bext : Space n ≃L[ℝ] Space n)
    (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ)
    (hGram : localizationGramIdentity s B Bext a) (e : Space n) (he : ‖e‖ = 1)
    {β CP : ℝ} (hβ : 0 < β) (hCP : 0 < CP)
    (hWeighted : ∀ (f : Point n → ℝ) (F S : ℝ),
      HolderBound α (cylinder {x | 0 ≤ inner ℝ e x} 0 T) f F →
      (∀ x, inner ℝ e x = 0 → f (x,0) = 0) → 0 ≤ S → S ≤ F →
      (∀ p ∈ cylinder {x | 0 ≤ inner ℝ e x} 0 T, |f p| ≤ S) →
      HolderBound α (cylinder {x | 0 ≤ inner ℝ e x} 0 T)
        (localizedHalfSpaceResidual T s r hr B Bext e a b f) (F/4+β*S/4) ∧
      (∀ p ∈ cylinder {x | 0 ≤ inner ℝ e x} 0 T,
        |localizedHalfSpaceResidual T s r hr B Bext e a b f p| ≤ F/(4*β)))
    (hParametrix : ∀ (f : Point n → ℝ) (F : ℝ),
      HolderBound α (cylinder {x | 0 ≤ inner ℝ e x} 0 T) f F →
      (∀ x, inner ℝ e x = 0 → f (x,0) = 0) →
      SchauderBound α (cylinder univ 0 T) (localizedHalfSpaceParametrix s hr B Bext e T f) (CP*F) ∧
      HolderBound α (cylinder univ 0 T)
        (fun p => (localizedHalfSpaceParametrix s hr B Bext e T f p,
          spatialD (localizedHalfSpaceParametrix s hr B Bext e T f) p)) (CP*F)) :
    ∀ (f : Point n → ℝ) (F : ℝ),
      HolderBound α (cylinder {x | 0 ≤ inner ℝ e x} 0 T) f F →
      (∀ x, inner ℝ e x = 0 → f (x,0) = 0) → ∃ u : Point n → ℝ,
      SchauderBound α (cylinder univ 0 T) u ((2*(1+β)*CP)*F) ∧
      HolderBound α (cylinder univ 0 T) (fun p => (u p,spatialD u p)) ((2*(1+β)*CP)*F) ∧
      (∀ x, u (x,0) = 0) ∧
      (∀ x, inner ℝ e x = 0 → ∀ t ∈ Icc 0 T, u (x,t) = 0) ∧
      ∀ p ∈ cylinder {x | 0 ≤ inner ℝ e x} 0 T,
        linearOp (cylinder {x | 0 ≤ inner ℝ e x} 0 T) a b u p = f p := by
  let O : Set (Space n) := {x | 0 < inner ℝ e x}
  let Q : Set (Point n) := cylinder {x | 0 ≤ inner ℝ e x} 0 T
  let E := compatibleHolderGraph α O T
  have hClosure : closure O = {x | 0 ≤ inner ℝ e x} := unitNormal_halfSpace_closure he
  have hFrontier : frontier O = {x | inner ℝ e x = 0} := unitNormal_halfSpace_frontier he
  have hFunctionBound (x : E) : HolderBound α Q (compatibleHolderFun x) ‖x‖ := by
    simpa only [hClosure] using compatibleHolderFun_holderBound x
  have hFunctionCorner (x : E) : ∀ y, inner ℝ e y = 0 → compatibleHolderFun x (y,0) = 0 := by
    intro y hy
    exact compatibleHolderFun_corner x (by rw [hFrontier]; exact hy)
  obtain ⟨P,hP,hSource⟩ := localizationSource_holderBound (n := n) hα hα1
  have hφ : ∀ i ∈ localizationIndices s, ContDiff ℝ 2 (localizationOuter s hr i) :=
    fun i _ => localizationOuter_contDiff s hr i
  have hψ : ∀ i ∈ localizationIndices s,
      HolderBound α Q (fun p => localizationSource s hr i p.1) (P*r⁻¹*r^(1-α)) :=
    fun i _ => holderBound_mono (hSource s r hr hr1 hSep T i) (fun _ hp => ⟨mem_univ _,hp.2⟩)
  let D : E → Point n → ℝ := fun x =>
    halfSpaceFiniteResidual T (localizationIndices s) (localizationEquiv B Bext) e
      (localizationOuter s hr) (localizationSource s hr) a b (compatibleHolderFun x)
  have hResidualEq (x : E) {p : Point n} (hp : p ∈ Q) :
      D x p = localizedHalfSpaceResidual T s r hr B Bext e a b (compatibleHolderFun x) p :=
    halfSpaceHolderInverse_residual_eq hα hα1 hT hT1 s hr hr1 hSep B Bext a b hGram e he
      (hFunctionBound x) (hFunctionCorner x) hp
  have hProjection (x : E) : ‖x.val.val.1‖ ≤ ‖x‖ := by
    change ‖x.val.val.1‖ ≤ max ‖x.val.val.1‖ ‖x.val.val.2‖
    exact le_max_left _ _
  have hGraphSup (x : E) (p : Point n) (hp : p ∈ Q) :
      |compatibleHolderFun x p| ≤ ‖x.val.val.1‖ := by
    have hpC : p ∈ cylinder (closure O) 0 T := by rw [hClosure]; exact hp
    rw [compatibleHolderFun,holderGraphFun_apply x.val ⟨p,hpC⟩]
    exact x.val.val.1.norm_coe_le_norm ⟨p,hpC⟩
  have hRefined (x : E) : HolderBound α Q (D x) (‖x‖/4+β*‖x.val.val.1‖/4) ∧
      (∀ p ∈ Q, |D x p| ≤ ‖x‖/(4*β)) := by
    have h := hWeighted (compatibleHolderFun x) ‖x‖ ‖x.val.val.1‖
      (hFunctionBound x) (hFunctionCorner x) (norm_nonneg _) (hProjection x) (hGraphSup x)
    refine ⟨holderBound_congr_on h.1 (fun p hp => (hResidualEq x hp).symm),?_⟩
    intro p hp
    rw [hResidualEq x hp]
    exact h.2 p hp
  have hBound (x : E) : HolderBound α (cylinder (closure O) 0 T) (D x) (((1+β)/4)*‖x‖) := by
    have hQ : HolderBound α Q (D x) (((1+β)/4)*‖x‖) := by
      apply holderBound_mono_const (hRefined x).1
      have h := mul_le_mul_of_nonneg_left (hProjection x) hβ.le
      nlinarith only [h]
    simpa only [hClosure] using hQ
  have hAdd (x y : E) (p : Point n) (hp : p ∈ cylinder (closure O) 0 T) :
      D (x+y) p = D x p+D y p := by
    dsimp only [D]
    rw [compatibleHolderFun_add]
    rw [hClosure] at hp
    exact halfSpaceFiniteResidual_add _ _ (localizationFrozenMatrix a) he _ _ a b
      hα hα1 hT hT1 hφ hψ (hFunctionBound x) (hFunctionBound y)
      (hFunctionCorner x) (hFunctionCorner y) hGram hp
  have hSmul (c : ℝ) (x : E) (p : Point n) (hp : p ∈ cylinder (closure O) 0 T) :
      D (c • x) p = c*D x p := by
    dsimp only [D]
    rw [compatibleHolderFun_smul]
    rw [hClosure] at hp
    exact halfSpaceFiniteResidual_smul _ _ (localizationFrozenMatrix a) he _ _ a b
      hα hα1 hT hT1 hφ hψ (hFunctionBound x) (hFunctionCorner x) hGram c hp
  have hCornerD (x : E) (y : Space n) (hy : y ∈ frontier O) : D x (y,0) = 0 := by
    rw [hFrontier] at hy
    exact halfSpaceFiniteResidual_corner _ _ (localizationFrozenMatrix a) he _ _ a b
      hα hα1 hT hT1 hφ hψ (hFunctionBound x) (hFunctionCorner x) hGram y hy
  let R : E →L[ℝ] E := compatibleHolderGraphLift hα hT.le D hBound hAdd hSmul hCornerD
  have hREq (x : E) : EqOn (compatibleHolderFun (R x)) (D x) Q := by
    have h := compatibleHolderGraphLift_eqOn hα hT.le D hBound hAdd hSmul hCornerD x
    simpa only [hClosure] using h
  have hStrong (x : E) : ‖R x‖ ≤ (1/4 : ℝ)*‖x‖+(β/4)*‖x.val.val.1‖ := by
    change ‖(R x).val‖ ≤ _
    apply holderGraph_norm_le_of_holderBound (R x).val
    have hQ : HolderBound α Q (compatibleHolderFun (R x))
        ((1/4:ℝ)*‖x‖+(β/4)*‖x.val.val.1‖) := by
      have h := holderBound_congr_on (hRefined x).1 (fun p hp => (hREq x hp).symm)
      convert h using 1; ring
    apply holderBound_mono hQ
    intro p hp
    exact ⟨by simpa only [hClosure] using hp.1,hp.2⟩
  have hSupR (x : E) : ‖(R x).val.val.1‖ ≤ (1/(4*β))*‖x‖ := by
    apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
    intro p
    change |D x p.val| ≤ _
    have hp : p.val ∈ Q := by simpa only [hClosure] using p.property
    convert (hRefined x).2 p.val hp using 1; ring
  have hεd : (1/4 : ℝ)+β*(1/(4*β)) ≤ (1/2 : ℝ) := by
    have hCancel : β*(1/(4*β)) = (1/4 : ℝ) := by field_simp [hβ.ne']
    rw [hCancel]
    norm_num
  have hAB : β/4 ≤ β/2 := by linarith only [hβ]
  intro f F hf hCorner
  have hfC : HolderBound α (cylinder (closure O) 0 T) f F := by rw [hClosure]; exact hf
  have hCornerC : ∀ x ∈ frontier O, f (x,0) = 0 := by
    intro x hx
    rw [hFrontier] at hx
    exact hCorner x hx
  let fH : E := compatibleHolderGraphOfBound hα hT.le hfC hCornerC
  have hFHEq : EqOn (compatibleHolderFun fH) f Q := by
    have h := compatibleHolderGraphOfBound_eqOn hα hT.le hfC hCornerC
    simpa only [hClosure] using h
  obtain ⟨g,hCorrect,hg⟩ := compatibleHolderGraph_residual_correction_of_two_bounds
    R hβ.le hεd hAB hStrong hSupR fH
  let u : Point n → ℝ := localizedHalfSpaceParametrix s hr B Bext e T (compatibleHolderFun g)
  have hBudget : CP*‖g‖ ≤ (2*(1+β)*CP)*F := by
    have hgf : ‖g‖ ≤ 2*(1+β)*F := hg.trans
      (mul_le_mul_of_nonneg_left (compatibleHolderGraphOfBound_norm_le hα hT.le hfC hCornerC) (by positivity))
    calc
      CP*‖g‖ ≤ CP*(2*(1+β)*F) := mul_le_mul_of_nonneg_left hgf hCP.le
      _ = _ := by ring
  have hU := hParametrix (compatibleHolderFun g) ‖g‖ (hFunctionBound g) (hFunctionCorner g)
  have hData := halfSpaceHolderInverse_data hα hα1 hT hT1 s hr hr1 hSep B Bext a hGram e he
    (hFunctionBound g) (hFunctionCorner g)
  refine ⟨u,schauderBound_mono_const hU.1 hBudget,holderBound_mono_const hU.2 hBudget,
    hData.2.1,hData.2.2,?_⟩
  intro p hp
  have hEval := congrArg (fun x : E => compatibleHolderFun x p) hCorrect
  rw [compatibleHolderFun_add,Pi.add_apply,hREq g hp,hFHEq hp] at hEval
  change linearOp Q a b (localizedHalfSpaceParametrix s hr B Bext e T (compatibleHolderFun g)) p = f p
  dsimp only [D,halfSpaceFiniteResidual] at hEval
  change compatibleHolderFun g p+
    (linearOp Q a b (localizedHalfSpaceParametrix s hr B Bext e T (compatibleHolderFun g)) p-
      compatibleHolderFun g p) = f p at hEval
  linarith only [hEval]

/-- Uniform short-time, zero-data half-space inverse for genuinely Holder
coefficients that equal the identity away from a fixed compact set. Both
constants precede every coefficient field and forcing, with only the first
initial-lateral compatibility condition. -/
theorem halfSpaceHolderInverse_exists_uniform_short {n : ℕ} {α M lam upper : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (e : Space n) (he : ‖e‖ = 1)
    {K : Set (Space n)} (hK : IsCompact K) (hKH : K ⊆ {x | 0 ≤ inner ℝ e x}) :
    ∃ δ C : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < C ∧
      ∀ (T : ℝ) (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ),
      0 < T → T ≤ δ → HolderBound α (cylinder {x | 0 ≤ inner ℝ e x} 0 T) a M →
      (∀ i, HolderBound α (cylinder {x | 0 ≤ inner ℝ e x} 0 T) (fun p => b p i) M) →
      Elliptic (cylinder {x | 0 ≤ inner ℝ e x} 0 T) a lam upper →
      (∀ p ∈ cylinder {x | 0 ≤ inner ℝ e x} 0 T, p.1 ∉ K → a p = 1) →
      ∀ (f : Point n → ℝ) (F : ℝ),
      HolderBound α (cylinder {x | 0 ≤ inner ℝ e x} 0 T) f F →
      (∀ x, inner ℝ e x = 0 → f (x,0) = 0) → ∃ u : Point n → ℝ,
      SchauderBound α (cylinder univ 0 T) u (C*F) ∧
      HolderBound α (cylinder univ 0 T) (fun p => (u p,spatialD u p)) (C*F) ∧
      (∀ x, u (x,0) = 0) ∧
      (∀ x, inner ℝ e x = 0 → ∀ t ∈ Icc 0 T, u (x,t) = 0) ∧
      ∀ p ∈ cylinder {x | 0 ≤ inner ℝ e x} 0 T,
        linearOp (cylinder {x | 0 ≤ inner ℝ e x} 0 T) a b u p = f p := by
  let N : ℝ := ellipticHeatNormBudget α lam upper
  have hN : 0 ≤ N := by dsimp only [N,ellipticHeatNormBudget]; positivity
  obtain ⟨r,hr,s,β,δ,hr1,hsK,hSep,hCover,hβ,hδ,hδ1,hWeighted⟩ :=
    exists_localizedHalfSpaceResidual_holder_only_weighted_bounds
      (n := n) (M := M) (N := N) hα hα1 hK e he hKH
  obtain ⟨CP,hCP,hParametrix⟩ :=
    halfSpaceHolderInverse_uniform_full_regularity hα hα1 N hN s hr hr1 hSep
  refine ⟨δ,2*(1+β)*CP,hδ,hδ1,by positivity,?_⟩
  intro T a b hT hTδ ha hb hEll hExterior
  have hH : ({x : Space n | 0 ≤ inner ℝ e x}).Nonempty := ⟨0,by simp⟩
  obtain ⟨B,hBN,hNid,hGram⟩ := elliptic_localization_equivs_on hα.le hT.le hH a hEll s
    (fun c hc => hKH (hsK c hc))
  exact halfSpaceHolderInverse_weighted hα hα1 hT (hTδ.trans hδ1) s hr hr1 hSep B
    (ContinuousLinearEquiv.refl ℝ (Space n)) a b hGram e he hβ hCP
    (fun f F S hf hCorner hS hSF hSup => hWeighted T a b B
      (ContinuousLinearEquiv.refl ℝ (Space n)) f F S hT hTδ ha hb hExterior hBN hNid
      (fun c hc => by
        have hcs : some c ∈ localizationIndices s := by simp [localizationIndices,hc]
        simpa only [localizationEquiv,localizationFrozenMatrix] using hGram (some c) hcs)
      (by
        have hNone : (none : Option (Space n)) ∈ localizationIndices s := by simp [localizationIndices]
        simpa only [localizationEquiv,localizationFrozenMatrix] using hGram none hNone)
      hf hCorner hS hSF hSup)
    (fun f F hf hCorner => hParametrix B (ContinuousLinearEquiv.refl ℝ (Space n)) hBN hNid a hGram e he
      T F hT (hTδ.trans hδ1) f hf hCorner)

end Yau.LeafProofs.L16Aux
