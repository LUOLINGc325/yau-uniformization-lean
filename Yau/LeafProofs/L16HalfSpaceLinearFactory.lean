import Yau.LeafProofs.L16HalfSpaceHolderInverse
import Yau.LeafProofs.L16CompatibleParametrixFactory

open MeasureTheory Filter Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

local instance halfSpaceLinearFactory_group {n : ℕ} (α : ℝ) (O : Set (Space n)) (T : ℝ) :
    NormedAddCommGroup (compatibleHolderGraph α O T) := inferInstance
local instance halfSpaceLinearFactory_space {n : ℕ} (α : ℝ) (O : Set (Space n)) (T : ℝ) :
    NormedSpace ℝ (compatibleHolderGraph α O T) := inferInstance

/-- The actual finite half-space kernels and actual residual estimates give
an actual source-linear inverse on the closed compatible source space. -/
theorem halfSpaceHolderInverse_linear_weighted {n : ℕ} {α T : ℝ}
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
    ∃ U : compatibleHolderGraph α {x | 0 < inner ℝ e x} T → Point n → ℝ,
      (∀ f g p, p ∈ cylinder univ 0 T → U (f+g) p = U f p+U g p) ∧
      (∀ (c : ℝ) f p, p ∈ cylinder univ 0 T → U (c • f) p = c*U f p) ∧
      ∀ f,
        SchauderBound α (cylinder univ 0 T) (U f) ((2*(1+β)*CP)*‖f‖) ∧
        HolderBound α (cylinder univ 0 T) (fun p => (U f p,spatialD (U f) p))
          ((2*(1+β)*CP)*‖f‖) ∧
        (∀ x, U f (x,0) = 0) ∧
        (∀ x, inner ℝ e x = 0 → ∀ t ∈ Icc 0 T, U f (x,t) = 0) ∧
        ∀ p ∈ cylinder {x | 0 ≤ inner ℝ e x} 0 T,
          linearOp (cylinder {x | 0 ≤ inner ℝ e x} 0 T) a b (U f) p = compatibleHolderFun f p := by
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
  let P0 : E → Point n → ℝ := fun f =>
    localizedHalfSpaceParametrix s hr B Bext e T (compatibleHolderFun f)
  have hP (f : E) := hParametrix (compatibleHolderFun f) ‖f‖
    (hFunctionBound f) (hFunctionCorner f)
  have hData (f : E) := halfSpaceHolderInverse_data hα hα1 hT hT1 s hr hr1 hSep
    B Bext a hGram e he (hFunctionBound f) (hFunctionCorner f)
  have hInitial (f : E) (x : Space n) : P0 f (x,0) = 0 := (hData f).2.1 x
  have hLateral (f : E) (x : Space n) (hx : x ∈ frontier O) :
      ∀ t ∈ Icc 0 T, P0 f (x,t) = 0 := by
    rw [hFrontier] at hx
    exact (hData f).2.2 x hx
  have hPAdd (f g : E) (p : Point n) (hp : p ∈ cylinder univ 0 T) :
      P0 (f+g) p = P0 f p+P0 g p := by
    dsimp only [P0,localizedHalfSpaceParametrix]
    rw [compatibleHolderFun_add]
    exact halfSpaceFiniteParametrix_add _ _ he _ _ hα hT.le hψ
      (hFunctionBound f) (hFunctionBound g) hp.2
  have hPSmul (c : ℝ) (f : E) (p : Point n) (_hp : p ∈ cylinder univ 0 T) :
      P0 (c • f) p = c*P0 f p := by
    dsimp only [P0,localizedHalfSpaceParametrix]
    rw [compatibleHolderFun_smul]
    exact halfSpaceFiniteParametrix_smul _ _ e T c _ _ _ p
  have hOperator (f : E) (p : Point n) (_hp : p ∈ cylinder (closure O) 0 T) :
      linearOp (cylinder (closure O) 0 T) a b (P0 f) p = compatibleHolderFun f p+D f p := by
    rw [hClosure]
    dsimp only [P0,localizedHalfSpaceParametrix,D,halfSpaceFiniteResidual]
    ring
  have hRefinedC (f : E) :
      HolderBound α (cylinder (closure O) 0 T) (D f) (‖f‖/4+β*‖f.val.val.1‖/4) ∧
      ∀ p ∈ cylinder (closure O) 0 T, |D f p| ≤ ‖f‖/(4*β) := by
    simpa only [hClosure] using hRefined f
  obtain ⟨U,hUAdd,hUSmul,hU⟩ := compatibleParametrix_linear_inverse hα hT.le hβ hCP a b
    P0 D hP hInitial hLateral hPAdd hPSmul hOperator hAdd hSmul hCornerD hRefinedC
  refine ⟨U,hUAdd,hUSmul,?_⟩
  intro f
  simpa only [hClosure,hFrontier,Set.mem_ofPred_eq] using hU f

/-- Uniform source-linear factory with only the original Holder, ellipticity
and compact-perturbation hypotheses. The constants precede every coefficient. -/
theorem halfSpaceHolderInverse_linear_exists_uniform_short {n : ℕ} {α M lam upper : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (e : Space n) (he : ‖e‖ = 1)
    {K : Set (Space n)} (hK : IsCompact K) (hKH : K ⊆ {x | 0 ≤ inner ℝ e x}) :
    ∃ δ C : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < C ∧
      ∀ (T : ℝ) (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ),
      0 < T → T ≤ δ → HolderBound α (cylinder {x | 0 ≤ inner ℝ e x} 0 T) a M →
      (∀ i, HolderBound α (cylinder {x | 0 ≤ inner ℝ e x} 0 T) (fun p => b p i) M) →
      Elliptic (cylinder {x | 0 ≤ inner ℝ e x} 0 T) a lam upper →
      (∀ p ∈ cylinder {x | 0 ≤ inner ℝ e x} 0 T, p.1 ∉ K → a p = 1) →
      ∃ U : compatibleHolderGraph α {x | 0 < inner ℝ e x} T → Point n → ℝ,
      (∀ f g p, p ∈ cylinder univ 0 T → U (f+g) p = U f p+U g p) ∧
      (∀ (c : ℝ) f p, p ∈ cylinder univ 0 T → U (c • f) p = c*U f p) ∧
      ∀ f,
        SchauderBound α (cylinder univ 0 T) (U f) (C*‖f‖) ∧
        HolderBound α (cylinder univ 0 T) (fun p => (U f p,spatialD (U f) p))
          (C*‖f‖) ∧
        (∀ x, U f (x,0) = 0) ∧
        (∀ x, inner ℝ e x = 0 → ∀ t ∈ Icc 0 T, U f (x,t) = 0) ∧
        ∀ p ∈ cylinder {x | 0 ≤ inner ℝ e x} 0 T,
          linearOp (cylinder {x | 0 ≤ inner ℝ e x} 0 T) a b (U f) p = compatibleHolderFun f p := by
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
  exact halfSpaceHolderInverse_linear_weighted hα hα1 hT (hTδ.trans hδ1) s hr hr1 hSep B
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
