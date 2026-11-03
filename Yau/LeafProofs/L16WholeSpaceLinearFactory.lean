import Yau.LeafProofs.L16HolderOnlyInverse
import Yau.LeafProofs.L16CompatibleParametrixFactory

open MeasureTheory Filter Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

local instance wholeSpaceLinearFactory_group {n : ℕ} (α : ℝ) (O : Set (Space n)) (T : ℝ) :
    NormedAddCommGroup (compatibleHolderGraph α O T) := inferInstance
local instance wholeSpaceLinearFactory_space {n : ℕ} (α : ℝ) (O : Set (Space n)) (T : ℝ) :
    NormedSpace ℝ (compatibleHolderGraph α O T) := inferInstance

/-- Actual whole-space finite kernels with their actual residual estimates
produce a genuine source-linear solution factory. -/
theorem localizedHeatParametrix_linear_weighted_inverse {n : ℕ} {α T : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1)
    (s : Finset (Space n)) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hSep : ∀ c ∈ s, ∀ d ∈ s, c ≠ d → r ≤ ‖c-d‖)
    (B : Space n → Space n ≃L[ℝ] Space n) (Bext : Space n ≃L[ℝ] Space n)
    (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ)
    (hGram : localizationGramIdentity s B Bext a)
    {β CP : ℝ} (hβ : 0 < β) (hCP : 0 < CP)
    (hWeighted : ∀ (f : Point n → ℝ) (F S : ℝ),
      HolderBound α (cylinder Set.univ 0 T) f F → 0 ≤ S → S ≤ F →
      (∀ p ∈ cylinder Set.univ 0 T, |f p| ≤ S) →
      HolderBound α (cylinder Set.univ 0 T)
        (localizedHeatResidual T s r hr B Bext a b f) (F/4+β*S/4) ∧
      (∀ p ∈ cylinder Set.univ 0 T,
        |localizedHeatResidual T s r hr B Bext a b f p| ≤ F/(4*β)))
    (hParametrix : ∀ (f : Point n → ℝ) (F : ℝ),
      HolderBound α (cylinder Set.univ 0 T) f F →
      SchauderBound α (cylinder Set.univ 0 T) (localizedHeatParametrix s hr B Bext f) (CP*F) ∧
      HolderBound α (cylinder Set.univ 0 T)
        (fun p => (localizedHeatParametrix s hr B Bext f p,
          spatialD (localizedHeatParametrix s hr B Bext f) p)) (CP*F)) :
    ∃ U : compatibleHolderGraph α (univ : Set (Space n)) T → Point n → ℝ,
      (∀ f g p, p ∈ cylinder univ 0 T → U (f+g) p = U f p+U g p) ∧
      (∀ (c : ℝ) f p, p ∈ cylinder univ 0 T → U (c • f) p = c*U f p) ∧
      ∀ f,
        SchauderBound α (cylinder univ 0 T) (U f) ((2*(1+β)*CP)*‖f‖) ∧
        HolderBound α (cylinder univ 0 T) (fun p => (U f p,spatialD (U f) p))
          ((2*(1+β)*CP)*‖f‖) ∧
        (∀ x, U f (x,0) = 0) ∧
        ∀ p ∈ cylinder univ 0 T,
          linearOp (cylinder univ 0 T) a b (U f) p = compatibleHolderFun f p := by
  let Q : Set (Point n) := cylinder univ 0 T
  let E := compatibleHolderGraph α (univ : Set (Space n)) T
  have hFunctionBound (x : E) : HolderBound α Q (compatibleHolderFun x) ‖x‖ := by
    simpa only [closure_univ] using compatibleHolderFun_holderBound x
  obtain ⟨P,hP,hSource⟩ := localizationSource_holderBound (n := n) hα hα1
  have hφ : ∀ i ∈ localizationIndices s, ContDiff ℝ 2 (localizationOuter s hr i) :=
    fun i _ => localizationOuter_contDiff s hr i
  have hψ : ∀ i ∈ localizationIndices s,
      HolderBound α Q (fun p => localizationSource s hr i p.1) (P*r⁻¹*r^(1-α)) :=
    fun i _ => hSource s r hr hr1 hSep T i
  let D : E → Point n → ℝ := fun x =>
    finiteHeatResidual T (localizationIndices s) (localizationEquiv B Bext)
      (localizationOuter s hr) (localizationSource s hr) a b (compatibleHolderFun x)
  have hResidualEq {f : Point n → ℝ} {F : ℝ} (hf : HolderBound α Q f F)
      {p : Point n} (hp : p ∈ Q) :
      finiteHeatResidual T (localizationIndices s) (localizationEquiv B Bext)
        (localizationOuter s hr) (localizationSource s hr) a b f p =
        localizedHeatResidual T s r hr B Bext a b f p := by
    unfold finiteHeatResidual
    change linearOp Q a b (localizedHeatParametrix s hr B Bext f) p-f p = _
    rw [localizedHeatParametrix_linearOp hα hα1 hT hT1 s hr hr1 hSep B Bext a b hGram hf hp]
    ring
  have hProjection (x : E) : ‖x.val.val.1‖ ≤ ‖x‖ := by
    change ‖x.val.val.1‖ ≤ max ‖x.val.val.1‖ ‖x.val.val.2‖
    exact le_max_left _ _
  have hGraphSup (x : E) (p : Point n) (hp : p ∈ Q) :
      |compatibleHolderFun x p| ≤ ‖x.val.val.1‖ := by
    rw [compatibleHolderFun,holderGraphFun_apply x.val ⟨p,by simpa only [closure_univ] using hp⟩]
    exact x.val.val.1.norm_coe_le_norm ⟨p,by simpa only [closure_univ] using hp⟩
  have hRefined (x : E) :
      HolderBound α Q (D x) (‖x‖/4+β*‖x.val.val.1‖/4) ∧
      (∀ p ∈ Q, |D x p| ≤ ‖x‖/(4*β)) := by
    have h := hWeighted (compatibleHolderFun x) ‖x‖ ‖x.val.val.1‖
      (hFunctionBound x) (norm_nonneg _) (hProjection x) (hGraphSup x)
    refine ⟨holderBound_congr_on h.1 (fun p hp => (hResidualEq (hFunctionBound x) hp).symm),?_⟩
    intro p hp
    rw [show D x p = localizedHeatResidual T s r hr B Bext a b (compatibleHolderFun x) p from
      hResidualEq (hFunctionBound x) hp]
    exact h.2 p hp
  have hAdd (x y : E) (p : Point n) (hp : p ∈ Q) :
      D (x+y) p = D x p+D y p := by
    dsimp only [D]
    rw [compatibleHolderFun_add]
    exact finiteHeatResidual_add _ _ _ _ a b hα hα1 hT hT1 hφ hψ
      (hFunctionBound x) (hFunctionBound y) hp
  have hSmul (c : ℝ) (x : E) (p : Point n) (hp : p ∈ Q) :
      D (c • x) p = c*D x p := by
    dsimp only [D]
    rw [compatibleHolderFun_smul]
    exact finiteHeatResidual_smul _ _ _ _ a b hα hα1 hT hT1 hφ hψ
      (hFunctionBound x) c hp
  let P0 : E → Point n → ℝ := fun f => localizedHeatParametrix s hr B Bext (compatibleHolderFun f)
  have hP0 (f : E) := hParametrix (compatibleHolderFun f) ‖f‖ (hFunctionBound f)
  have hInitial (f : E) (x : Space n) : P0 f (x,0) = 0 :=
    localizedHeatParametrix_initial s hr B Bext (compatibleHolderFun f) x
  have hLateral (f : E) (x : Space n) (hx : x ∈ frontier (univ : Set (Space n))) :
      ∀ t ∈ Icc 0 T, P0 f (x,t) = 0 := by
    simp only [frontier_univ,mem_empty_iff_false] at hx
  have hPAdd (f g : E) (p : Point n) (hp : p ∈ Q) : P0 (f+g) p = P0 f p+P0 g p := by
    dsimp only [P0,localizedHeatParametrix]
    rw [compatibleHolderFun_add]
    exact finiteHeatParametrix_add _ _ _ _ hα hT.le
      (fun i hi => holderBound_mul (hψ i hi) (hFunctionBound f))
      (fun i hi => holderBound_mul (hψ i hi) (hFunctionBound g)) hp
  have hPSmul (c : ℝ) (f : E) (p : Point n) (_hp : p ∈ Q) : P0 (c • f) p = c*P0 f p := by
    dsimp only [P0,localizedHeatParametrix]
    rw [compatibleHolderFun_smul]
    exact finiteHeatParametrix_smul _ _ _ _ c _ p
  have hOperator (f : E) (p : Point n) (_hp : p ∈ cylinder (closure (univ : Set (Space n))) 0 T) :
      linearOp (cylinder (closure (univ : Set (Space n))) 0 T) a b (P0 f) p =
        compatibleHolderFun f p+D f p := by
    rw [closure_univ]
    dsimp only [P0,localizedHeatParametrix,D,finiteHeatResidual]
    ring
  have hCornerD (f : E) (x : Space n) (hx : x ∈ frontier (univ : Set (Space n))) : D f (x,0) = 0 := by
    simp only [frontier_univ,mem_empty_iff_false] at hx
  obtain ⟨U,hUAdd,hUSmul,hU⟩ := compatibleParametrix_linear_inverse hα hT.le hβ hCP a b
    P0 D hP0 hInitial hLateral hPAdd hPSmul hOperator
    (fun f g p hp => hAdd f g p (by simpa only [closure_univ] using hp))
    (fun c f p hp => hSmul c f p (by simpa only [closure_univ] using hp)) hCornerD
    (fun f => by simpa only [closure_univ] using hRefined f)
  refine ⟨U,hUAdd,hUSmul,?_⟩
  intro f
  have h := hU f
  exact ⟨h.1,h.2.1,h.2.2.1,by simpa only [closure_univ] using h.2.2.2.2⟩

/-- Uniform actual source-linear whole-space inverse for only Holder
coefficients, with the constants fixed before every coefficient and source. -/
theorem exists_uniform_short_linear_schauder_inverse_holder_only {n : ℕ}
    {α M lam upper : ℝ} (hα : 0 < α) (hα1 : α < 1)
    {K : Set (Space n)} (hK : IsCompact K) :
    ∃ δ C : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < C ∧
      ∀ (T : ℝ) (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ),
      0 < T → T ≤ δ → HolderBound α (cylinder Set.univ 0 T) a M →
      (∀ i, HolderBound α (cylinder Set.univ 0 T) (fun p => b p i) M) →
      Elliptic (cylinder Set.univ 0 T) a lam upper →
      (∀ p ∈ cylinder Set.univ 0 T, p.1 ∉ K → a p = 1) →
      ∃ U : compatibleHolderGraph α (univ : Set (Space n)) T → Point n → ℝ,
      (∀ f g p, p ∈ cylinder univ 0 T → U (f+g) p = U f p+U g p) ∧
      (∀ (c : ℝ) f p, p ∈ cylinder univ 0 T → U (c • f) p = c*U f p) ∧
      ∀ f,
        SchauderBound α (cylinder univ 0 T) (U f) (C*‖f‖) ∧
        HolderBound α (cylinder univ 0 T) (fun p => (U f p,spatialD (U f) p))
          (C*‖f‖) ∧
        (∀ x, U f (x,0) = 0) ∧
        ∀ p ∈ cylinder univ 0 T,
          linearOp (cylinder univ 0 T) a b (U f) p = compatibleHolderFun f p := by
  let N : ℝ := ellipticHeatNormBudget α lam upper
  have hN : 0 ≤ N := by dsimp only [N,ellipticHeatNormBudget]; positivity
  obtain ⟨r,hr,s,β,δ,hr1,hsK,hSep,hCover,hβ,hδ,hδ1,hWeighted⟩ :=
    exists_localizedHeatResidual_holder_only_weighted_bounds
      (n := n) (M := M) (N := N) hα hα1 hK
  obtain ⟨CP,hCP,hParametrix⟩ :=
    localizedHeatParametrix_uniform_full_regularity hα hα1 N hN s hr hr1 hSep
  refine ⟨δ,2*(1+β)*CP,hδ,hδ1,by positivity,?_⟩
  intro T a b hT hTδ ha hb hEll hExterior
  obtain ⟨B,hBN,hNid,hGram⟩ := elliptic_localization_equivs hα.le hT.le a hEll s
  exact localizedHeatParametrix_linear_weighted_inverse hα hα1 hT (hTδ.trans hδ1) s hr hr1 hSep
    B (ContinuousLinearEquiv.refl ℝ (Space n)) a b hGram hβ hCP
    (fun f F S hf hS hSF hSup => hWeighted T a b B
      (ContinuousLinearEquiv.refl ℝ (Space n)) f F S hT hTδ
      ha hb hExterior hBN hNid hf hS hSF hSup)
    (fun f F hf => hParametrix B (ContinuousLinearEquiv.refl ℝ (Space n))
      hBN hNid T F hT (hTδ.trans hδ1) f hf)

end Yau.LeafProofs.L16Aux
