import Yau.LeafProofs.L16HalfSpaceControlled
import Yau.LeafProofs.L16DomainDataSource
import Yau.LeafProofs.L16HolderOnlyLocalization

open MeasureTheory Filter Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic
local instance halfSpaceResidualRates_dualGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance halfSpaceResidualRates_dualSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance
local instance halfSpaceResidualRates_hessianGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance
local instance halfSpaceResidualRates_hessianSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance

private theorem halfSpaceResidual_schauder_restrict_space {n : ℕ} {S X : Set (Space n)}
    {α l r C : ℝ} {u : Point n → ℝ} (hSX : S ⊆ X) (hu : SchauderBound α (cylinder X l r) u C) :
    SchauderBound α (cylinder S l r) u C := by
  have hSub : cylinder S l r ⊆ cylinder X l r := fun p hp => ⟨hSX hp.1,hp.2⟩
  refine ⟨c2_cylinder_mono_space hSX hu.1,hu.2.1,fun p hp => hu.2.2.1 p (hSub hp),
    holderBound_mono hu.2.2.2.1 hSub,?_⟩
  exact holderBound_congr_on (holderBound_mono hu.2.2.2.2 hSub)
    (fun p hp => (timeD_cylinder_change_space u hp.1 (hSX hp.1)).symm)

/-- The existing uniform cutoffs have the same refined source budget on
    any actual spatial set, including a closed half space. -/
theorem source_cutoffs_uniform_refined_holderBound_on {n : ℕ} {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) :
    ∃ P : ℝ, 0 < P ∧ ∀ (s : Finset (Space n)) (r : ℝ) (hr : 0 < r), r ≤ 1 →
      (∀ c ∈ s, ∀ d ∈ s, c ≠ d → r ≤ ‖c-d‖) → ∀ (O : Set (Space n)) (T F S : ℝ),
      ∀ f : Point n → ℝ, HolderBound α (cylinder O 0 T) f F → 0 ≤ S →
      (∀ p ∈ cylinder O 0 T, |f p| ≤ S) →
      (∀ c ∈ s, HolderBound α (cylinder O 0 T)
        (fun p => normalizedPatchCutoff s r hr c p.1*f p) (F+(P*r⁻¹*r^(1-α))*S)) ∧
      HolderBound α (cylinder O 0 T)
        (fun p => exteriorSourceCutoff s r hr p.1*f p) (F+(P*r⁻¹*r^(1-α))*S) := by
  obtain ⟨P,hP,hSource⟩ := source_cutoffs_uniform_holderBound (n := n) hα hα1
  refine ⟨P,hP,?_⟩
  intro s r hr hr1 hSep O T F S f hf hS hSup
  have hSub : cylinder O 0 T ⊆ cylinder univ 0 T := fun p hp => ⟨mem_univ _,hp.2⟩
  constructor
  · intro c hc
    apply holderBound_cutoff_source_refined (holderBound_mono ((hSource s r hr hr1 hSep T).1 c) hSub) _ hf hS hSup
    intro p hp
    rw [abs_of_nonneg (normalizedPatchCutoff_nonneg s hr c p.1)]
    exact normalizedPatchCutoff_le_one s hr hc p.1
  · apply holderBound_cutoff_source_refined (holderBound_mono (hSource s r hr hr1 hSep T).2 hSub) _ hf hS hSup
    intro p hp
    rw [abs_of_nonneg (exteriorSourceCutoff_mem_Icc s hr p.1).1]
    exact (exteriorSourceCutoff_mem_Icc s hr p.1).2

/-- The actual frozen half-space kernel has the refined two-norm residual
    bounds, with the same proved geometric rates as whole-space localization. -/
theorem interiorHalfSpaceResidual_holder_only_refined_bounds {n : ℕ} {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) :
    ∃ P Cφ CH : ℝ, 0 < P ∧ 0 < Cφ ∧ 0 < CH ∧
      ∀ (s : Finset (Space n)) (r : ℝ) (hr : 0 < r), r ≤ 1 →
      (∀ c ∈ s, ∀ d ∈ s, c ≠ d → r ≤ ‖c-d‖) →
      ∀ (T F S M N : ℝ) (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ)
        (B : Space n ≃L[ℝ] Space n) (c e : Space n) (f : Point n → ℝ),
      c ∈ s → 0 ≤ inner ℝ e c → ‖e‖ = 1 →
      (∀ H : Space n →L[ℝ] Space n →L[ℝ] ℝ,
        (∑ k : Yau.RIdx n, H (B (Yau.realVec k)) (B (Yau.realVec k))) =
          ∑ i : Yau.RIdx n, ∑ j : Yau.RIdx n, a (c,0) i j*H (Yau.realVec i) (Yau.realVec j)) →
      0 < T → T ≤ 1 → constantHeatNormFactor α B ≤ N →
      HolderBound α (cylinder {x : Space n | 0 ≤ inner ℝ e x} 0 T) a M →
      (∀ i, HolderBound α (cylinder {x : Space n | 0 ≤ inner ℝ e x} 0 T) (fun p => b p i) M) →
      HolderBound α (cylinder {x : Space n | 0 ≤ inner ℝ e x} 0 T) f F →
      (∀ x, inner ℝ e x = 0 → f (x,0) = 0) → 0 ≤ S →
      (∀ p ∈ cylinder {x : Space n | 0 ≤ inner ℝ e x} 0 T, |f p| ≤ S) →
      HolderBound α (cylinder {x : Space n | 0 ≤ inner ℝ e x} 0 T)
        (frozenPatchResidual (cylinder {x : Space n | 0 ≤ inner ℝ e x} 0 T) a b (a (c,0)) (outerPatchBump r hr c)
          (halfSpaceConstantPullbackDuhamel B e T (fun p => normalizedPatchCutoff s r hr c p.1*f p)))
        (holderOnlyInteriorHolderRate n α Cφ CH M N r T*(F+(P*r⁻¹*r^(1-α))*S)) ∧
      (∀ p ∈ cylinder {x : Space n | 0 ≤ inner ℝ e x} 0 T,
        |frozenPatchResidual (cylinder {x : Space n | 0 ≤ inner ℝ e x} 0 T) a b (a (c,0)) (outerPatchBump r hr c)
          (halfSpaceConstantPullbackDuhamel B e T (fun p => normalizedPatchCutoff s r hr c p.1*f p)) p| ≤
        holderOnlyInteriorSupRate n α Cφ CH M N r T*(F+(P*r⁻¹*r^(1-α))*S)) := by
  obtain ⟨P,hP,hSource⟩ := source_cutoffs_uniform_refined_holderBound_on (n := n) hα hα1
  obtain ⟨Cφ,hCφ,hCutoff⟩ := patchBumps_uniform_three_holderBounds (n := n) hα hα1
  obtain ⟨CH,hCH,hHeat⟩ := halfSpaceConstantPullbackDuhamel_controlled_bounds (n := n) hα hα1
  refine ⟨P,Cφ,CH,hP,hCφ,hCH,?_⟩
  intro s r hr hr1 hSep T F S M N a b B c e f hc hCenter he hGram hT hT1 hN ha hb hf hCorner hS hSup
  let E0 := cutoffJetBudget α Cφ r 0
  let E1 := cutoffJetBudget α Cφ r 1
  let E2 := cutoffJetBudget α Cφ r 2
  let W : ℝ := F+(P*r⁻¹*r^(1-α))*S
  let G : ℝ := CH*N
  let w : Point n → ℝ := fun p => normalizedPatchCutoff s r hr c p.1*f p
  let u : Point n → ℝ := halfSpaceConstantPullbackDuhamel B e T w
  have hWeighted : HolderBound α (cylinder {x : Space n | 0 ≤ inner ℝ e x} 0 T) w W :=
    (hSource s r hr hr1 hSep {x | 0 ≤ inner ℝ e x} T F S f hf hS hSup).1 c hc
  have hWCorner : ∀ x, inner ℝ e x = 0 → w (x,0) = 0 := by
    intro x hx
    change normalizedPatchCutoff s r hr c x*f (x,0) = 0
    rw [hCorner x hx,mul_zero]
  have hHeatFull := hHeat N B hN (a (c,0)) hGram e he T W hT hT1 w hWeighted hWCorner
  have hSub : cylinder {x : Space n | 0 ≤ inner ℝ e x} 0 T ⊆ cylinder univ 0 T :=
    fun p hp => ⟨mem_univ _,hp.2⟩
  have hHeatBounds := And.intro
    (halfSpaceResidual_schauder_restrict_space (subset_univ {x | 0 ≤ inner ℝ e x}) hHeatFull.1)
    (And.intro (fun p hp => hHeatFull.2.1 p (hSub hp)) (holderBound_mono hHeatFull.2.2 hSub))
  have hHeatScale : CH*W*N = G*W := by dsimp only [G]; ring
  rw [hHeatScale] at hHeatBounds
  have hCut := hCutoff r hr hr1 T c _ (Or.inr rfl)
  have hφ : HolderBound α (cylinder {x : Space n | 0 ≤ inner ℝ e x} 0 T) (fun p => outerPatchBump r hr c p.1) E0 := by
    simpa only [E0,cutoffJetBudget,Nat.zero_add,pow_one] using holderBound_mono hCut.1 hSub
  have hφD : HolderBound α (cylinder {x : Space n | 0 ≤ inner ℝ e x} 0 T)
      (fun p => fderiv ℝ (outerPatchBump r hr c) p.1) E1 := by
    simpa only [E1,cutoffJetBudget] using holderBound_mono hCut.2.1 hSub
  have hφDD : HolderBound α (cylinder {x : Space n | 0 ≤ inner ℝ e x} 0 T)
      (fun p => fderiv ℝ (fderiv ℝ (outerPatchBump r hr c)) p.1) E2 := by
    simpa only [E2,cutoffJetBudget] using holderBound_mono hCut.2.2 hSub
  have hOrigin : (c,(0 : ℝ)) ∈ cylinder {x : Space n | 0 ≤ inner ℝ e x} 0 T := ⟨hCenter,le_rfl,hT.le⟩
  have hA0 : 0 ≤ M*((2*r)^α+T^(α/2)) := mul_nonneg ha.1 (by positivity)
  have hD0 : 0 ≤ G*W*T^(α/2) :=
    mul_nonneg hHeatBounds.1.2.1 (Real.rpow_nonneg hT.le _)
  have hCoeff (i j : Yau.RIdx n) := frozen_patch_coefficient_holderBound ha hφ c 0 hOrigin i j
  have hCoeffSup (i j : Yau.RIdx n) (p : Point n) (hp : p ∈ cylinder {x : Space n | 0 ≤ inner ℝ e x} 0 T) :
      |outerPatchBump r hr c p.1*(a (c,0) i j-a p i j)| ≤ M*((2*r)^α+T^(α/2)) := by
    apply frozen_patch_coefficient_sup_holder hα.le ha hr c hOrigin hp
    simpa only [sub_zero,abs_of_nonneg hp.2.1] using hp.2.2
  constructor
  · have hBound := frozenPatchResidual_holderBound hA0 hD0 ha hb hφ
      (fun i => holderBound_gradient_component hφD i)
      (fun i j => holderBound_hessian_component hφDD i j)
      hHeatBounds.2.2 hHeatBounds.1.2.2.2.1 hHeatBounds.2.1 hCoeff hCoeffSup
    change HolderBound α (cylinder {x : Space n | 0 ≤ inner ℝ e x} 0 T)
      (frozenPatchResidual (cylinder {x : Space n | 0 ≤ inner ℝ e x} 0 T) a b (a (c,0)) (outerPatchBump r hr c) u) _
    convert hBound using 1
    dsimp only [holderOnlyInteriorHolderRate,lowerCutoffBudget,E0,E1,E2,G,W]
    ring
  · intro p hp
    have hBound := frozenPatchResidual_sup_bound hD0 ha hb hφ
      (fun i => holderBound_gradient_component hφD i)
      (fun i j => holderBound_hessian_component hφDD i j)
      hHeatBounds.2.2 hHeatBounds.2.1 hCoeffSup hp
    change |frozenPatchResidual (cylinder {x : Space n | 0 ≤ inner ℝ e x} 0 T) a b (a (c,0)) (outerPatchBump r hr c) u p| ≤ _
    convert hBound using 1
    dsimp only [holderOnlyInteriorSupRate,lowerCutoffBudget,E0,E1,E2,G,W]
    ring


/-- The genuine exterior half-space patch has only lower-jet errors,
    whose already proved Holder rate vanishes as the time horizon shrinks. -/
theorem exteriorHalfSpaceResidual_holder_only_refined_bound {n : ℕ} {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) :
    ∃ P CH : ℝ, 0 < P ∧ 0 < CH ∧
      ∀ (s : Finset (Space n)) (r : ℝ) (hr : 0 < r), r ≤ 1 →
      (∀ c ∈ s, ∀ d ∈ s, c ≠ d → r ≤ ‖c-d‖) →
      ∃ E0 E1 E2 : ℝ, 0 < E0 ∧ 0 < E1 ∧ 0 < E2 ∧
      ∀ (K : Set (Space n)) (T F S M N : ℝ) (a : Point n → Mat n)
        (b : Point n → Yau.RIdx n → ℝ) (B : Space n ≃L[ℝ] Space n) (e : Space n) (f : Point n → ℝ),
      ‖e‖ = 1 →
      (∀ H : Space n →L[ℝ] Space n →L[ℝ] ℝ,
        (∑ k : Yau.RIdx n, H (B (Yau.realVec k)) (B (Yau.realVec k))) =
          ∑ i : Yau.RIdx n, ∑ j : Yau.RIdx n, (1 : Mat n) i j*H (Yau.realVec i) (Yau.realVec j)) →
      0 < T → T ≤ 1 → constantHeatNormFactor α B ≤ N →
      (∀ x ∈ K, 1 ≤ patchSum s r hr x) →
      HolderBound α (cylinder {x : Space n | 0 ≤ inner ℝ e x} 0 T) a M →
      (∀ i, HolderBound α (cylinder {x : Space n | 0 ≤ inner ℝ e x} 0 T) (fun p => b p i) M) →
      (∀ p ∈ cylinder {x : Space n | 0 ≤ inner ℝ e x} 0 T, p.1 ∉ K → a p = 1) →
      HolderBound α (cylinder {x : Space n | 0 ≤ inner ℝ e x} 0 T) f F →
      (∀ x, inner ℝ e x = 0 → f (x,0) = 0) → 0 ≤ S →
      (∀ p ∈ cylinder {x : Space n | 0 ≤ inner ℝ e x} 0 T, |f p| ≤ S) →
      HolderBound α (cylinder {x : Space n | 0 ≤ inner ℝ e x} 0 T)
        (frozenPatchResidual (cylinder {x : Space n | 0 ≤ inner ℝ e x} 0 T) a b 1 (exteriorCutoff s r hr)
          (halfSpaceConstantPullbackDuhamel B e T (fun p => exteriorSourceCutoff s r hr p.1*f p)))
        (holderOnlyExteriorRate n α CH M N T E0 E1 E2*(F+(P*r⁻¹*r^(1-α))*S)) := by
  obtain ⟨P,hP,hSource⟩ := source_cutoffs_uniform_refined_holderBound_on (n := n) hα hα1
  obtain ⟨CH,hCH,hHeat⟩ := halfSpaceConstantPullbackDuhamel_controlled_bounds (n := n) hα hα1
  refine ⟨P,CH,hP,hCH,?_⟩
  intro s r hr hr1 hSep
  obtain ⟨E0,E1,E2,hE0,hE1,hE2,hφ0,hφD0,hφDD0⟩ := exteriorCutoff_holder_jets hα hα1 s hr
  refine ⟨E0,E1,E2,hE0,hE1,hE2,?_⟩
  intro K T F S M N a b B e f he hGram hT hT1 hN hCover ha hb hExterior hf hCorner hS hSup
  let W : ℝ := F+(P*r⁻¹*r^(1-α))*S
  let G : ℝ := CH*N
  let w : Point n → ℝ := fun p => exteriorSourceCutoff s r hr p.1*f p
  let u : Point n → ℝ := halfSpaceConstantPullbackDuhamel B e T w
  have hWeighted : HolderBound α (cylinder {x : Space n | 0 ≤ inner ℝ e x} 0 T) w W :=
    (hSource s r hr hr1 hSep {x | 0 ≤ inner ℝ e x} T F S f hf hS hSup).2
  have hWCorner : ∀ x, inner ℝ e x = 0 → w (x,0) = 0 := by
    intro x hx
    change exteriorSourceCutoff s r hr x*f (x,0) = 0
    rw [hCorner x hx,mul_zero]
  have hHeatFull := hHeat N B hN 1 hGram e he T W hT hT1 w hWeighted hWCorner
  have hSub : cylinder {x : Space n | 0 ≤ inner ℝ e x} 0 T ⊆ cylinder univ 0 T :=
    fun p hp => ⟨mem_univ _,hp.2⟩
  have hSubUnit : cylinder {x : Space n | 0 ≤ inner ℝ e x} 0 T ⊆ cylinder univ 0 1 :=
    fun p hp => ⟨mem_univ _,hp.2.1,hp.2.2.trans hT1⟩
  have hHeatBounds := And.intro
    (halfSpaceResidual_schauder_restrict_space (subset_univ {x | 0 ≤ inner ℝ e x}) hHeatFull.1)
    (And.intro (fun p hp => hHeatFull.2.1 p (hSub hp)) (holderBound_mono hHeatFull.2.2 hSub))
  have hHeatScale : CH*W*N = G*W := by dsimp only [G]; ring
  rw [hHeatScale] at hHeatBounds
  have hφ := holderBound_mono hφ0 hSubUnit
  have hφD := holderBound_mono hφD0 hSubUnit
  have hφDD := holderBound_mono hφDD0 hSubUnit
  have hLower := lowerPatchResidual_holderBound ha hb hφ
    (fun i => holderBound_gradient_component hφD i)
    (fun i j => holderBound_hessian_component hφDD i j) hHeatBounds.2.2
  have hResidual := holderBound_congr_on (holderBound_neg hLower) (show
      Set.EqOn (fun p => -lowerPatchResidual a b (exteriorCutoff s r hr) u p)
        (frozenPatchResidual (cylinder {x : Space n | 0 ≤ inner ℝ e x} 0 T) a b 1 (exteriorCutoff s r hr) u)
        (cylinder {x : Space n | 0 ≤ inner ℝ e x} 0 T) from by
    intro p hp
    exact (exterior_frozenPatchResidual_eq_neg_lower b s hr hCover hExterior u hp).symm)
  change HolderBound α (cylinder {x : Space n | 0 ≤ inner ℝ e x} 0 T)
    (frozenPatchResidual (cylinder {x : Space n | 0 ≤ inner ℝ e x} 0 T) a b 1 (exteriorCutoff s r hr) u) _
  convert hResidual using 1
  dsimp only [holderOnlyExteriorRate,lowerCutoffBudget,G,W]
  ring


def localizedHalfSpaceResidual {n : ℕ} (T : ℝ) (s : Finset (Space n))
    (r : ℝ) (hr : 0 < r) (B : Space n → Space n ≃L[ℝ] Space n)
    (Bext : Space n ≃L[ℝ] Space n) (e : Space n) (a : Point n → Mat n)
    (b : Point n → Yau.RIdx n → ℝ) (f : Point n → ℝ) (p : Point n) : ℝ :=
  (∑ c ∈ s, frozenPatchResidual (cylinder {x : Space n | 0 ≤ inner ℝ e x} 0 T) a b (a (c,0))
    (outerPatchBump r hr c)
    (halfSpaceConstantPullbackDuhamel (B c) e T (fun q => normalizedPatchCutoff s r hr c q.1*f q)) p)+
  frozenPatchResidual (cylinder {x : Space n | 0 ≤ inner ℝ e x} 0 T) a b 1 (exteriorCutoff s r hr)
    (halfSpaceConstantPullbackDuhamel Bext e T (fun q => exteriorSourceCutoff s r hr q.1*f q)) p

/-- The actual sum has dimension-only overlap before the spatial radius
    is chosen; both refined norms concern the real half-space residual. -/
theorem localizedHalfSpaceResidual_holder_only_refined_bounds {n : ℕ} {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) :
    ∃ PI PE Cφ CHI CHE : ℝ, 0 < PI ∧ 0 < PE ∧ 0 < Cφ ∧ 0 < CHI ∧ 0 < CHE ∧
      ∀ (s : Finset (Space n)) (r : ℝ) (hr : 0 < r), r ≤ 1 →
      (∀ c ∈ s, ∀ d ∈ s, c ≠ d → r ≤ ‖c-d‖) →
      ∃ E0 E1 E2 : ℝ, 0 < E0 ∧ 0 < E1 ∧ 0 < E2 ∧
      ∀ (K : Set (Space n)) (T F S M N : ℝ) (a : Point n → Mat n)
        (b : Point n → Yau.RIdx n → ℝ) (B : Space n → Space n ≃L[ℝ] Space n)
        (Bext : Space n ≃L[ℝ] Space n) (e : Space n) (f : Point n → ℝ),
      ‖e‖ = 1 → (∀ c ∈ s, 0 ≤ inner ℝ e c) →
      (∀ c ∈ s, ∀ H : Space n →L[ℝ] Space n →L[ℝ] ℝ,
        (∑ k : Yau.RIdx n, H (B c (Yau.realVec k)) (B c (Yau.realVec k))) =
          ∑ i : Yau.RIdx n, ∑ j : Yau.RIdx n, a (c,0) i j*H (Yau.realVec i) (Yau.realVec j)) →
      (∀ H : Space n →L[ℝ] Space n →L[ℝ] ℝ,
        (∑ k : Yau.RIdx n, H (Bext (Yau.realVec k)) (Bext (Yau.realVec k))) =
          ∑ i : Yau.RIdx n, ∑ j : Yau.RIdx n, (1 : Mat n) i j*H (Yau.realVec i) (Yau.realVec j)) →
      0 < T → T ≤ 1 →
      (∀ x ∈ K, 1 ≤ patchSum s r hr x) →
      HolderBound α (cylinder {x : Space n | 0 ≤ inner ℝ e x} 0 T) a M →
      (∀ i, HolderBound α (cylinder {x : Space n | 0 ≤ inner ℝ e x} 0 T) (fun p => b p i) M) →
      (∀ p ∈ cylinder {x : Space n | 0 ≤ inner ℝ e x} 0 T, p.1 ∉ K → a p = 1) →
      (∀ c, constantHeatNormFactor α (B c) ≤ N) →
      constantHeatNormFactor α Bext ≤ N →
      HolderBound α (cylinder {x : Space n | 0 ≤ inner ℝ e x} 0 T) f F →
      (∀ x, inner ℝ e x = 0 → f (x,0) = 0) → 0 ≤ S →
      (∀ p ∈ cylinder {x : Space n | 0 ≤ inner ℝ e x} 0 T, |f p| ≤ S) →
      HolderBound α (cylinder {x : Space n | 0 ≤ inner ℝ e x} 0 T)
        (localizedHalfSpaceResidual T s r hr B Bext e a b f)
        (holderOnlyTotalHolderRate n α Cφ CHI CHE M N r T E0 E1 E2*
          (F+((PI+PE)*r⁻¹*r^(1-α))*S)) ∧
      (∀ p ∈ cylinder {x : Space n | 0 ≤ inner ℝ e x} 0 T,
        |localizedHalfSpaceResidual T s r hr B Bext e a b f p| ≤
        holderOnlyTotalSupRate n α Cφ CHI CHE M N r T E0 E1 E2*
          (F+((PI+PE)*r⁻¹*r^(1-α))*S)) := by
  obtain ⟨PI,Cφ,CHI,hPI,hCφ,hCHI,hInterior⟩ :=
    interiorHalfSpaceResidual_holder_only_refined_bounds (n := n) hα hα1
  obtain ⟨PE,CHE,hPE,hCHE,hExterior⟩ :=
    exteriorHalfSpaceResidual_holder_only_refined_bound (n := n) hα hα1
  refine ⟨PI,PE,Cφ,CHI,CHE,hPI,hPE,hCφ,hCHI,hCHE,?_⟩
  intro s r hr hr1 hSep
  obtain ⟨E0,E1,E2,hE0,hE1,hE2,hExt⟩ := hExterior s r hr hr1 hSep
  refine ⟨E0,E1,E2,hE0,hE1,hE2,?_⟩
  intro K T F S M N a b B Bext e f he hCenters hGram hGramExt hT hT1 hCover ha hb hExteriorCoeff hB hBext hf hCorner hS hSup
  let W : ℝ := F+((PI+PE)*r⁻¹*r^(1-α))*S
  let AI := holderOnlyInteriorHolderRate n α Cφ CHI M N r T
  let BI := holderOnlyInteriorSupRate n α Cφ CHI M N r T
  let AE := holderOnlyExteriorRate n α CHE M N T E0 E1 E2
  have hF : 0 ≤ F := hf.1
  have hM : 0 ≤ M := ha.1
  have hN : 0 ≤ N := (constantHeatNormFactor_pos α Bext).le.trans hBext
  have hAI : 0 ≤ AI := by
    dsimp only [AI,holderOnlyInteriorHolderRate,lowerCutoffBudget,cutoffJetBudget]
    positivity
  have hBI : 0 ≤ BI := by
    dsimp only [BI,holderOnlyInteriorSupRate,lowerCutoffBudget,cutoffJetBudget]
    positivity
  have hAE : 0 ≤ AE := by
    dsimp only [AE,holderOnlyExteriorRate,lowerCutoffBudget]
    positivity
  have hW : 0 ≤ W := by dsimp only [W]; positivity
  have hCmpI : F+(PI*r⁻¹*r^(1-α))*S ≤ W := by
    dsimp only [W]
    have hExtra : 0 ≤ PE*r⁻¹*r^(1-α)*S := by positivity
    nlinarith
  have hCmpE : F+(PE*r⁻¹*r^(1-α))*S ≤ W := by
    dsimp only [W]
    have hExtra : 0 ≤ PI*r⁻¹*r^(1-α)*S := by positivity
    nlinarith
  have hIntRaw (c : Space n) (hc : c ∈ s) :=
    hInterior s r hr hr1 hSep T F S M N a b (B c) c e f hc (hCenters c hc) he (hGram c hc) hT hT1 (hB c) ha hb hf hCorner hS hSup
  have hExtRaw := hExt K T F S M N a b Bext e f he hGramExt hT hT1 hBext hCover ha hb hExteriorCoeff hf hCorner hS hSup
  have hInt (c : Space n) (hc : c ∈ s) : HolderBound α (cylinder {x : Space n | 0 ≤ inner ℝ e x} 0 T)
      (frozenPatchResidual (cylinder {x : Space n | 0 ≤ inner ℝ e x} 0 T) a b (a (c,0)) (outerPatchBump r hr c)
        (halfSpaceConstantPullbackDuhamel (B c) e T (fun p => normalizedPatchCutoff s r hr c p.1*f p))) (AI*W) :=
    holderBound_mono_const (hIntRaw c hc).1 (mul_le_mul_of_nonneg_left hCmpI hAI)
  have hExt := holderBound_mono_const hExtRaw (mul_le_mul_of_nonneg_left hCmpE hAE)
  constructor
  · have hIntSum := frozenPatchResidual_outer_sum_holderBound a b (fun c => a (c,0))
      (fun c => halfSpaceConstantPullbackDuhamel (B c) e T (fun q => normalizedPatchCutoff s r hr c q.1*f q))
      hr s hSep (mul_nonneg hAI hW) hInt
    have hTotal := holderBound_add hIntSum hExt
    change HolderBound α (cylinder {x : Space n | 0 ≤ inner ℝ e x} 0 T)
      (localizedHalfSpaceResidual T s r hr B Bext e a b f) _ at hTotal
    convert hTotal using 1
    dsimp only [holderOnlyTotalHolderRate,AI,AE]
    ring
  · intro p hp
    have hIntSup (c : Space n) (hc : c ∈ s) (q : Point n)
        (hq : q ∈ cylinder {x : Space n | 0 ≤ inner ℝ e x} 0 T) :
        |frozenPatchResidual (cylinder {x : Space n | 0 ≤ inner ℝ e x} 0 T) a b (a (c,0)) (outerPatchBump r hr c)
          (halfSpaceConstantPullbackDuhamel (B c) e T (fun z => normalizedPatchCutoff s r hr c z.1*f z)) q| ≤ BI*W :=
      ((hIntRaw c hc).2 q hq).trans (mul_le_mul_of_nonneg_left hCmpI hBI)
    have hIntSum := frozenPatchResidual_outer_sum_sup_bound a b (fun c => a (c,0))
      (fun c => halfSpaceConstantPullbackDuhamel (B c) e T (fun q => normalizedPatchCutoff s r hr c q.1*f q))
      hr s hSep (mul_nonneg hBI hW) hIntSup hp
    have hExtSup := hExt.2.1 p hp
    have hTotal := (abs_add_le _ _).trans (add_le_add hIntSum hExtSup)
    change |localizedHalfSpaceResidual T s r hr B Bext e a b f p| ≤ _ at hTotal
    convert hTotal using 1
    dsimp only [holderOnlyTotalSupRate,BI,AE]
    ring


/-- Actual half-space residual contraction scales. Every spatial cover,
    weight and time horizon is chosen before the coefficients or source. -/
theorem exists_localizedHalfSpaceResidual_holder_only_weighted_bounds {n : ℕ}
    {α M N : ℝ} (hα : 0 < α) (hα1 : α < 1)
    {K : Set (Space n)} (hK : IsCompact K) (e : Space n) (he : ‖e‖ = 1)
    (hKH : K ⊆ {x : Space n | 0 ≤ inner ℝ e x}) :
    ∃ (r : ℝ) (hr : 0 < r) (s : Finset (Space n)) (β δ : ℝ), r ≤ 1 ∧
      (∀ c ∈ s, c ∈ K) ∧ (∀ c ∈ s, ∀ d ∈ s, c ≠ d → r ≤ ‖c-d‖) ∧
      (∀ x ∈ K, 1 ≤ patchSum s r hr x) ∧ 0 < β ∧ 0 < δ ∧ δ ≤ 1 ∧
      ∀ (T : ℝ) (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ)
        (B : Space n → Space n ≃L[ℝ] Space n)
        (Bext : Space n ≃L[ℝ] Space n) (f : Point n → ℝ) (F S : ℝ),
      0 < T → T ≤ δ →
      HolderBound α (cylinder {x : Space n | 0 ≤ inner ℝ e x} 0 T) a M →
      (∀ i, HolderBound α (cylinder {x : Space n | 0 ≤ inner ℝ e x} 0 T) (fun p => b p i) M) →
      (∀ p ∈ cylinder {x : Space n | 0 ≤ inner ℝ e x} 0 T, p.1 ∉ K → a p = 1) →
      (∀ c, constantHeatNormFactor α (B c) ≤ N) →
      constantHeatNormFactor α Bext ≤ N →
      (∀ c ∈ s, ∀ H : Space n →L[ℝ] Space n →L[ℝ] ℝ,
        (∑ k : Yau.RIdx n, H (B c (Yau.realVec k)) (B c (Yau.realVec k))) =
          ∑ i : Yau.RIdx n, ∑ j : Yau.RIdx n, a (c,0) i j*H (Yau.realVec i) (Yau.realVec j)) →
      (∀ H : Space n →L[ℝ] Space n →L[ℝ] ℝ,
        (∑ k : Yau.RIdx n, H (Bext (Yau.realVec k)) (Bext (Yau.realVec k))) =
          ∑ i : Yau.RIdx n, ∑ j : Yau.RIdx n, (1 : Mat n) i j*H (Yau.realVec i) (Yau.realVec j)) →
      HolderBound α (cylinder {x : Space n | 0 ≤ inner ℝ e x} 0 T) f F →
      (∀ x, inner ℝ e x = 0 → f (x,0) = 0) → 0 ≤ S → S ≤ F →
      (∀ p ∈ cylinder {x : Space n | 0 ≤ inner ℝ e x} 0 T, |f p| ≤ S) →
      HolderBound α (cylinder {x : Space n | 0 ≤ inner ℝ e x} 0 T)
        (localizedHalfSpaceResidual T s r hr B Bext e a b f) (F/4+β*S/4) ∧
      (∀ p ∈ cylinder {x : Space n | 0 ≤ inner ℝ e x} 0 T,
        |localizedHalfSpaceResidual T s r hr B Bext e a b f p| ≤ F/(4*β)) := by
  obtain ⟨PI,PE,Cφ,CHI,CHE,hPI,hPE,hCφ,hCHI,hCHE,hActual⟩ :=
    localizedHalfSpaceResidual_holder_only_refined_bounds (n := n) hα hα1
  obtain ⟨r,hr,hr1,hScales⟩ :=
    exists_holder_only_localization_scales n hα hα1 PI PE Cφ CHI CHE M N
  obtain ⟨s,hsK,hSep,hCover,_,_⟩ := compact_separated_patch_partition hK hr
  obtain ⟨E0,E1,E2,hE0,hE1,hE2,hBounds⟩ := hActual s r hr hr1 hSep
  obtain ⟨β,δ,hβ,hWeight,hδ,hδ1,hRate⟩ := hScales E0 E1 E2
  refine ⟨r,hr,s,β,δ,hr1,hsK,hSep,hCover,hβ,hδ,hδ1,?_⟩
  intro T a b B Bext f F S hT hTδ ha hb hExt hB hBext hGram hGramExt hf hCorner hS hSF hSup
  let p : ℝ := (PI+PE)*r⁻¹*r^(1-α)
  have hp : 0 ≤ p := by dsimp only [p]; positivity
  have hF : 0 ≤ F := hf.1
  have hM : 0 ≤ M := ha.1
  have hN : 0 ≤ N := (constantHeatNormFactor_pos α Bext).le.trans hBext
  have hW : 0 ≤ F+p*S := by positivity
  have hRho : 0 ≤ holderOnlyTotalSupRate n α Cφ CHI CHE M N r T E0 E1 E2 := by
    dsimp only [holderOnlyTotalSupRate,holderOnlyInteriorSupRate,holderOnlyExteriorRate,
      lowerCutoffBudget,cutoffJetBudget]
    positivity
  have hFull := hBounds K T F S M N a b B Bext e f he
    (fun c hc => hKH (hsK c hc)) hGram hGramExt hT (hTδ.trans hδ1) hCover
    ha hb hExt hB hBext hf hCorner hS hSup
  have hSmall := hRate T hT.le hTδ
  constructor
  · apply holderBound_mono_const hFull.1
    have h := mul_le_mul_of_nonneg_right hSmall.1 hW
    have hWeightS := mul_le_mul_of_nonneg_right hWeight hS
    change holderOnlyTotalHolderRate n α Cφ CHI CHE M N r T E0 E1 E2*(F+p*S) ≤ _
    change p*S ≤ β*S at hWeightS
    nlinarith
  · intro q hq
    have hWBound : F+p*S ≤ (1+p)*F := by nlinarith [mul_le_mul_of_nonneg_left hSF hp]
    calc
      _ ≤ holderOnlyTotalSupRate n α Cφ CHI CHE M N r T E0 E1 E2*(F+p*S) :=
        hFull.2 q hq
      _ ≤ holderOnlyTotalSupRate n α Cφ CHI CHE M N r T E0 E1 E2*((1+p)*F) :=
        mul_le_mul_of_nonneg_left hWBound hRho
      _ = ((1+p)*holderOnlyTotalSupRate n α Cφ CHI CHE M N r T E0 E1 E2)*F := by ring
      _ ≤ (1/(4*β))*F := mul_le_mul_of_nonneg_right hSmall.2 hF
      _ = F/(4*β) := by ring


end Yau.LeafProofs.L16Aux
