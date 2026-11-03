import Yau.Proofs.F05FlowLocalFactory

/-! The native local solvers are instantiated with the actual supplied metric
and scalar field, uniformly before every short endpoint and source. -/

open Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

def F05FlowPrincipal (A : AtlasData M) (i : Fin A.count)
    (h : ℝ → HermitianField M) (c : M.Carrier → ℝ → ℝ) (p : Point n) : Mat n :=
  pull A i c p • flatA (h p.2) A i p

def F05FlowDrift (A : AtlasData M) (i : Fin A.count)
    (h : ℝ → HermitianField M) (c : M.Carrier → ℝ → ℝ) (p : Point n) (j : RIdx n) : ℝ :=
  pull A i c p * flatB (h p.2) A i p j

def F05ActualPatchData (A : AtlasData M) (χ : Fin A.count → M.Carrier → ℝ)
    (h : ℝ → HermitianField M) (c : M.Carrier → ℝ → ℝ)
    (α C E T ρ : ℝ) (i : Fin A.count)
    (W H : compatibleHolderGraph α (F05ModelOpen A i) T → Point n → ℝ) : Prop :=
  (∀ f g p, p ∈ cylinder univ 0 T → W (f+g) p = W f p+W g p) ∧
  (∀ (d : ℝ) f p, p ∈ cylinder univ 0 T → W (d • f) p = d*W f p) ∧
  (∀ f x, H f (x,0) = 0) ∧ ∀ f,
    (SchauderBound α (cylinder univ 0 T) (W f) (C*‖f‖) ∧
    HolderBound α (cylinder univ 0 T) (fun p => (W f p,spatialD (W f) p)) (C*‖f‖*ρ^(1-α)) ∧
    (∀ x, W f (x,0) = 0) ∧
    (∀ x ∈ frontier (F05ModelOpen A i), ∀ t ∈ Icc 0 T, W f (x,t) = 0) ∧
    ∀ p ∈ cylinder (closure (F05ModelOpen A i)) 0 T,
      linearOp (cylinder (closure (F05ModelOpen A i)) 0 T)
        (F05PrincipalExtension (F05FlowPrincipal A i h c))
        (F05DriftExtension (F05FlowDrift A i h c)) (W f) p =
        F05ModelPartition A χ i p.1*compatibleHolderFun f p-H f p) ∧
    HolderBound α (cylinder (closure (F05ModelOpen A i)) 0 T) (H f) (E*‖f‖*ρ^(1-α)) ∧
    ∀ p ∈ cylinder (closure (F05ModelOpen A i)) 0 T, ‖p.1‖ ≤ 1 →
      linearOp (cylinder (closure (F05ModelOpen A i)) 0 T)
        (F05FlowPrincipal A i h c) (F05FlowDrift A i h c) (W f) p =
        F05ModelPartition A χ i p.1*compatibleHolderFun f p-H f p

theorem F05_flow_patch_solvers {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {χ : Fin A.count → M.Carrier → ℝ}
    (hχ : F05Partition O A χ) (h : ℝ → HermitianField M) (c : M.Carrier → ℝ → ℝ)
    {S : ℝ} (hS : 0 < S) (hh : MetricFamilySmooth h (Icc 0 S))
    (hc : SmoothSpaceTime c (Icc 0 S)) (hPos : ∀ x t, t ∈ Icc 0 S → 0 < c x t)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ δ C E : ℝ, 0 < δ ∧ δ ≤ S ∧ δ ≤ 1 ∧ 0 < C ∧ 0 < E ∧
      ∀ (ρ T : ℝ), 0 < ρ → ρ ≤ 1 → 0 < T → T ≤ δ → T ≤ ρ^2 →
        ∀ i : Fin A.count, ∃ W H : compatibleHolderGraph α (F05ModelOpen A i) T → Point n → ℝ,
          F05ActualPatchData A χ h c α C E T ρ i W H := by
  obtain ⟨lam,upper,B,hB,hCoeff⟩ := F05_global_model_coefficients hA h c hS hh hc hPos hα hα1
  obtain ⟨δ,C,E,hδ,hδ1,hC,hE,hFactory⟩ := F05_atlas_physical_factories hA hχ
    (lam := lam) (upper := upper) hα hα1 hB.le
  refine ⟨min S δ,C,E,lt_min hS hδ,min_le_left _ _,(min_le_right _ _).trans hδ1,hC,hE,?_⟩
  intro ρ T hρ hρ1 hT hTδ hTρ i
  have hTS : T ≤ S := hTδ.trans (min_le_left _ _)
  have hBounds := hCoeff T hTS i
  obtain ⟨W,H,hAdd,hSmul,hH0,hWH⟩ := hFactory i ρ T
    (F05PrincipalExtension (F05FlowPrincipal A i h c))
    (F05DriftExtension (F05FlowDrift A i h c)) hρ hρ1 hT
    (hTδ.trans (min_le_right _ _)) hTρ hBounds.1 hBounds.2.1 hBounds.2.2
  refine ⟨W,H,hAdd,hSmul,hH0,?_⟩
  intro f
  obtain ⟨hW,hH⟩ := hWH f
  refine ⟨hW,hH,?_⟩
  intro p hp hn
  have hEq := hW.2.2.2.2 p hp
  have hExact := F05_coefficient_extension_exact
    (a := F05FlowPrincipal A i h c) (b := F05FlowDrift A i h c) hn
  simpa only [linearOp,hExact.1,hExact.2] using hEq

end Yau.Proofs.F05Aux
