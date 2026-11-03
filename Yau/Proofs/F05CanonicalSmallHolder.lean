import Yau.Proofs.F05CanonicalLowerHolder
import Yau.Proofs.F05FiniteManifoldPatch
import Yau.LeafProofs.L16ZeroInitialSchauderJets

/-! The actual homogeneous initial slice gives a genuinely small lower-jet
Holder operator norm on all full physical charts, with constants before time. -/

open Set
noncomputable section
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_canonical_small_lower_holder {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {χ : Fin A.count → M.Carrier → ℝ} (hχ : F05Partition O A χ)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ρ T : ℝ) (hT : 0 < T), 0 < ρ → ρ ≤ 1 → T ≤ ρ^2 →
      ∀ u : F05CompatibleJetGraph A α hT.le, ∀ i : Fin A.count,
        HolderBound α (F05Q A i T)
          (fun p => (F05CanonicalPull A χ α hT.le u i p,
            spatialD (F05CanonicalPull A χ α hT.le u i) p)) (C*‖u‖*ρ^(1-α)) := by
  classical
  choose β hβ hRange hSupport hOne using (fun j : Fin A.count => F05_outer_manifold_cutoff hA j)
  choose H hH hHigh using (fun j : Fin A.count => F05_local_extension_schauder_budget A j
    (F05ModelPartition A χ j) (F05ModelPartition_contDiff hA hχ j)
    (F05ModelPartition_tsupport hA hχ j) α hα hα1)
  let H₀ := 1+∑ j,H j
  have hHSum : 0 ≤ ∑ j,H j := Finset.sum_nonneg (fun j _ => (hH j).le)
  have hH₀ : 0 < H₀ := by dsimp only [H₀]; positivity
  have hHH (j : Fin A.count) : H j ≤ H₀ := by
    have hh := Finset.single_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin A.count))) => (hH k).le)
      (Finset.mem_univ j)
    dsimp only [H₀]
    linarith
  obtain ⟨G,hG,hGlue⟩ := F05_finite_manifold_patch_budget hA β hβ hSupport hα hα1
  refine ⟨16*G*H₀,by positivity,?_⟩
  intro ρ T hT hρ hρ1 hTρ u i
  have hT1 : T ≤ 1 := by nlinarith [mul_nonneg hρ.le (sub_nonneg.mpr hρ1)]
  let U (j : Fin A.count) : Point n → ℝ := F05LocalJetExtension A j (F05ModelPartition A χ j) (u.val j).val
  have hNorm (j : Fin A.count) : ‖(u.val j).val‖ ≤ ‖u‖ := by
    change ‖u.val j‖ ≤ ‖u.val‖
    exact norm_le_pi_norm u.val j
  have hUpper (j : Fin A.count) : SchauderBound α (cylinder univ 0 T) (U j) (H₀*‖u‖) := by
    let uj : F05LocalFTCGraph A j α hT.le := ⟨(u.val j).val,(u.val j).property.1.1.1⟩
    apply schauderBound_mono_const (hHigh j T hT uj)
    exact mul_le_mul (hHH j) (hNorm j) (norm_nonneg _) hH₀.le
  have hU0 (j : Fin A.count) (z : Space n) : U j (z,0) = 0 :=
    F05_local_extension_initial_value A j α hT.le (u.val j) (F05ModelPartition A χ j) z
  have hLow (j : Fin A.count) : HolderBound α (cylinder univ 0 T)
      (fun p => (U j p,spatialD (U j) p)) (16*(H₀*‖u‖)*ρ^(1-α)) :=
    zero_initial_schauder_lowPair_small hα hα1 hT hρ hρ1 hTρ (hUpper j) (hU0 j)
  have hBounds := hGlue T (H₀*‖u‖) (16*(H₀*‖u‖)*ρ^(1-α)) U hT1 (by positivity) (by positivity)
    hUpper hLow i
  let v : Point n → ℝ := pull A i (F05CutoffReconstruction A χ β α hT.le u)
  let ui : F05LocalFTCGraph A i α hT.le := ⟨(u.val i).val,(u.val i).property.1.1.1⟩
  have hValue : EqOn v (F05BCFFun (u.val i).val.1) (F05Q A i T) := by
    intro p hp
    exact (F05CutoffReconstruction_eq hA hχ β hSupport hOne α hT.le u
      (F05D_lift_mem_closure hA hp.1) p.2).trans
        (F05CanonicalJetFunction_value hA hχ α hT.le u i hp.1 hp.2)
  have hReal := F05LocalFTCGraph_realization A i α hT ui v hValue
    (fun p hp => hBounds.1.1.2.2.2.2.1 p hp)
  have hCanonical := F05CanonicalJetFunction_realizes hA hχ α hT u i
  have hLowV : HolderBound α (F05Q A i T) (fun p => (v p,spatialD v p))
      (G*(16*(H₀*‖u‖)*ρ^(1-α))) := hBounds.2
  have hActual := holderBound_congr_on (g := fun p => (F05CanonicalPull A χ α hT.le u i p,
      spatialD (F05CanonicalPull A χ α hT.le u i) p)) hLowV (fun p hp =>
    Prod.ext (F05CutoffReconstruction_eq hA hχ β hSupport hOne α hT.le u
      (F05D_lift_mem_closure hA hp.1) p.2) ((hReal.2.1 hp).trans (hCanonical.2.1 hp).symm))
  convert hActual using 1
  ring

end Yau.Proofs.F05Aux
