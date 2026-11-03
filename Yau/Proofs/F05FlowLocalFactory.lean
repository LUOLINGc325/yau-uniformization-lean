import Yau.Proofs.F05UniformCoefficients
import Yau.Proofs.F05PartitionModel
import Yau.Proofs.F05SpatialCutoffHolder

/-! The actual atlas has one native physical factory budget before every
short time interval and every source. The coefficients stay variable. -/

open Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_physical_factory_mono {O : Set (Space n)}
    {α lam upper B δ δ' C C' E E' : ℝ} {ψ : Space n → ℝ}
    (h : F05AllInitialPhysicalFactory O α lam upper B ψ δ C E)
    (hδ : δ' ≤ δ) (hC : C ≤ C') (hE : E ≤ E') :
    F05AllInitialPhysicalFactory O α lam upper B ψ δ' C' E' := by
  intro ρ T a b hρ hρ1 hT hTδ hTρ hEll ha hb
  obtain ⟨W,H,hAdd,hSmul,hH0,hWH⟩ :=
    h ρ T a b hρ hρ1 hT (hTδ.trans hδ) hTρ hEll ha hb
  refine ⟨W,H,hAdd,hSmul,hH0,?_⟩
  intro f
  obtain ⟨⟨hHigh,hLow,hW0,hWB,hEq⟩,hHH⟩ := hWH f
  have hCN : C*‖f‖ ≤ C'*‖f‖ := mul_le_mul_of_nonneg_right hC (norm_nonneg _)
  have hEN : E*‖f‖ ≤ E'*‖f‖ := mul_le_mul_of_nonneg_right hE (norm_nonneg _)
  have hp : 0 ≤ ρ^(1-α) := Real.rpow_nonneg hρ.le _
  exact ⟨⟨schauderBound_mono_const hHigh hCN,
    holderBound_mono_const hLow (mul_le_mul_of_nonneg_right hCN hp),hW0,hWB,hEq⟩,
    holderBound_mono_const hHH (mul_le_mul_of_nonneg_right hEN hp)⟩

theorem F05_atlas_physical_factories {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {χ : Fin A.count → M.Carrier → ℝ}
    (hχ : F05Partition O A χ) {α lam upper B : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hB : 0 ≤ B) :
    ∃ δ C E : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < C ∧ 0 < E ∧
      ∀ i : Fin A.count, F05AllInitialPhysicalFactory (F05ModelOpen A i)
        α lam upper B (F05ModelPartition A χ i) δ C E := by
  classical
  have hFactory (i : Fin A.count) :
      ∃ δ C E : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < C ∧ 0 < E ∧
        F05AllInitialPhysicalFactory (F05ModelOpen A i)
          α lam upper B (F05ModelPartition A χ i) δ C E := by
    have hSmooth := F05ModelPartition_contDiff hA hχ i
    have hCompact : HasCompactSupport (F05ModelPartition A χ i) :=
      HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Space n) (1/4))
        ((subset_tsupport _).trans (F05ModelPartition_tsupport hA hχ i))
    obtain ⟨P,hP,hHolder⟩ := F05_smooth_compact_spatial_holder hSmooth hCompact
    exact F05_flat_physical_factory (A.normal i) hα hα1 hB hP.le
      (F05ModelPartition A χ i)
      (holderBound_mono (hHolder α hα hα1) (subset_univ _))
      (F05ModelPartition_tsupport hA hχ i)
  choose δ C E hδ hδ1 hC hE hF using hFactory
  let I := ∑ i, (δ i)⁻¹
  let δ₀ := min 1 (1/(1+I))
  let C₀ := 1+∑ i,C i
  let E₀ := 1+∑ i,E i
  have hI : 0 ≤ I := Finset.sum_nonneg (fun i _ => inv_nonneg.mpr (hδ i).le)
  have hCsum : 0 ≤ ∑ i,C i := Finset.sum_nonneg (fun i _ => (hC i).le)
  have hEsum : 0 ≤ ∑ i,E i := Finset.sum_nonneg (fun i _ => (hE i).le)
  have hδ₀ : 0 < δ₀ := by dsimp only [δ₀]; positivity
  have hC₀ : 0 < C₀ := by dsimp only [C₀]; positivity
  have hE₀ : 0 < E₀ := by dsimp only [E₀]; positivity
  refine ⟨δ₀,C₀,E₀,hδ₀,min_le_left _ _,hC₀,hE₀,?_⟩
  intro i
  have hδi : δ₀ ≤ δ i := by
    have hi : (δ i)⁻¹ ≤ I := Finset.single_le_sum
      (fun j (_ : j ∈ (Finset.univ : Finset (Fin A.count))) => inv_nonneg.mpr (hδ j).le)
      (Finset.mem_univ i)
    calc
      δ₀ ≤ 1/(1+I) := min_le_right _ _
      _ ≤ 1/((δ i)⁻¹) := one_div_le_one_div_of_le (inv_pos.mpr (hδ i)) (by linarith)
      _ = δ i := by rw [one_div,inv_inv]
  have hCi : C i ≤ C₀ := by
    have hi := Finset.single_le_sum
      (fun j (_ : j ∈ (Finset.univ : Finset (Fin A.count))) => (hC j).le) (Finset.mem_univ i)
    dsimp only [C₀]
    linarith
  have hEi : E i ≤ E₀ := by
    have hi := Finset.single_le_sum
      (fun j (_ : j ∈ (Finset.univ : Finset (Fin A.count))) => (hE j).le) (Finset.mem_univ i)
    dsimp only [E₀]
    linarith
  exact F05_physical_factory_mono (hF i) hδi hCi hEi

end Yau.Proofs.F05Aux
