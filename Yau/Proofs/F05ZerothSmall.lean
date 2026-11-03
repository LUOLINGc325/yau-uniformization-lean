import Yau.Proofs.F05ActualSourceLinear
import Yau.Proofs.F05CanonicalSmallHolder
import Yau.Proofs.F05CanonicalLinear
import Yau.Proofs.F05LinearCoefficients

/-! A fixed smooth zeroth-order coefficient is a genuinely small operator
on the homogeneous initial jet space. The original physical norm is retained. -/

open Set
noncomputable section
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

def F05MultiplyActualLinear (q : M.Carrier → ℝ → ℝ) :
    (M.Carrier → ℝ → ℝ) →ₗ[ℝ] (M.Carrier → ℝ → ℝ) where
  toFun := fun f x t => q x t*f x t
  map_add' f g := by funext x t; exact mul_add _ _ _
  map_smul' d f := by funext x t; simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply]; ring

theorem F05_scalar_holder_uniform {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (q : M.Carrier → ℝ → ℝ)
    {S : ℝ} (hS : 0 < S) (hq : SmoothSpaceTime q (Icc 0 S)) :
    ∃ B : ℝ, 0 < B ∧ ∀ (α : ℝ), 0 < α → α < 1 → ∀ (T : ℝ), T ≤ S →
      ∀ i : Fin A.count, HolderBound α (F05Q A i T) (pull A i q) B := by
  classical
  have hEach (i : Fin A.count) := F05_compact_cylinder_holder Metric.isOpen_ball
    (isCompact_closedBall (0 : Space n) 2) (convex_closedBall (0 : Space n) 2)
    (Metric.closedBall_subset_ball (by norm_num : (2 : ℝ) < 3)) hS
    (F05_pull_spacetime_smooth hA q hq i)
  choose C hC hEach using hEach
  let B := 1+∑ i,C i
  have hSum : 0 ≤ ∑ i,C i := Finset.sum_nonneg (fun i _ => (hC i).le)
  refine ⟨B,by dsimp only [B]; positivity,?_⟩
  intro α hα hα1 T hTS i
  have hCB : C i ≤ B := by
    have hh := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin A.count))) => (hC j).le)
      (Finset.mem_univ i)
    dsimp only [B]
    linarith
  apply holderBound_mono_const (holderBound_mono (hEach i α hα hα1 T hTS) ?_) hCB
  intro p hp
  exact ⟨by simpa only [Metric.mem_closedBall,dist_zero_right] using hp.1.1,hp.2⟩

theorem F05_zeroth_small_operator {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {χ : Fin A.count → M.Carrier → ℝ} (hχ : F05Partition O A χ)
    (q : M.Carrier → ℝ → ℝ) {S : ℝ} (hS : 0 < S) (hq : SmoothSpaceTime q (Icc 0 S))
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ρ T : ℝ) (hT : 0 < T),
      0 < ρ → ρ ≤ 1 → T ≤ ρ^2 → T ≤ S →
      ∃ Z : F05CompatibleJetGraph A α hT.le →L[ℝ] F05SourceZeroGraph A α T,
        ‖Z‖ ≤ C*ρ^(1-α) ∧ ∀ u (i : Fin A.count) (p : F05Q A i T),
          holderGraphFun ((Z u).val i) p.val =
            q (lift A i p.val.1) p.val.2*F05CanonicalJetFunction A χ α hT.le u (lift A i p.val.1) p.val.2 := by
  obtain ⟨B,hB,hqHolder⟩ := F05_scalar_holder_uniform hA q hS hq
  obtain ⟨G,hG,hLow⟩ := F05_canonical_small_lower_holder hA hχ hα hα1
  refine ⟨2*B*G,by positivity,?_⟩
  intro ρ T hT hρ hρ1 hTρ hTS
  let C := 2*B*G*ρ^(1-α)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  let F := (F05MultiplyActualLinear q).comp (F05CanonicalJetLinear A χ α hT.le)
  have hFEval (u : F05CompatibleJetGraph A α hT.le) (x : M.Carrier) (t : ℝ) :
      F u x t = q x t*F05CanonicalJetFunction A χ α hT.le u x t := by
    change q x t*F05CanonicalJetLinear A χ α hT.le u x t = _
    rw [F05CanonicalJetLinear_apply]
  have hFHolder (u : F05CompatibleJetGraph A α hT.le) (i : Fin A.count) :
      HolderBound α (F05Q A i T) (pull A i (F u)) (C*‖u‖) := by
    have hh := holderBound_mul (hqHolder α hα hα1 T hTS i)
      (holderBound_fst (hLow ρ T hT hρ hρ1 hTρ u i))
    have hCong : EqOn (fun p => pull A i q p*F05CanonicalPull A χ α hT.le u i p)
        (pull A i (F u)) (F05Q A i T) := by
      intro p hp
      exact (hFEval u (lift A i p.1) p.2).symm
    convert holderBound_congr_on hh hCong using 1
    dsimp only [C]
    ring
  have hF0 (u : F05CompatibleJetGraph A α hT.le) (x : M.Carrier) (_ : x ∈ closure O) : F u x 0 = 0 := by
    rw [hFEval,F05CanonicalJetFunction_initial,mul_zero]
  let Z := F05ActualSourceLinear hA hα hT.le hC F hFHolder hF0
  refine ⟨Z,F05ActualSourceLinear_norm_le hA hα hT.le hC F hFHolder hF0,?_⟩
  intro u i p
  exact (F05ActualSourceLinear_eval hA hα hT.le hC F hFHolder hF0 u i p).trans (hFEval u _ _)

end Yau.Proofs.F05Aux
