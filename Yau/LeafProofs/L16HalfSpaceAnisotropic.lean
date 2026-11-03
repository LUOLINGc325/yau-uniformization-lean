import Yau.LeafProofs.L16HalfSpaceHeatSolver
import Yau.LeafProofs.L16ParametrixBounds
import Mathlib.Analysis.InnerProductSpace.Adjoint

open MeasureTheory Filter Set
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

local instance halfSpaceAnisotropic_dualGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance halfSpaceAnisotropic_dualSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance
local instance halfSpaceAnisotropic_bilinearGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance
local instance halfSpaceAnisotropic_bilinearSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance

/-- The actual normal of the half-space after the spatial change x = B y. -/
def halfSpacePullbackNormal {n : ℕ} (B : Space n ≃L[ℝ] Space n) (e : Space n) : Space n :=
  ‖(B : Space n →L[ℝ] Space n).adjoint e‖⁻¹ • (B : Space n →L[ℝ] Space n).adjoint e

theorem halfSpacePullbackNormal_adjoint_ne_zero {n : ℕ} (B : Space n ≃L[ℝ] Space n)
    {e : Space n} (he : ‖e‖ = 1) : (B : Space n →L[ℝ] Space n).adjoint e ≠ 0 := by
  intro hzero
  have hh := (B : Space n →L[ℝ] Space n).adjoint_inner_left (B.symm e) e
  rw [hzero,inner_zero_left] at hh
  change 0 = inner ℝ e (B (B.symm e)) at hh
  rw [B.apply_symm_apply] at hh
  have he0 : e = 0 := (inner_self_eq_zero (𝕜 := ℝ)).mp hh.symm
  rw [he0,norm_zero] at he
  norm_num at he

theorem halfSpacePullbackNormal_unit {n : ℕ} (B : Space n ≃L[ℝ] Space n)
    {e : Space n} (he : ‖e‖ = 1) : ‖halfSpacePullbackNormal B e‖ = 1 :=
  norm_smul_inv_norm (halfSpacePullbackNormal_adjoint_ne_zero B he)

theorem halfSpacePullbackNormal_inner {n : ℕ} (B : Space n ≃L[ℝ] Space n)
    {e : Space n} (he : ‖e‖ = 1) (y : Space n) :
    inner ℝ e (B y) = ‖(B : Space n →L[ℝ] Space n).adjoint e‖ *
      inner ℝ (halfSpacePullbackNormal B e) y := by
  have hw : ‖(B : Space n →L[ℝ] Space n).adjoint e‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (halfSpacePullbackNormal_adjoint_ne_zero B he)
  rw [halfSpacePullbackNormal,real_inner_smul_left,←mul_assoc,mul_inv_cancel₀ hw,one_mul]
  exact ((B : Space n →L[ℝ] Space n).adjoint_inner_left y e).symm

theorem halfSpacePullbackNormal_nonneg_iff {n : ℕ} (B : Space n ≃L[ℝ] Space n)
    {e : Space n} (he : ‖e‖ = 1) (y : Space n) :
    0 ≤ inner ℝ e (B y) ↔ 0 ≤ inner ℝ (halfSpacePullbackNormal B e) y := by
  rw [halfSpacePullbackNormal_inner B he]
  exact mul_nonneg_iff_of_pos_left (norm_pos_iff.mpr (halfSpacePullbackNormal_adjoint_ne_zero B he))

theorem halfSpacePullbackNormal_zero_iff {n : ℕ} (B : Space n ≃L[ℝ] Space n)
    {e : Space n} (he : ‖e‖ = 1) (y : Space n) :
    inner ℝ e (B y) = 0 ↔ inner ℝ (halfSpacePullbackNormal B e) y = 0 := by
  rw [halfSpacePullbackNormal_inner B he,mul_eq_zero]
  simp only [norm_ne_zero_iff.mpr (halfSpacePullbackNormal_adjoint_ne_zero B he),false_or]

/-- Source Holder bounds pull back using only values in the actual source set.
No Holder extension across the true lateral face is assumed. -/
theorem holderBound_comp_spaceLinearMap_on {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    {α T C : ℝ} {S S' : Set (Space n)} {f : Point n → E}
    (hα : 0 ≤ α) (L : Space n →L[ℝ] Space n) (hMap : MapsTo L S' S)
    (hf : HolderBound α (cylinder S 0 T) f C) :
    HolderBound α (cylinder S' 0 T) (fun p : Point n => f (L p.1,p.2)) (C*(1+‖L‖^α)) := by
  have hPow : 0 ≤ ‖L‖^α := Real.rpow_nonneg (norm_nonneg _) _
  have hFactor : 1 ≤ 1+‖L‖^α := by linarith
  have hQ (p : Point n) (hp : p ∈ cylinder S' 0 T) : (L p.1,p.2) ∈ cylinder S 0 T :=
    ⟨hMap hp.1,hp.2⟩
  refine ⟨mul_nonneg hf.1 (by positivity),?_,?_⟩
  · intro p hp
    exact (hf.2.1 _ (hQ p hp)).trans
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hFactor hf.1)
  · intro p hp q hq
    have hsp : ‖L p.1-L q.1‖^α ≤ ‖L‖^α*‖p.1-q.1‖^α := by
      rw [←map_sub]
      calc
        _ ≤ (‖L‖*‖p.1-q.1‖)^α := Real.rpow_le_rpow (norm_nonneg _) (L.le_opNorm _) hα
        _ = _ := Real.mul_rpow (norm_nonneg _) (norm_nonneg _)
    have hWeight : holderWeight α (L p.1,p.2) (L q.1,q.2) ≤
        (1+‖L‖^α)*holderWeight α p q := by
      unfold holderWeight
      calc
        _ ≤ ‖L‖^α*‖p.1-q.1‖^α+|p.2-q.2|^(α/2) := add_le_add hsp le_rfl
        _ ≤ (1+‖L‖^α)*‖p.1-q.1‖^α+(1+‖L‖^α)*|p.2-q.2|^(α/2) :=
          add_le_add
            (mul_le_mul_of_nonneg_right (by linarith : ‖L‖^α ≤ 1+‖L‖^α)
              (Real.rpow_nonneg (norm_nonneg _) _))
            (by simpa only [one_mul] using
              (mul_le_mul_of_nonneg_right hFactor (Real.rpow_nonneg (abs_nonneg _) _)))
        _ = _ := by ring
    exact (hf.2.2 _ (hQ p hp) _ (hQ q hq)).trans
      ((mul_le_mul_of_nonneg_left hWeight hf.1).trans_eq (by ring))

/-- The explicit constant-matrix solution obtained from the genuine flat solver.
B and its normalized adjoint normal depend only on the matrix and the face. -/
def halfSpaceConstantPullbackDuhamel {n : ℕ} (B : Space n ≃L[ℝ] Space n)
    (e : Space n) (T : ℝ) (f : Point n → ℝ) : Point n → ℝ :=
  spaceTimePullback B.symm (halfSpaceHeatDuhamel (halfSpacePullbackNormal B e) T (spaceTimePullback B f))

/-- Explicit B/e' transport, including full ambient C2/Schauder regularity,
actual half-space PDE and both zero faces. The constant precedes B,A,e,T,F,f. -/
theorem halfSpace_constantPullback_schauder_solution {n : ℕ} {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : Space n ≃L[ℝ] Space n) (A : Mat n),
      (∀ H : Space n →L[ℝ] Space n →L[ℝ] ℝ,
        (∑ k : Yau.RIdx n, H (B (Yau.realVec k)) (B (Yau.realVec k))) =
          ∑ i : Yau.RIdx n, ∑ j : Yau.RIdx n, A i j*H (Yau.realVec i) (Yau.realVec j)) →
      ∀ e : Space n, ‖e‖ = 1 → ∀ T F : ℝ, 0 < T → T ≤ 1 → ∀ f : Point n → ℝ,
      HolderBound α (cylinder {x | 0 ≤ inner ℝ e x} 0 T) f F →
      (∀ x : Space n, inner ℝ e x = 0 → f (x,0) = 0) →
      let u := halfSpaceConstantPullbackDuhamel B e T f
      SchauderBound α (cylinder univ 0 T) u (C*F*constantHeatNormFactor α B) ∧
      (∀ x : Space n, u (x,0) = 0) ∧
      (∀ x : Space n, inner ℝ e x = 0 → ∀ t ∈ Icc 0 T, u (x,t) = 0) ∧
      ∀ p ∈ cylinder {x | 0 ≤ inner ℝ e x} 0 T,
        linearOp (cylinder {x | 0 ≤ inner ℝ e x} 0 T) (fun _ => A) (fun _ _ => 0) u p = f p := by
  obtain ⟨C,hC,hSolve⟩ := halfSpace_heat_schauder_solution (n := n) hα hα1
  refine ⟨C,hC,?_⟩
  intro B A hContract e he T F hT hT1 f hf hCompat
  let e' := halfSpacePullbackNormal B e
  let g := spaceTimePullback B f
  let v := halfSpaceHeatDuhamel e' T g
  have hg : HolderBound α (cylinder {y | 0 ≤ inner ℝ e' y} 0 T) g
      (F*(1+‖(B : Space n →L[ℝ] Space n)‖^α)) :=
    holderBound_comp_spaceLinearMap_on hα.le (B : Space n →L[ℝ] Space n)
      (fun y hy => (halfSpacePullbackNormal_nonneg_iff B he y).mpr hy) hf
  have hCompatG : ∀ y : Space n, inner ℝ e' y = 0 → g (y,0) = 0 :=
    fun y hy => hCompat (B y) ((halfSpacePullbackNormal_zero_iff B he y).mpr hy)
  obtain ⟨hV,hV0,hVB,hVPDE⟩ := hSolve e' (halfSpacePullbackNormal_unit B he)
    T (F*(1+‖(B : Space n →L[ℝ] Space n)‖^α)) hT hT1 g hg hCompatG
  have hUp := SchauderBound_spaceTimePullback hα.le B.symm hV
  dsimp only
  refine ⟨?_,?_,?_,?_⟩
  · convert hUp using 1 <;> try rfl
    dsimp only [constantHeatNormFactor]
    ring
  · intro x
    exact hV0 (B.symm x)
  · intro x hx t ht
    apply hVB (B.symm x) _ t ht
    exact (halfSpacePullbackNormal_zero_iff B he (B.symm x)).mp (by simpa only [B.apply_symm_apply] using hx)
  · intro p hp
    change linearOp (cylinder {x | 0 ≤ inner ℝ e x} 0 T) (fun _ => A) (fun _ _ => 0)
      (spaceTimePullback B.symm v) p = f p
    rw [linearOp_cylinder_restrict_space _ _ _ hp,linearOp_spaceTimePullback_constant B hContract v T p]
    have hq : (B.symm p.1,p.2) ∈ cylinder {y | 0 ≤ inner ℝ e' y} 0 T :=
      ⟨(halfSpacePullbackNormal_nonneg_iff B he (B.symm p.1)).mp
        (by simpa only [B.apply_symm_apply] using (show 0 ≤ inner ℝ e p.1 from hp.1)),hp.2⟩
    rw [←linearOp_cylinder_restrict_space _ _ _ hq]
    simpa only [g,spaceTimePullback,ContinuousLinearEquiv.apply_symm_apply,Prod.eta] using hVPDE _ hq

/-- Uniform Dirichlet Schauder solvability for a genuine general constant
symmetric elliptic matrix, with the constant chosen before A and the unit face.
All original mixed normal/tangent coefficients remain in the actual PDE. -/
theorem halfSpace_constant_elliptic_schauder_solution {n : ℕ} {α lam upper : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hLam : 0 < lam) (hLamUpper : lam ≤ upper) :
    ∃ C : ℝ, 0 < C ∧ ∀ A : Mat n, A.IsSymm →
      (∀ z : Yau.RIdx n → ℝ,
        lam*(∑ i, (z i)^2) ≤ ∑ i, ∑ j, A i j*z i*z j ∧
          (∑ i, ∑ j, A i j*z i*z j) ≤ upper*(∑ i, (z i)^2)) →
      ∀ e : Space n, ‖e‖ = 1 → ∀ T F : ℝ, 0 < T → T ≤ 1 → ∀ f : Point n → ℝ,
      HolderBound α (cylinder {x | 0 ≤ inner ℝ e x} 0 T) f F →
      (∀ x : Space n, inner ℝ e x = 0 → f (x,0) = 0) →
      ∃ u : Point n → ℝ, SchauderBound α (cylinder univ 0 T) u (C*F) ∧
        (∀ x : Space n, u (x,0) = 0) ∧
        (∀ x : Space n, inner ℝ e x = 0 → ∀ t ∈ Icc 0 T, u (x,t) = 0) ∧
        ∀ p ∈ cylinder {x | 0 ≤ inner ℝ e x} 0 T,
          linearOp (cylinder {x | 0 ≤ inner ℝ e x} 0 T) (fun _ => A) (fun _ _ => 0) u p = f p := by
  obtain ⟨C0,hC0,hSolve⟩ := halfSpace_constantPullback_schauder_solution (n := n) hα hα1
  let N : ℝ := (1+(Real.sqrt upper)^α)*(1+(Real.sqrt lam)⁻¹)^2*(1+((Real.sqrt lam)⁻¹)^α)
  refine ⟨C0*N,by dsimp [N]; positivity,?_⟩
  intro A hSymm hForm e he T F hT hT1 f hf hCompat
  obtain ⟨B,hBN,hBI,hContract⟩ := elliptic_matrix_space_equiv A hLam hLamUpper hSymm hForm
  obtain ⟨hU,hU0,hUB,hUPDE⟩ := hSolve B A hContract e he T F hT hT1 f hf hCompat
  have hFactor : constantHeatNormFactor α B ≤ N := constantHeatNormFactor_le hα.le B hBN hBI
  have hBudget : C0*F*constantHeatNormFactor α B ≤ (C0*N)*F :=
    (mul_le_mul_of_nonneg_left hFactor (mul_nonneg hC0.le hf.1)).trans_eq (by ring)
  exact ⟨halfSpaceConstantPullbackDuhamel B e T f,schauderBound_mono_const hU hBudget,hU0,hUB,hUPDE⟩

end Yau.LeafProofs.L16Aux
