import Yau.LeafProofs.L05AutonomousSpatialPeano

noncomputable section
open Filter Set MeasureTheory Asymptotics
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

theorem autoSpaceInnerBilin_apply {n : ℕ} (v w : Space n) : spaceInnerBilin n v w=inner ℝ v w := rfl

/-- A true second Peano expansion identifies the actual first spatial derivative. -/
theorem auto_spatial_peano_hasFDerivAt {n : ℕ} {f : Space n → ℝ} {x : Space n}
    {l : Space n →L[ℝ] ℝ} {B : Space n →L[ℝ] Space n →L[ℝ] ℝ}
    (h : autoSpatialPeanoJet f x l B) : HasFDerivAt f l x := by
  let R := fun y => f y-f x-l (y-x)-(1/2 : ℝ)*B (y-x) (y-x)
  have hR : HasFDerivAt R (0 : Space n →L[ℝ] ℝ) x :=
    h.2.isBigO.hasFDerivAt (by norm_num : 1 < (2 : ℕ))
  have hs : HasFDerivAt (fun y : Space n => y-x) (ContinuousLinearMap.id ℝ (Space n)) x :=
    (hasFDerivAt_id x).sub_const x
  have hQ : HasFDerivAt (fun y => (1/2 : ℝ)*B (y-x) (y-x)) (0 : Space n →L[ℝ] ℝ) x := by
    simpa using (B.hasFDerivAt_of_bilinear hs hs).const_mul (1/2 : ℝ)
  have hP := ((l.hasFDerivAt.comp x hs).add_const (f x)).add hQ
  convert hR.add hP using 1
  · funext y
    dsimp [R]
    ring
  · simp

/-- Subtracting the actual quadratic restores a Peano expansion for the original spatial slice. -/
theorem auto_spatial_semiconvex_peano {n : ℕ} {f : Space n → ℝ} {x : Space n} {C : ℝ}
    {l : Space n →L[ℝ] ℝ} {B : Space n →L[ℝ] Space n →L[ℝ] ℝ}
    (h : autoSpatialPeanoJet (fun y => f y+(C/2)*‖y‖^2) x l B) :
    autoSpatialPeanoJet f x (l-C • (spaceInnerBilin n x)) (B-C • spaceInnerBilin n) := by
  refine ⟨?_,?_⟩
  · intro v w
    simp only [sub_apply,smul_apply,smul_eq_mul,autoSpaceInnerBilin_apply]
    rw [h.1 v w,real_inner_comm v w]
  · have hNorm (y : Space n) : ‖y‖^2=‖x‖^2+2*inner ℝ x (y-x)+‖y-x‖^2 := by
      simp only [norm_sub_sq_real,inner_sub_right,real_inner_self_eq_norm_sq]
      rw [real_inner_comm y x]
      ring
    have heq : (fun y => f y-f x-(l-C • (spaceInnerBilin n x)) (y-x)-
        (1/2 : ℝ)*(B-C • spaceInnerBilin n) (y-x) (y-x))=
        (fun y => (f y+(C/2)*‖y‖^2)-(f x+(C/2)*‖x‖^2)-l (y-x)-
          (1/2 : ℝ)*B (y-x) (y-x)) := by
      funext y
      rw [hNorm y]
      simp only [sub_apply,smul_apply,smul_eq_mul,autoSpaceInnerBilin_apply,real_inner_self_eq_norm_sq]
      ring
    rw [heq]
    exact h.2

end Yau.LeafProofs.L05AutonomousAux
