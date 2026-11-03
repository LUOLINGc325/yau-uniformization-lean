import Yau.Proofs.F05HolderTimeAffine

/-! Exact scalar linearity of the native parabolic jets and their genuine
Schauder budgets. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_holder_const_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {α C : ℝ} {Q : Set (Point n)} {u : Point n → E}
    (hu : HolderBound α Q u C) (c : ℝ) :
    HolderBound α Q (fun p => c • u p) (|c| * C) := by
  refine ⟨mul_nonneg (abs_nonneg _) hu.1,?_,?_⟩
  · intro p hp
    simpa only [norm_smul,Real.norm_eq_abs] using
      mul_le_mul_of_nonneg_left (hu.2.1 p hp) (abs_nonneg c)
  · intro p hp q hq
    rw [← smul_sub,norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (hu.2.2 p hp q hq) (abs_nonneg c)).trans_eq
      (by ring)

theorem F05_spatial_const_mul_jets (c : ℝ) (u : Point n → ℝ) (p : Point n) :
    spatialD (fun z => c*u z) p = c • spatialD u p ∧
      spatialDD (fun z => c*u z) p = c • spatialDD u p := by
  have hD (x : Space n) : fderiv ℝ (fun y => c*u (y,p.2)) x =
      c • fderiv ℝ (fun y => u (y,p.2)) x :=
    congrFun (fderiv_const_smul_field (𝕜 := ℝ) (f := fun y => u (y,p.2)) c) x
  refine ⟨hD p.1,?_⟩
  unfold spatialDD
  simp_rw [hD]
  exact congrFun (fderiv_const_smul_field (𝕜 := ℝ)
    (f := fun x => fderiv ℝ (fun y => u (y,p.2)) x) c) p.1

theorem F05_schauder_const_mul {α C : ℝ} {Q : Set (Point n)} {u : Point n → ℝ}
    (hu : SchauderBound α Q u C) (c : ℝ) :
    SchauderBound α Q (fun p => c*u p) (|c| * C) := by
  have hJets := F05_spatial_const_mul_jets c u
  have hTime (p : Point n) : timeD Q (fun z => c*u z) p = c*timeD Q u p :=
    timeD_spatial_mul Q (fun _ => c) u p
  refine ⟨c2_const_smul hu.1 c,mul_nonneg (abs_nonneg c) hu.2.1,?_,?_,?_⟩
  · intro p hp
    rw [(hJets p).1,abs_mul,norm_smul,Real.norm_eq_abs]
    exact ⟨mul_le_mul_of_nonneg_left (hu.2.2.1 p hp).1 (abs_nonneg c),
      mul_le_mul_of_nonneg_left (hu.2.2.1 p hp).2 (abs_nonneg c)⟩
  · exact holderBound_congr_on (F05_holder_const_smul hu.2.2.2.1 c)
      (fun p _ => (hJets p).2.symm)
  · exact holderBound_congr_on (F05_holder_const_smul hu.2.2.2.2 c)
      (fun p _ => (hTime p).symm)

theorem F05_schauder_sub {α C D : ℝ} {Q : Set (Point n)} {u v : Point n → ℝ}
    (hu : SchauderBound α Q u C) (hv : SchauderBound α Q v D) :
    SchauderBound α Q (fun p => u p-v p) (C+D) := by
  refine ⟨c2_sub hu.1 hv.1,add_nonneg hu.2.1 hv.2.1,?_,?_,?_⟩
  · intro p hp
    rw [spatialD_sub hu.1 hv.1 hp]
    exact ⟨(abs_sub (u p) (v p)).trans (add_le_add (hu.2.2.1 p hp).1 (hv.2.2.1 p hp).1),
      (norm_sub_le _ _).trans (add_le_add (hu.2.2.1 p hp).2 (hv.2.2.1 p hp).2)⟩
  · exact holderBound_congr_on (holderBound_sub hu.2.2.2.1 hv.2.2.2.1)
      (fun p hp => (spatialDD_sub hu.1 hv.1 hp).symm)
  · exact holderBound_congr_on (holderBound_sub hu.2.2.2.2 hv.2.2.2.2)
      (fun p hp => (timeD_sub hu.1 hv.1 hp).symm)

end Yau.Proofs.F05Aux
