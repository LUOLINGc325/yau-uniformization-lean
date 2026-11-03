import Yau.LeafProofs.L05SlopeCompact

noncomputable section

open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

local instance l05LogDetSymContinuousSMul (n : ℕ) : ContinuousSMul ℝ (Sym n) :=
  (show Topology.IsInducing (fun A : Sym n => (A : Mat n)) from ⟨rfl⟩).continuousSMul
    (f := fun c : ℝ => c) continuous_id (by intros; rfl)

def logDetDomain (n : ℕ) : Set (Sym n) := {A | (A : Mat n).det ≠ 0}

theorem sym_det_contDiff (n : ℕ) : ContDiff ℝ ∞ (fun A : Sym n => (A : Mat n).det) := by
  apply contDiffOn_univ.mp
  exact L18Aux.contDiffOn_matrix_det (fun i j => (symEntry n i j).contDiff.contDiffOn)

theorem logDetDomain_isOpen (n : ℕ) : IsOpen (logDetDomain n) :=
  isOpen_ne.preimage (sym_det_contDiff n).continuous

theorem slopeSet_subset_logDetDomain {n : ℕ} {ell L : ℝ} (hell : 0 < ell) :
    slopeSet n ell L ⊆ logDetDomain n :=
  fun _ hA => (slopeSet_posDef hell hA).det_pos.ne'

theorem logDetReal_contDiffOn (n : ℕ) : ContDiffOn ℝ ∞ (@logDetReal n) (logDetDomain n) := by
  exact contDiffOn_const.mul ((sym_det_contDiff n).contDiffOn.log (fun _ hA => hA))

theorem symEntry_fderiv {n : ℕ} (A V : Sym n) (i j : RIdx n) :
    fderiv ℝ (fun B : Sym n => (B : Mat n) i j) A V=(V : Mat n) i j := by
  change fderiv ℝ (symEntry n i j) A V=(V : Mat n) i j
  rw [(symEntry n i j).fderiv]
  rfl

theorem logDetReal_fderiv {n : ℕ} {A : Sym n} (hA : A ∈ logDetDomain n) (V : Sym n) :
    fderiv ℝ (@logDetReal n) A V=(1/2:ℝ)*Matrix.trace ((A : Mat n)⁻¹*(V : Mat n)) := by
  have hentry (i j : RIdx n) : DifferentiableAt ℝ (fun B : Sym n => (B : Mat n) i j) A :=
    (symEntry n i j).differentiableAt
  have hd : DifferentiableAt ℝ (fun B : Sym n => (B : Mat n).det) A :=
    (sym_det_contDiff n).differentiable (by simp) A
  have hl := ((hd.hasFDerivAt.log hA).const_mul (1/2:ℝ)).fderiv
  have he : fderiv ℝ (@logDetReal n) A V=
      (1/2:ℝ)*((A : Mat n).det⁻¹*fderiv ℝ (fun B : Sym n => (B : Mat n).det) A V) := by
    convert! congrArg (fun D : Sym n →L[ℝ] ℝ => D V) hl using 1
  rw [he]
  have hj : fderiv ℝ (fun B : Sym n => (B : Mat n).det) A V=(A : Mat n).det*
      Matrix.trace ((A : Mat n)⁻¹*(Matrix.of fun i j => fderiv ℝ (fun B : Sym n => (B : Mat n) i) A V j)) := by
    convert! L18Aux.fderiv_matrix_det_trace hentry hA V using 1
  rw [hj]
  have hrows : (Matrix.of fun i j => fderiv ℝ (fun B : Sym n => (B : Mat n) i) A V j)=(V : Mat n) := by
    ext i j
    change fderiv ℝ (fun B : Sym n => (B : Mat n) i) A V j=(V : Mat n) i j
    calc
      _=fderiv ℝ (fun B : Sym n => (B : Mat n) i j) A V := by
        convert! L18Aux.fderiv_matrix_row_apply hentry V i j using 1
      _=_ := symEntry_fderiv A V i j
  rw [hrows]
  have hdet : (A : Mat n).det ≠ 0 := hA
  field_simp

end Yau.LeafProofs.L05Aux
