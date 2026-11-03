import Yau.Proofs.E02ProjectorWirtinger
import Yau.Proofs.E02TangentMixed

open Matrix Filter
open scoped Topology ContDiff Matrix ComplexOrder Matrix.Norms.Elementwise
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-- The genuine barred Wirtinger derivative of S, with fixed Z. -/
theorem projectorTangent_wirtBar_of_inverseGram {n m : ℕ} (M Z : Rect n m)
    (hM : (M*Mᴴ).PosDef)
    (hInv : DifferentiableAt ℝ (fun N : Rect n m => (N*Nᴴ)⁻¹) M) (i j : Fin m) :
    wirtBar (fun N : Rect n m => projectorTangent N Z i j) M Z =
      ((projectorTangent M Z)ᴴ*projectorTangent M Z-
        projectorTangent M Z*(projectorTangent M Z)ᴴ) i j := by
  have hS := projectorTangent_differentiableAt_of_inverseGram M Z hInv
  rw [wirtBar,fderiv_matrix_entry _ M Z hS i j,
    fderiv_matrix_entry _ M (Complex.I • Z) hS i j]
  have h := congrArg (fun A : Herm m => A i j)
    (projectorTangent_mixed_real_derivatives M Z hM hInv)
  simp only [Matrix.smul_apply,Matrix.add_apply,smul_eq_mul] at h
  convert h using 1
  rfl

/-- The original nested Wirtinger derivative of the explicit projector
is SᴴS−SSᴴ. Near-point differentiability of its actual inverse is enough;
it is later supplied by the smooth inverse on the open full-rank locus. -/
theorem rowProjector_wirt_wirtBar_of_inverseGram {n m : ℕ} (M Z : Rect n m)
    (hM : (M*Mᴴ).PosDef)
    (hInv : ∀ᶠ N in 𝓝 M, DifferentiableAt ℝ (fun N : Rect n m => (N*Nᴴ)⁻¹) N)
    (i j : Fin m) :
    wirt (fun N : Rect n m => wirtBar (fun A : Rect n m => rowProjector A i j) N Z) M Z =
      ((projectorTangent M Z)ᴴ*projectorTangent M Z-
        projectorTangent M Z*(projectorTangent M Z)ᴴ) i j := by
  have hAt := hInv.self_of_nhds
  have hEq : (fun N : Rect n m => wirtBar (fun A : Rect n m => rowProjector A i j) N Z)
      =ᶠ[𝓝 M] (fun N : Rect n m => star (projectorTangent N Z j i)) := by
    filter_upwards [hInv,(isOpen_fullRankRect n m).mem_nhds
      ((fullRankRect_iff_posDef M).mpr hM)] with N hN hRank
    exact rowProjector_wirtBar_of_inverseGram N Z ((fullRankRect_iff_posDef N).mp hRank) hN i j
  have hConj : wirt (fun N : Rect n m => star (projectorTangent N Z j i)) M Z =
      star (wirtBar (fun N : Rect n m => projectorTangent N Z j i) M Z) := by
    unfold wirt wirtBar
    rw [fderiv_star]
    change (1/2 : ℂ)*(star (fderiv ℝ (fun N : Rect n m => projectorTangent N Z j i) M Z)-
        Complex.I*star (fderiv ℝ (fun N : Rect n m => projectorTangent N Z j i) M (Complex.I • Z))) =
      star ((1/2 : ℂ)*(fderiv ℝ (fun N : Rect n m => projectorTangent N Z j i) M Z+
        Complex.I*fderiv ℝ (fun N : Rect n m => projectorTangent N Z j i) M (Complex.I • Z)))
    have hHalf : star (1/2 : ℂ) = (1/2 : ℂ) := by norm_num [Complex.star_def]
    have hI : star Complex.I = -Complex.I := by simp [Complex.star_def]
    simp only [star_mul,star_add,hHalf,hI]
    ring
  have hBar := projectorTangent_wirtBar_of_inverseGram M Z hM hAt j i
  have hH : ((projectorTangent M Z)ᴴ*projectorTangent M Z-
      projectorTangent M Z*(projectorTangent M Z)ᴴ).IsHermitian :=
    (Matrix.posSemidef_conjTranspose_mul_self _).isHermitian.sub
      (Matrix.posSemidef_self_mul_conjTranspose _).isHermitian
  have hEntry := congrArg (fun A : Herm m => A i j) hH.eq
  have hSame :
      wirt (fun N : Rect n m => wirtBar (fun A : Rect n m => rowProjector A i j) N Z) M Z =
        wirt (fun N : Rect n m => star (projectorTangent N Z j i)) M Z := by
    unfold wirt
    erw [hEq.fderiv_eq (𝕜 := ℝ)]
    rfl
  exact hSame.trans (hConj.trans ((congrArg star hBar).trans hEntry))

end Yau.NodeProofs.E02Aux
