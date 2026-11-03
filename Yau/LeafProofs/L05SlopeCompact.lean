import Yau.LeafProofs.L05ViscosityPrimitives

noncomputable section

open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

def symInclusionLinear (n : ℕ) : Sym n →ₗ[ℝ] Mat n where
  toFun A := A
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def symInclusion (n : ℕ) : Sym n →L[ℝ] Mat n :=
  (symInclusionLinear n).mkContinuous 1 (fun A => by
    change ‖(A : Mat n)‖ ≤ 1*‖(A : Mat n)‖
    rw [one_mul])

local instance l05SlopeSymFiniteDimensional (n : ℕ) : FiniteDimensional ℝ (Sym n) :=
  FiniteDimensional.of_injective (symInclusionLinear n) Subtype.val_injective

local instance l05SlopeSymContinuousSMul (n : ℕ) : ContinuousSMul ℝ (Sym n) :=
  (show Topology.IsInducing (fun A : Sym n => (A : Mat n)) from ⟨rfl⟩).continuousSMul
    (f := fun c : ℝ => c) continuous_id (by intros; rfl)

def symEntry (n : ℕ) (i j : RIdx n) : Sym n →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ({toFun := fun A => (A : Mat n) i j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl} : Sym n →ₗ[ℝ] ℝ)

theorem slopeSet_isClosed (n : ℕ) (ell L : ℝ) : IsClosed (slopeSet n ell L) := by
  exact (Matrix.posSemidef_is_closed.preimage
    (continuous_subtype_val.sub continuous_const)).inter
    (Matrix.posSemidef_is_closed.preimage (continuous_const.sub continuous_subtype_val))

theorem slopeSet_isCompact (n : ℕ) {ell L : ℝ} (hell : 0 ≤ ell) :
    IsCompact (slopeSet n ell L) := by
  apply Metric.isCompact_of_isClosed_isBounded (slopeSet_isClosed n ell L)
  exact isBounded_iff_forall_norm_le.mpr ⟨(2*n)*L,fun _ hA => slopeSet_norm_le hell hA⟩

theorem slopeSet_convex (n : ℕ) (ell L : ℝ) : Convex ℝ (slopeSet n ell L) := by
  intro A hA B hB a b ha hb hab
  have hlow := (hA.1.smul ha).add (hB.1.smul hb)
  have hupp := (hA.2.smul ha).add (hB.2.smul hb)
  constructor
  · convert! hlow using 1
    change a • (A : Mat n)+b • (B : Mat n)-ell • (1 : Mat n)=
      a • ((A : Mat n)-ell • (1 : Mat n))+b • ((B : Mat n)-ell • (1 : Mat n))
    rw [smul_sub,smul_sub,smul_smul,smul_smul]
    have he : (a*ell) • (1 : Mat n)+(b*ell) • (1 : Mat n)=ell • (1 : Mat n) := by
      rw [← add_smul,← add_mul,hab,one_mul]
    rw [← he]
    abel
  · convert! hupp using 1
    change L • (1 : Mat n)-(a • (A : Mat n)+b • (B : Mat n))=
      a • (L • (1 : Mat n)-(A : Mat n))+b • (L • (1 : Mat n)-(B : Mat n))
    rw [smul_sub,smul_sub,smul_smul,smul_smul]
    have he : (a*L) • (1 : Mat n)+(b*L) • (1 : Mat n)=L • (1 : Mat n) := by
      rw [← add_smul,← add_mul,hab,one_mul]
    rw [← he]
    abel

theorem slopeSet_posDef {n : ℕ} {ell L : ℝ} (hell : 0 < ell)
    {A : Sym n} (hA : A ∈ slopeSet n ell L) : (A : Mat n).PosDef := by
  have hh := (Matrix.PosDef.one.smul hell).posSemidef_add hA.1
  simpa only [sub_add_cancel] using hh

end Yau.LeafProofs.L05Aux
