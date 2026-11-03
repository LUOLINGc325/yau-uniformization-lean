import spec.CHAIN.CONTRACTS

/-! An explicit holomorphic quadratic coordinate change with identity
linear part. This supplies actual local inverses for the normal-jet change. -/
noncomputable section
open scoped ContDiff
namespace Yau.NodeProofs.F01Aux
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def quadraticCoordinate (B : E →L[ℂ] E →L[ℂ] E) (z : E) : E :=
  z + (1 / 2 : ℂ) • B z z

theorem quadraticCoordinate_zero (B : E →L[ℂ] E →L[ℂ] E) :
    quadraticCoordinate B 0 = 0 := by simp [quadraticCoordinate]

theorem quadraticCoordinate_contDiff (B : E →L[ℂ] E →L[ℂ] E) :
    ContDiff ℂ ∞ (quadraticCoordinate B) :=
  contDiff_id.add ((B.contDiff.clm_apply contDiff_id).const_smul (1 / 2 : ℂ))

theorem quadraticCoordinate_hasFDerivAt_zero (B : E →L[ℂ] E →L[ℂ] E) :
    HasFDerivAt (quadraticCoordinate B) (ContinuousLinearMap.id ℂ E) 0 := by
  have hq : HasFDerivAt (fun z : E => B z z) (0 : E →L[ℂ] E) 0 := by
    convert B.hasFDerivAt.clm_apply (hasFDerivAt_id (0 : E)) using 1 <;>
      ext v <;> simp [ContinuousLinearMap.flip_apply]
  change HasFDerivAt (fun z : E => z + (1 / 2 : ℂ) • B z z)
    (ContinuousLinearMap.id ℂ E) 0
  simpa only [Pi.add_def, Pi.smul_def, id_eq,
    smul_zero, add_zero] using
      (hasFDerivAt_id (0 : E)).add (hq.const_smul (1 / 2 : ℂ))

theorem quadraticCoordinate_local_inverse [CompleteSpace E]
    (B : E →L[ℂ] E →L[ℂ] E) :
    ∃ e : OpenPartialHomeomorph E E,
      (e : E → E) = quadraticCoordinate B ∧ (0 : E) ∈ e.source ∧
      e 0 = 0 ∧ ContDiffAt ℂ ∞ e.symm 0 := by
  let f' := ContinuousLinearEquiv.refl ℂ E
  have hd : HasFDerivAt (quadraticCoordinate B) (f' : E →L[ℂ] E) 0 :=
    quadraticCoordinate_hasFDerivAt_zero B
  have hc : ContDiffAt ℂ ∞ (quadraticCoordinate B) 0 :=
    (quadraticCoordinate_contDiff B).contDiffAt
  let e := hc.toOpenPartialHomeomorph (quadraticCoordinate B) hd (by simp)
  refine ⟨e, rfl, hc.mem_toOpenPartialHomeomorph_source hd (by simp),
    quadraticCoordinate_zero B, ?_⟩
  have hi := hc.to_localInverse hd (by simp)
  change ContDiffAt ℂ ∞ (hc.localInverse hd (by simp)) 0
  simpa only [quadraticCoordinate_zero] using hi

end Yau.NodeProofs.F01Aux
