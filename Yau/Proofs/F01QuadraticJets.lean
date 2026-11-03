import Yau.Proofs.F01QuadraticCoordinate

/-! The exact first and second complex jets of the explicit quadratic
coordinate change, as genuine Fréchet derivatives. -/
noncomputable section
namespace Yau.NodeProofs.F01Aux
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem quadraticCoordinate_hasFDerivAt (B : E →L[ℂ] E →L[ℂ] E) (z : E) :
    HasFDerivAt (quadraticCoordinate B)
      (ContinuousLinearMap.id ℂ E + (1 / 2 : ℂ) • (B z + B.flip z)) z := by
  have hq : HasFDerivAt (fun w : E => B w w) (B z + B.flip z) z := by
    simpa only [ContinuousLinearMap.comp_id, id_eq] using
      B.hasFDerivAt.clm_apply (hasFDerivAt_id z)
  change HasFDerivAt (fun w : E => w + (1 / 2 : ℂ) • B w w) _ z
  simpa only [Pi.add_def, Pi.smul_def, id_eq] using
    (hasFDerivAt_id z).add (hq.const_smul (1 / 2 : ℂ))

theorem quadraticCoordinate_secondFDeriv (B : E →L[ℂ] E →L[ℂ] E) (z v w : E) :
    fderiv ℂ (fderiv ℂ (quadraticCoordinate B)) z v w =
      (1 / 2 : ℂ) • (B v w + B w v) := by
  have he : fderiv ℂ (quadraticCoordinate B) =
      (fun a => ContinuousLinearMap.id ℂ E + (1 / 2 : ℂ) • (B a + B.flip a)) :=
    funext fun a => (quadraticCoordinate_hasFDerivAt B a).fderiv
  have hsum : HasFDerivAt (fun a : E => B a + B.flip a)
      (B + B.flip : E →L[ℂ] E →L[ℂ] E) z := B.hasFDerivAt.add B.flip.hasFDerivAt
  have hscale : HasFDerivAt (fun a : E => (1 / 2 : ℂ) • (B a + B.flip a))
      ((1 / 2 : ℂ) • (B + B.flip)) z := hsum.const_smul (1 / 2 : ℂ)
  have hd : HasFDerivAt
      (fun a : E => ContinuousLinearMap.id ℂ E + (1 / 2 : ℂ) • (B a + B.flip a))
      ((1 / 2 : ℂ) • (B + B.flip)) z := hscale.const_add (ContinuousLinearMap.id ℂ E)
  rw [he, hd.fderiv]
  change ((1 / 2 : ℂ) • (B v + B.flip v)) w = _
  simp only [smul_apply, add_apply, ContinuousLinearMap.flip_apply, smul_add]

theorem quadraticCoordinate_secondFDeriv_of_symmetric
    (B : E →L[ℂ] E →L[ℂ] E) (hB : ∀ v w, B v w = B w v) (z v w : E) :
    fderiv ℂ (fderiv ℂ (quadraticCoordinate B)) z v w = B v w := by
  rw [quadraticCoordinate_secondFDeriv, ← hB v w, ← two_smul ℂ, smul_smul]
  norm_num

end Yau.NodeProofs.F01Aux
