import Yau.Proofs.C02NijenhuisPullback

/-! Dilation preserves the actual frozen Nijenhuis tensor equation. -/

noncomputable section
namespace Yau.Blueprint.C02Proof
variable {n : ℕ}

theorem nijenhuis_comp_dilation
    (J : ComplexVector n → ComplexVector n →L[ℝ] ComplexVector n)
    (r : ℝ) (x : ComplexVector n) (hJ : DifferentiableAt ℝ J (r • x))
    (v w : ComplexVector n) :
    LeafCandidates.nijenhuis (fun y => J (r • y)) x v w =
      r • LeafCandidates.nijenhuis J (r • x) v w := by
  have hD (u : ComplexVector n) :
      fderiv ℝ (fun y => J (r • y) u) x =
        r • fderiv ℝ (fun y => J y u) (r • x) := by
    have hh := ((hJ.clm_apply (differentiableAt_const u)).hasFDerivAt.comp x
      ((hasFDerivAt_id x).const_smul r)).fderiv
    apply hh.trans
    apply ContinuousLinearMap.ext
    intro a
    simp only [ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.id_apply, map_smul]
  simp only [LeafCandidates.nijenhuis, LeafCandidates.bracket, hD, fderiv_const_apply,
    zero_apply, smul_apply, map_smul, smul_sub, map_sub, map_zero, smul_zero]

end Yau.Blueprint.C02Proof
