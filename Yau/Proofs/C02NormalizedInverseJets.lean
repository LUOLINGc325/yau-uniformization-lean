import Yau.Proofs.C02NormalizedInverseControl
import Yau.Proofs.C02AffinePositiveJets

/-! The normalized inverse has a single numerical jet profile fixed
before the coordinate family. The translation F(0) does not enter it. -/

noncomputable section
open Set
open scoped ContDiff
namespace Yau.Blueprint.C02Proof
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def normalizedInverseJetMajorant (r : ℝ) (b : ℕ → ℝ) (m : ℕ) : ℝ :=
  |r| * ((m.factorial : ℝ) * finiteJetEnvelope b m *
    finiteJetEnvelope (fun _ => 3 / r) m ^ m)

theorem normalizedInverseSource_jet_le
    (e : OpenPartialHomeomorph E E)
    (hClose : ‖fderiv ℝ (e : E → E) 0 - ContinuousLinearMap.id ℝ E‖ ≤ 1 / 4)
    (hBack : ContDiffOn ℝ ∞ e.symm e.target)
    (b : ℕ → ℝ) (hJets : ∀ m y, y ∈ e.target → ‖iteratedFDeriv ℝ m e.symm y‖ ≤ b m)
    (r : ℝ) (hr : 0 < r)
    {O : Set E} (hO : IsOpen O)
    (hRange : ∀ z ∈ O,
      e 0 + (Real.sqrt (2 : ℝ) / r) • fderiv ℝ (e : E → E) 0 z ∈ e.target)
    (m : ℕ) {x : E} (hx : x ∈ O) :
    ‖iteratedFDeriv ℝ m (normalizedInverseSource e r) x‖ ≤ normalizedInverseJetMajorant r b m := by
  let S := (Real.sqrt (2 : ℝ) / r) • fderiv ℝ (e : E → E) 0
  let T := fun z => e 0 + S z
  have hS : ‖S‖ ≤ 3 / r := by
    apply S.opNorm_le_bound (by positivity)
    intro v
    exact (normalization_argument_norm_le _ hClose r hr v).trans_eq (by ring)
  have hT : ContDiff ℝ ∞ T := contDiff_const.add S.contDiff
  have hQ : ContDiffOn ℝ ∞ (e.symm ∘ T) O :=
    hBack.comp hT.contDiffOn hRange
  have hCompose := norm_iteratedFDeriv_comp_on_le hO e.open_target hT.contDiffOn
    hBack hRange hx m b (fun _ => 3 / r)
    (fun i hi => hJets i (T x) (hRange x hx))
    (fun i hi him => (norm_iteratedFDeriv_affine_pos_le (e 0) S i hi x).trans hS)
  change ‖iteratedFDeriv ℝ m (fun y => r • (e.symm ∘ T) y) x‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply'
    ((hQ.contDiffAt (hO.mem_nhds hx)).of_le (by simp)), norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left hCompose (abs_nonneg r)

end Yau.Blueprint.C02Proof
