import Yau.LeafProofs.L10InteriorCommutatorEnergy

/-! The differentiated operator has the original source jet and a proved lower-order commutator. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff Topology

namespace Yau.LeafProofs

theorem ellipticOp_contDiffOn {n : ℕ}
    {a : ComplexVector n → Matrix (RIdx n) (RIdx n) ℝ}
    {b : ComplexVector n → RIdx n → ℝ} {u : ComplexVector n → ℂ}
    {O : Set (ComplexVector n)} (hO : IsOpen O)
    (ha : ∀ p q, ContDiffOn ℝ ∞ (fun y => a y p q) O)
    (hb : ∀ p, ContDiffOn ℝ ∞ (fun y => b y p) O)
    (hu : ContDiffOn ℝ ∞ u O) : ContDiffOn ℝ ∞ (LeafCandidates.ellipticOp a b u) O := by
  have hA : ContDiffOn ℝ ∞ (fun x => ∑ p, ∑ q,
      a x p q • ellipticPartial (ellipticPartial u q) p x) O := by
    apply ContDiffOn.sum
    intro p _
    apply ContDiffOn.sum
    intro q _
    exact (ha p q).smul (ellipticPartial_contDiffOn hO (ellipticPartial_contDiffOn hO hu q) p)
  have hB : ContDiffOn ℝ ∞ (fun x => ∑ p, b x p • ellipticPartial u p x) O :=
    ContDiffOn.sum fun p _ => (hb p).smul (ellipticPartial_contDiffOn hO hu p)
  exact (hA.add hB).congr (fun x _ => ellipticOp_eq_sum_partials a b u x)

theorem ellipticPartial_sobolev_bound {n m : ℕ}
    {u : ComplexVector n → ℂ} {O : Set (ComplexVector n)} (hO : IsOpen O)
    (hu : ContDiffOn ℝ ∞ u O)
    (hi : ∀ j ≤ m + 1, IntegrableOn (fun x => ‖iteratedFDeriv ℝ j u x‖^2) O (lebesgueC n))
    (i : RIdx n) :
    (∀ j ≤ m, IntegrableOn (fun x => ‖iteratedFDeriv ℝ j (ellipticPartial u i) x‖^2) O (lebesgueC n)) ∧
      LeafCandidates.sobolevNormSq O (ellipticPartial u i) m ≤
        (m + 1 : ℝ) * LeafCandidates.sobolevNormSq O u (m + 1) := by
  have hPart (j : ℕ) (hjm : j ≤ m) : IntegrableOn
      (fun x => ‖iteratedFDeriv ℝ j (ellipticPartial u i) x‖^2) O (lebesgueC n) := by
    change IntegrableOn (fun x => ‖iteratedFDeriv ℝ j (fun y => fderiv ℝ u y (realVec i)) x‖^2)
      O (lebesgueC n)
    exact elliptic_directional_jet_sq_integrableOn hO hu (hi (j + 1) (by omega)) i
  refine ⟨hPart, ?_⟩
  have hEach (j : ℕ) (hjm : j ≤ m) :
      (∫ x in O, ‖iteratedFDeriv ℝ j (ellipticPartial u i) x‖^2 ∂lebesgueC n) ≤
        LeafCandidates.sobolevNormSq O u (m + 1) := by
    apply le_trans _ (integral_iteratedFDeriv_sq_le_sobolevNormSq O u (j := j + 1) (by omega))
    apply integral_mono_ae (hPart j hjm) (hi (j + 1) (by omega))
    filter_upwards [ae_restrict_mem hO.measurableSet] with x hx
    exact pow_le_pow_left₀ (norm_nonneg _) (elliptic_directional_jet_norm_le hO hu hx i j) 2
  unfold LeafCandidates.sobolevNormSq
  calc
    _ ≤ ∑ _j ∈ Finset.range (m + 1), LeafCandidates.sobolevNormSq O u (m + 1) :=
      Finset.sum_le_sum fun j hj => hEach j (by have := Finset.mem_range.mp hj; omega)
    _ = _ := by simp [LeafCandidates.sobolevNormSq]

def ellipticDifferentiatedForcingConstant (n m : ℕ) (A : ℝ) : ℝ :=
  2 * ((m + 1 : ℝ) + ellipticFirstCommutatorEnergyConstant n m A + 1)

theorem ellipticDifferentiatedForcingConstant_pos (n m : ℕ) (A : ℝ) :
    0 < ellipticDifferentiatedForcingConstant n m A := by
  unfold ellipticDifferentiatedForcingConstant ellipticFirstCommutatorEnergyConstant
  positivity

theorem ellipticOperator_partial_sobolev_bound {n m : ℕ}
    {a : ComplexVector n → Matrix (RIdx n) (RIdx n) ℝ}
    {b : ComplexVector n → RIdx n → ℝ} {u : ComplexVector n → ℂ}
    {O : Set (ComplexVector n)} (hO : IsOpen O)
    (ha : ∀ p q, ContDiffOn ℝ ∞ (fun y => a y p q) O)
    (hb : ∀ p, ContDiffOn ℝ ∞ (fun y => b y p) O)
    (hu : ContDiffOn ℝ ∞ u O) {A : ℝ} (hA : 0 ≤ A)
    (haBound : ∀ j ≤ m + 1, ∀ x ∈ O, ∀ p q, ‖iteratedFDeriv ℝ j (fun y => a y p q) x‖ ≤ A)
    (hbBound : ∀ j ≤ m + 1, ∀ x ∈ O, ∀ p, ‖iteratedFDeriv ℝ j (fun y => b y p) x‖ ≤ A)
    (hi : ∀ j ≤ m + 2, IntegrableOn (fun x => ‖iteratedFDeriv ℝ j u x‖^2) O (lebesgueC n))
    (hFi : ∀ j ≤ m + 1, IntegrableOn (fun x => ‖iteratedFDeriv ℝ j (LeafCandidates.ellipticOp a b u) x‖^2)
      O (lebesgueC n)) (i : RIdx n) :
    (∀ j ≤ m, IntegrableOn (fun x => ‖iteratedFDeriv ℝ j
      (LeafCandidates.ellipticOp a b (ellipticPartial u i)) x‖^2) O (lebesgueC n)) ∧
    LeafCandidates.sobolevNormSq O (LeafCandidates.ellipticOp a b (ellipticPartial u i)) m ≤
      ellipticDifferentiatedForcingConstant n m A *
        (LeafCandidates.sobolevNormSq O (LeafCandidates.ellipticOp a b u) (m + 1) +
          LeafCandidates.sobolevNormSq O u (m + 2)) := by
  classical
  let F := LeafCandidates.ellipticOp a b u
  let C := ellipticFirstCommutator a b u i
  let L := LeafCandidates.ellipticOp a b (ellipticPartial u i)
  have hF := ellipticOp_contDiffOn hO ha hb hu
  have hC := ellipticFirstCommutator_contDiffOn hO ha hb hu i
  have hL := ellipticOp_contDiffOn hO ha hb (ellipticPartial_contDiffOn hO hu i)
  obtain ⟨hCInts, hCBound⟩ := ellipticFirstCommutator_sobolev_bound hO ha hb hu hA haBound hbBound hi i
  obtain ⟨hFInts, hFBound⟩ := ellipticPartial_sobolev_bound hO hF hFi i
  have hEq (x : ComplexVector n) (hx : x ∈ O) : L =ᶠ[𝓝 x] (fun y => ellipticPartial F i y - C y) := by
    filter_upwards [hO.mem_nhds hx] with y hy
    exact (eq_sub_iff_add_eq).mpr (ellipticFirstCommutator_identity hO ha hb hu hy i).symm
  have hPoint (j : ℕ) (hjm : j ≤ m) (x : ComplexVector n) (hx : x ∈ O) :
      ‖iteratedFDeriv ℝ j L x‖^2 ≤
        2 * (‖iteratedFDeriv ℝ j (ellipticPartial F i) x‖^2 + ‖iteratedFDeriv ℝ j C x‖^2) := by
    have heq : iteratedFDeriv ℝ j L x = iteratedFDeriv ℝ j (fun y => ellipticPartial F i y - C y) x :=
      ((hEq x hx).iteratedFDeriv ℝ j).eq_of_nhds
    have hsub : ‖iteratedFDeriv ℝ j L x‖ ≤
        ‖iteratedFDeriv ℝ j (ellipticPartial F i) x‖ + ‖iteratedFDeriv ℝ j C x‖ := by
      rw [heq, fun_iteratedFDeriv_sub_apply
        (((ellipticPartial_contDiffOn hO hF i).contDiffAt (hO.mem_nhds hx)).of_le (by simp))
        ((hC.contDiffAt (hO.mem_nhds hx)).of_le (by simp))]
      exact norm_sub_le _ _
    have hs := pow_le_pow_left₀ (norm_nonneg _) hsub 2
    nlinarith [sq_nonneg (‖iteratedFDeriv ℝ j (ellipticPartial F i) x‖ - ‖iteratedFDeriv ℝ j C x‖)]
  have hDom (j : ℕ) (hjm : j ≤ m) : IntegrableOn
      (fun x => 2 * (‖iteratedFDeriv ℝ j (ellipticPartial F i) x‖^2 +
        ‖iteratedFDeriv ℝ j C x‖^2)) O (lebesgueC n) := ((hFInts j hjm).add (hCInts j hjm)).const_mul 2
  have hInts (j : ℕ) (hjm : j ≤ m) : IntegrableOn (fun x => ‖iteratedFDeriv ℝ j L x‖^2)
      O (lebesgueC n) := by
    have hc : ContinuousOn (fun x => iteratedFDeriv ℝ j L x) O := by
      intro x hx
      exact ((hL.contDiffAt (hO.mem_nhds hx)).differentiableAt_iteratedFDeriv
        (m := j) (by exact_mod_cast ENat.natCast_lt_top j)).continuousAt.continuousWithinAt
    apply (hDom j hjm).mono' ((hc.norm.pow 2).aestronglyMeasurable hO.measurableSet)
    filter_upwards [ae_restrict_mem hO.measurableSet] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hPoint j hjm x hx
  refine ⟨hInts, ?_⟩
  have hEach (j : ℕ) (hjm : j ≤ m) :
      (∫ x in O, ‖iteratedFDeriv ℝ j L x‖^2 ∂lebesgueC n) ≤
        2 * ((∫ x in O, ‖iteratedFDeriv ℝ j (ellipticPartial F i) x‖^2 ∂lebesgueC n) +
          ∫ x in O, ‖iteratedFDeriv ℝ j C x‖^2 ∂lebesgueC n) := by
    have hbound := integral_mono_ae (hInts j hjm) (hDom j hjm)
      (show ∀ᵐ x ∂(lebesgueC n).restrict O,
        ‖iteratedFDeriv ℝ j L x‖^2 ≤ 2 * (‖iteratedFDeriv ℝ j (ellipticPartial F i) x‖^2 +
          ‖iteratedFDeriv ℝ j C x‖^2) by
        filter_upwards [ae_restrict_mem hO.measurableSet] with x hx
        exact hPoint j hjm x hx)
    have hFI' : IntegrableOn (fun x => ‖iteratedFDeriv ℝ j (ellipticPartial F i) x‖^2) O (lebesgueC n) :=
      hFInts j hjm
    have hCI' : IntegrableOn (fun x => ‖iteratedFDeriv ℝ j C x‖^2) O (lebesgueC n) := hCInts j hjm
    simpa only [integral_const_mul, integral_add hFI' hCI'] using hbound
  have hSum : LeafCandidates.sobolevNormSq O L m ≤
      2 * (LeafCandidates.sobolevNormSq O (ellipticPartial F i) m + LeafCandidates.sobolevNormSq O C m) := by
    unfold LeafCandidates.sobolevNormSq
    calc
      _ ≤ ∑ j ∈ Finset.range (m + 1),
          2 * ((∫ x in O, ‖iteratedFDeriv ℝ j (ellipticPartial F i) x‖^2 ∂lebesgueC n) +
            ∫ x in O, ‖iteratedFDeriv ℝ j C x‖^2 ∂lebesgueC n) :=
        Finset.sum_le_sum fun j hj => hEach j (by have := Finset.mem_range.mp hj; omega)
      _ = _ := by rw [← Finset.mul_sum, Finset.sum_add_distrib]
  have hKC : 0 ≤ ellipticFirstCommutatorEnergyConstant n m A := by
    unfold ellipticFirstCommutatorEnergyConstant
    positivity
  have hUN := sobolevNormSq_nonneg O u (m + 2)
  have hFN := sobolevNormSq_nonneg O F (m + 1)
  dsimp only [ellipticDifferentiatedForcingConstant]
  nlinarith [mul_nonneg (add_nonneg hKC zero_le_one) hFN,
    mul_nonneg (show (0 : ℝ) ≤ m + 2 by positivity) hUN]

end Yau.LeafProofs
