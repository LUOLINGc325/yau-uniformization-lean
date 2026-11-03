import Yau.Proofs.F04AuxiliaryBuffer

open Filter Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

noncomputable section

namespace Yau.F04Proof

open Yau.Parabolic Yau.ParabolicCandidates Seeley

def matrixTransposeContinuous (n : ℕ) : Mat n →L[ℝ] Mat n :=
  (Matrix.transposeLinearEquiv (Yau.RIdx n) (Yau.RIdx n) ℝ ℝ).toLinearMap.mkContinuous 1
    (fun A => by
      change ‖Aᵀ‖ ≤ 1 * ‖A‖
      rw [Matrix.frobenius_norm_transpose, one_mul])

theorem auxiliaryCoefficientExtension (n : ℕ) (_hn : 0 < n)
    (O V : Set (Space n)) (S lam upper : ℝ)
    (hO : IsOpen O) (_hV : IsOpen V) (hVc : IsCompact (closure V))
    (hVO : closure V ⊆ O) (hS : 0 < S)
    (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ)
    (hsmooth : SmoothCoefficients (O ×ˢ Icc 0 S) a b)
    (hell : Elliptic (O ×ˢ Icc 0 S) a lam upper) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ (a_e : Point n → Mat n) (b_e : Point n → Yau.RIdx n → ℝ),
      SmoothCoefficients (V ×ˢ Ioo (-ε) S) a_e b_e ∧
      Elliptic (V ×ˢ Ioo (-ε) S) a_e (lam / 2) (2 * upper) ∧
      ∀ p ∈ V ×ˢ Ico 0 S, a_e p = a p ∧ b_e p = b p := by
  obtain ⟨W, hW, hVW, hWO, hWc⟩ := exists_open_between_and_isCompact_closure hVc hO hVO
  obtain ⟨δ, hδ, hδS, χ, hχ, hχzero, hχone⟩ := auxiliary_time_cutoff hS
  let A : Point n → Mat n := seeleyExtend χ a
  let a_e : Point n → Mat n := fun p => (1 / 2 : ℝ) • (A p + (A p)ᵀ)
  let b_e : Point n → Yau.RIdx n → ℝ := fun p i => seeleyExtend χ (fun q => b q i) p
  have hAs : ContDiffOn ℝ ∞ A (W ×ˢ Iio S) :=
    seeleyExtend_contDiffOn hO hW hWc hWO hδ hδS hχ hχzero hχone hsmooth.1
  have hAtr : ContDiffOn ℝ ∞ (fun p => (A p)ᵀ) (W ×ˢ Iio S) :=
    (matrixTransposeContinuous n).contDiff.comp_contDiffOn hAs
  have hAes : ContDiffOn ℝ ∞ a_e (W ×ˢ Iio S) :=
    (contDiffOn_const (c := (1 / 2 : ℝ))).smul (hAs.add hAtr)
  have hbs (i : Yau.RIdx n) : ContDiffOn ℝ ∞ (fun p => b_e p i) (W ×ˢ Iio S) :=
    seeleyExtend_contDiffOn hO hW hWc hWO hδ hδS hχ hχzero hχone (hsmooth.2 i)
  obtain ⟨ε, hε, hnorm⟩ := compact_time_norm_control hVc hVW hS
    (half_pos hell.1) hAs.continuousOn
  have hVsub : V ⊆ W := fun x hx => hVW (subset_closure hx)
  have heq (p : Point n) (hp : p ∈ V ×ˢ Ico 0 S) : a_e p = a p ∧ b_e p = b p := by
    have hpO : p ∈ O ×ˢ Icc 0 S := ⟨hVO (subset_closure hp.1), hp.2.1, hp.2.2.le⟩
    have hsym := (hell.2.2 p hpO).1
    constructor
    · change (1 / 2 : ℝ) • (A p + (A p)ᵀ) = a p
      rw [show A p = a p from seeleyExtend_eq_nonneg χ a p hp.2.1, hsym.eq]
      ext i j
      simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
      ring
    · funext i
      exact seeleyExtend_eq_nonneg χ (fun q => b q i) p hp.2.1
  refine ⟨ε, hε, a_e, b_e, ⟨hAes.mono ?_, fun i => (hbs i).mono ?_⟩, ?_, heq⟩
  · exact fun p hp => ⟨hVsub hp.1, hp.2.2⟩
  · exact fun p hp => ⟨hVsub hp.1, hp.2.2⟩
  refine ⟨half_pos hell.1, by linarith [hell.1, hell.2.1], ?_⟩
  intro p hp
  refine ⟨(Matrix.isSymm_add_transpose_self (A p)).smul (1 / 2 : ℝ), ?_⟩
  by_cases ht : 0 ≤ p.2
  · have hpO : p ∈ O ×ˢ Icc 0 S := ⟨hVO (subset_closure hp.1), ht, hp.2.2.le⟩
    rw [(heq p ⟨hp.1, ht, hp.2.2⟩).1]
    apply quadratic_elliptic_perturbation (a p) (a p) lam upper hell.1 hell.2.1 (hell.2.2 p hpO).2
    simp only [sub_self, norm_zero]
    exact (half_pos hell.1).le
  · have htneg : p.2 < 0 := lt_of_not_ge ht
    have hp0 : (p.1, (0 : ℝ)) ∈ O ×ˢ Icc 0 S := ⟨hVO (subset_closure hp.1), le_rfl, hS.le⟩
    have hs0 := (hell.2.2 (p.1, 0) hp0).1
    have hnorm' : ‖A p - a (p.1, 0)‖ ≤ lam / 2 := by
      have hh := hnorm p.1 (subset_closure hp.1) p.2 ⟨hp.2.1, htneg⟩
      simpa only [show A (p.1, 0) = a (p.1, 0) from
        seeleyExtend_eq_nonneg χ a (p.1, 0) le_rfl] using hh
    apply quadratic_elliptic_perturbation (a_e p) (a (p.1, 0)) lam upper
      hell.1 hell.2.1 (hell.2.2 (p.1, 0) hp0).2
    exact (symmetricPart_difference_le (A p) (a (p.1, 0)) hs0).trans hnorm'

end Yau.F04Proof
