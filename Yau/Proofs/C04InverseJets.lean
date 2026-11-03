import Yau.Proofs.C04InverseJetsIdentity

/-! Uniform bounds for all derivatives of one and the same smooth local inverse. -/

noncomputable section
open Set Filter Finset
open scoped Topology ContDiff

namespace Yau.Proofs.C04Aux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem inverseJet_order_bound (B : ℕ → ℝ) (hB : ∀ j, 0 < B j) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ F ψ : E → E,
      ContDiff ℝ ∞ F → ContDiffOn ℝ ∞ ψ (Metric.ball 0 (1 / 8 : ℝ)) →
      (∀ w ∈ Metric.ball 0 (1 / 8 : ℝ), ψ w ∈ Metric.ball 0 (1 / 4 : ℝ)) →
      (∀ w ∈ Metric.ball 0 (1 / 8 : ℝ), F (ψ w) = w) →
      (∀ j x, x ∈ Metric.ball 0 (1 / 4 : ℝ) → ‖iteratedFDeriv ℝ j F x‖ ≤ B j) →
      (∀ w ∈ Metric.ball 0 (1 / 8 : ℝ),
        (fderiv ℝ F (ψ w)).IsInvertible ∧ ‖(fderiv ℝ F (ψ w)).inverse‖ ≤ 4 / 3) →
      ∀ w ∈ Metric.ball 0 (1 / 8 : ℝ), ‖iteratedFDeriv ℝ m ψ w‖ ≤ C := by
  induction m using Nat.strong_induction_on with
  | h m IH =>
    by_cases hm : m = 0
    · subst m
      refine ⟨1, zero_lt_one, ?_⟩
      intro F ψ hF hψ himage hcomp hbounds hinv w hw
      rw [norm_iteratedFDeriv_zero]
      have hh : ‖ψ w‖ < 1 / 4 := by
        simpa only [Metric.mem_ball, dist_zero_right] using himage w hw
      linarith
    · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
      choose P hPpos hPbound using fun k : Fin m => IH k k.isLt
      let P' : ℕ → ℝ := fun k => if hk : k < m then P ⟨k, hk⟩ else 1
      have hP' : ∀ k, 0 < P' k := by
        intro k
        dsimp only [P']
        split_ifs with hk
        · exact hPpos ⟨k, hk⟩
        · exact zero_lt_one
      let S := ∑ c ∈ (Finset.univ.erase (inverseJetCoarse m hmpos)),
        B c.length * ∏ i : Fin c.length, P' (c.partSize i)
      have hS : 0 ≤ S := by
        exact Finset.sum_nonneg fun c hc => mul_nonneg (hB _).le
          (Finset.prod_nonneg fun i hi => (hP' _).le)
      refine ⟨(4 / 3 : ℝ) * (1 + S) + 1, by positivity, ?_⟩
      intro F ψ hF hψ himage hcomp hbounds hinv w hw
      have hsmall : ∀ k, k < m → ‖ftaylorSeries ℝ ψ w k‖ ≤ P' k := by
        intro k hk
        dsimp only [P']
        rw [dif_pos hk]
        exact hPbound ⟨k, hk⟩ F ψ hF hψ himage hcomp hbounds hinv w hw
      have hq : ∀ k, k ≤ m → ‖ftaylorSeries ℝ F (ψ w) k‖ ≤ B k := by
        intro k hk
        exact hbounds k (ψ w) (himage w hw)
      have hlinear : ∀ v : Fin 1 → E,
          ftaylorSeries ℝ F (ψ w) 1 v = fderiv ℝ F (ψ w) (v 0) :=
        fun v => iteratedFDeriv_one_apply v
      have hid := inverseJet_identity_bound F ψ Metric.isOpen_ball hF hψ hcomp hw hmpos
      have hbound := inverseJet_coefficient_bound hmpos (ftaylorSeries ℝ F (ψ w))
        (ftaylorSeries ℝ ψ w) B P' (fun k => (hB k).le) (fun k => (hP' k).le)
        hq hsmall (fderiv ℝ F (ψ w)) (hinv w hw).1 hlinear
        (by norm_num : (0 : ℝ) ≤ 4 / 3) (hinv w hw).2 hid
      exact hbound.trans (by change (4 / 3 : ℝ) * (1 + S) ≤ (4 / 3 : ℝ) * (1 + S) + 1; linarith)

theorem same_inverse_jet_bounds (B : ℕ → ℝ) (hB : ∀ j, 0 < B j) :
    ∃ P : ℕ → ℝ, (∀ m, 0 < P m) ∧ ∀ F ψ : E → E,
      ContDiff ℝ ∞ F → ContDiffOn ℝ ∞ ψ (Metric.ball 0 (1 / 8 : ℝ)) →
      (∀ w ∈ Metric.ball 0 (1 / 8 : ℝ), ψ w ∈ Metric.ball 0 (1 / 4 : ℝ)) →
      (∀ w ∈ Metric.ball 0 (1 / 8 : ℝ), F (ψ w) = w) →
      (∀ j x, x ∈ Metric.ball 0 (1 / 4 : ℝ) → ‖iteratedFDeriv ℝ j F x‖ ≤ B j) →
      (∀ w ∈ Metric.ball 0 (1 / 8 : ℝ),
        (fderiv ℝ F (ψ w)).IsInvertible ∧ ‖(fderiv ℝ F (ψ w)).inverse‖ ≤ 4 / 3) →
      ∀ m w, w ∈ Metric.ball 0 (1 / 8 : ℝ) → ‖iteratedFDeriv ℝ m ψ w‖ ≤ P m := by
  choose P hPpos hPbound using fun m => inverseJet_order_bound (E := E) B hB m
  exact ⟨P, hPpos, fun F ψ hF hψ himage hcomp hbounds hinv m =>
    hPbound m F ψ hF hψ himage hcomp hbounds hinv⟩

end Yau.Proofs.C04Aux
