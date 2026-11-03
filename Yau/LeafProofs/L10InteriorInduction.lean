import Yau.LeafProofs.L10InteriorForcing

/-! The numerical constants are chosen before coefficients at every induction step. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff Topology

namespace Yau.LeafProofs

theorem sobolevNormSq_zero {n : ℕ} (O : Set (ComplexVector n)) (u : ComplexVector n → ℂ) :
    LeafCandidates.sobolevNormSq O u 0 = ∫ x in O, ‖u x‖^2 ∂lebesgueC n := by
  simp only [LeafCandidates.sobolevNormSq, Nat.zero_add, Finset.sum_range_one, norm_iteratedFDeriv_zero]

theorem sobolevNormSq_mono_domain {n s : ℕ} {O V : Set (ComplexVector n)}
    {u : ComplexVector n → ℂ} (hOV : O ⊆ V)
    (hi : ∀ j ≤ s, IntegrableOn (fun x => ‖iteratedFDeriv ℝ j u x‖^2) V (lebesgueC n)) :
    LeafCandidates.sobolevNormSq O u s ≤ LeafCandidates.sobolevNormSq V u s := by
  unfold LeafCandidates.sobolevNormSq
  apply Finset.sum_le_sum
  intro j hj
  apply setIntegral_mono_set (hi j (by have := Finset.mem_range.mp hj; omega))
    (Filter.Eventually.of_forall fun _ => sq_nonneg _)
  exact Filter.Eventually.of_forall fun x hx => hOV hx

theorem elliptic_interior_energy_estimate (n : ℕ) (hn : 0 < n) :
    ∀ (s : ℕ) (r R ell A : ℝ), 0 < r → r < R → 0 < ell → 0 < A →
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : ComplexVector n → Matrix (RIdx n) (RIdx n) ℝ)
        (b : ComplexVector n → RIdx n → ℝ),
      (∀ p q, ContDiffOn ℝ ∞ (fun z => a z p q) (Metric.ball 0 R)) →
      (∀ p, ContDiffOn ℝ ∞ (fun z => b z p) (Metric.ball 0 R)) →
      (∀ z ∈ Metric.ball 0 R, ∀ v : RIdx n → ℝ,
        ell * ∑ p, (v p)^2 ≤ ∑ p, ∑ q, a z p q * v p * v q) →
      (∀ k ≤ s + 1, ∀ z ∈ Metric.ball 0 R, ∀ p q,
        ‖iteratedFDeriv ℝ k (fun w => a w p q) z‖ ≤ A ∧
        ‖iteratedFDeriv ℝ k (fun w => b w p) z‖ ≤ A) →
      ∀ u : ComplexVector n → ℂ, ContDiffOn ℝ ∞ u (Metric.ball 0 R) →
      (∀ k ≤ s + 2, IntegrableOn (fun z => ‖iteratedFDeriv ℝ k u z‖^2)
        (Metric.ball 0 R) (lebesgueC n)) →
      (∀ k ≤ s, IntegrableOn (fun z => ‖iteratedFDeriv ℝ k (LeafCandidates.ellipticOp a b u) z‖^2)
        (Metric.ball 0 R) (lebesgueC n)) →
      LeafCandidates.sobolevNormSq (Metric.ball 0 r) u (s + 2) ≤
        C * (LeafCandidates.sobolevNormSq (Metric.ball 0 R) u 0 +
          LeafCandidates.sobolevNormSq (Metric.ball 0 R) (LeafCandidates.ellipticOp a b u) s) := by
  intro s
  induction s with
  | zero =>
    intro r R ell A hr hrR hell hA
    obtain ⟨C, hC, hBase⟩ := elliptic_H2_interior n 0 hn r R ell A hr hrR hell hA
    refine ⟨C, hC, ?_⟩
    intro a b ha _hb hEll hbound u hu hi hFi
    simpa only [sobolevNormSq_zero] using hBase a b ha hEll hbound u hu hi hFi
  | succ s ih =>
    intro r R ell A hr hrR hell hA
    let ρ : ℝ := (r + R) / 2
    have hrρ : r < ρ := by dsimp only [ρ]; linarith
    have hρR : ρ < R := by dsimp only [ρ]; linarith
    have hρ : 0 < ρ := hr.trans hrρ
    obtain ⟨Cin, hCin, hInner⟩ := ih r ρ ell A hr hrρ hell hA
    obtain ⟨Cout, hCout, hOuter⟩ := ih ρ R ell A hρ hρR hell hA
    let d : ℝ := Fintype.card (RIdx n)
    let K : ℝ := ellipticDifferentiatedForcingConstant n s A
    let P : ℝ := d^2 * Cin * (K + 1)
    have hd : 0 ≤ d := by dsimp only [d]; positivity
    have hK : 0 < K := ellipticDifferentiatedForcingConstant_pos _ _ _
    have hP : 0 ≤ P := by dsimp only [P]; positivity
    refine ⟨1 + P * (Cout + 1), by positivity, ?_⟩
    intro a b ha hb hEll hbound u hu hi hFi
    let F := LeafCandidates.ellipticOp a b u
    let j₀ : RIdx n := (⟨0, hn⟩, 0)
    have hsubρ : Metric.ball (0 : ComplexVector n) ρ ⊆ Metric.ball 0 R := Metric.ball_subset_ball hρR.le
    have hsubr : Metric.ball (0 : ComplexVector n) r ⊆ Metric.ball 0 ρ := Metric.ball_subset_ball hrρ.le
    have hsubrR := hsubr.trans hsubρ
    have haρ (p q : RIdx n) := (ha p q).mono hsubρ
    have hbρ (p : RIdx n) := (hb p).mono hsubρ
    have huρ := hu.mono hsubρ
    have hEllρ (z : ComplexVector n) (hz : z ∈ Metric.ball 0 ρ) := hEll z (hsubρ hz)
    have hboundsρ (k : ℕ) (hk : k ≤ s + 1) (z : ComplexVector n) (hz : z ∈ Metric.ball 0 ρ)
        (p q : RIdx n) := hbound k (by omega) z (hsubρ hz) p q
    have hSrc (i : RIdx n) := ellipticOperator_partial_sobolev_bound (m := s)
      Metric.isOpen_ball haρ hbρ huρ hA.le
      (fun k hk z hz p q => (hbound k (by omega) z (hsubρ hz) p q).1)
      (fun k hk z hz p => (hbound k (by omega) z (hsubρ hz) p j₀).2)
      (fun k hk => (hi k (by omega)).mono_set hsubρ)
      (fun k hk => (hFi k (by omega)).mono_set hsubρ) i
    have hVInts (i : RIdx n) (k : ℕ) (hk : k ≤ s + 2) : IntegrableOn
        (fun z => ‖iteratedFDeriv ℝ k (ellipticPartial u i) z‖^2) (Metric.ball 0 ρ) (lebesgueC n) := by
      change IntegrableOn (fun z => ‖iteratedFDeriv ℝ k (fun y => fderiv ℝ u y (realVec i)) z‖^2)
        (Metric.ball 0 ρ) (lebesgueC n)
      exact elliptic_directional_jet_sq_integrableOn Metric.isOpen_ball huρ
        ((hi (k + 1) (by omega)).mono_set hsubρ) i
    have hV0 (i : RIdx n) : LeafCandidates.sobolevNormSq (Metric.ball 0 ρ) (ellipticPartial u i) 0 ≤
        LeafCandidates.sobolevNormSq (Metric.ball 0 ρ) u (s + 2) := by
      have h0 := (ellipticPartial_sobolev_bound (m := 0) Metric.isOpen_ball huρ
        (fun k hk => (hi k (by omega)).mono_set hsubρ) i).2
      have h01 : LeafCandidates.sobolevNormSq (Metric.ball 0 ρ) (ellipticPartial u i) 0 ≤
          LeafCandidates.sobolevNormSq (Metric.ball 0 ρ) u 1 := by
        simpa only [Nat.zero_add, Nat.cast_zero, zero_add, one_mul] using h0
      exact h01.trans (sobolevNormSq_mono_order _ u (show 1 ≤ s + 2 by omega))
    let U := LeafCandidates.sobolevNormSq (Metric.ball 0 ρ) u (s + 2)
    let V := LeafCandidates.sobolevNormSq (Metric.ball 0 ρ) F (s + 1)
    let D := LeafCandidates.sobolevNormSq (Metric.ball 0 R) u 0 +
      LeafCandidates.sobolevNormSq (Metric.ball 0 R) F (s + 1)
    have hUN : 0 ≤ U := sobolevNormSq_nonneg _ _ _
    have hVN : 0 ≤ V := sobolevNormSq_nonneg _ _ _
    have hD : 0 ≤ D := add_nonneg (sobolevNormSq_nonneg _ _ _) (sobolevNormSq_nonneg _ _ _)
    have hInnerBound (i : RIdx n) :
        LeafCandidates.sobolevNormSq (Metric.ball 0 r) (ellipticPartial u i) (s + 2) ≤
          Cin * (K + 1) * (V + U) := by
      have hEst := hInner a b haρ hbρ hEllρ hboundsρ (ellipticPartial u i)
        (ellipticPartial_contDiffOn Metric.isOpen_ball huρ i) (hVInts i) (hSrc i).1
      have hForce := (hSrc i).2
      have hBase := hV0 i
      change _ ≤ K * (V + U) at hForce
      change _ ≤ U at hBase
      nlinarith [mul_nonneg hCin.le (sub_nonneg.mpr hForce),
        mul_nonneg hCin.le (sub_nonneg.mpr hBase), mul_nonneg hCin.le hVN]
    have hSum : (∑ i, LeafCandidates.sobolevNormSq (Metric.ball 0 r) (ellipticPartial u i) (s + 2)) ≤
        d * (Cin * (K + 1) * (V + U)) := by
      simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
        Finset.sum_le_sum (s := Finset.univ) (fun i _ => hInnerBound i)
    have hOuterBound := hOuter a b ha hb hEll
      (fun k hk z hz p q => hbound k (by omega) z hz p q) u hu
      (fun k hk => hi k (by omega)) (fun k hk => hFi k (by omega))
    have hOrder := sobolevNormSq_mono_order (Metric.ball (0 : ComplexVector n) R) F (Nat.le_succ s)
    have hUBound : U ≤ Cout * D := by
      exact hOuterBound.trans (mul_le_mul_of_nonneg_left
        (add_le_add le_rfl hOrder) hCout.le)
    have hVBound : V ≤ LeafCandidates.sobolevNormSq (Metric.ball 0 R) F (s + 1) :=
      sobolevNormSq_mono_domain hsubρ (fun k hk => hFi k (by omega))
    have hU0 : LeafCandidates.sobolevNormSq (Metric.ball 0 r) u 0 ≤
        LeafCandidates.sobolevNormSq (Metric.ball 0 R) u 0 :=
      sobolevNormSq_mono_domain hsubrR (fun k hk => hi k (by omega))
    have hBudget : V + U ≤ (Cout + 1) * D := by
      have hU0N := sobolevNormSq_nonneg (Metric.ball (0 : ComplexVector n) R) u 0
      dsimp only [D] at *
      nlinarith only [hUBound, hVBound, hU0N]
    have hNorm := sobolevNormSq_successor_le_partials (s := s + 2) Metric.isOpen_ball
      (hu.mono hsubrR) (fun k hk => (hi k (by omega)).mono_set hsubrR)
    change LeafCandidates.sobolevNormSq (Metric.ball 0 r) u (s + 3) ≤
      (1 + P * (Cout + 1)) * D
    calc
      _ ≤ LeafCandidates.sobolevNormSq (Metric.ball 0 r) u 0 +
          d * ∑ i, LeafCandidates.sobolevNormSq (Metric.ball 0 r) (ellipticPartial u i) (s + 2) := by
        simpa only [sobolevNormSq_zero] using hNorm
      _ ≤ LeafCandidates.sobolevNormSq (Metric.ball 0 R) u 0 +
          d * (d * (Cin * (K + 1) * (V + U))) := add_le_add hU0 (mul_le_mul_of_nonneg_left hSum hd)
      _ = LeafCandidates.sobolevNormSq (Metric.ball 0 R) u 0 + P * (V + U) := by dsimp only [P]; ring
      _ ≤ LeafCandidates.sobolevNormSq (Metric.ball 0 R) u 0 + P * ((Cout + 1) * D) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hBudget hP)
      _ ≤ _ := by
        have hFN := sobolevNormSq_nonneg (Metric.ball (0 : ComplexVector n) R) F (s + 1)
        dsimp only [D]
        nlinarith only [hFN]

end Yau.LeafProofs
