import Yau.Proofs.C07CurveConcatSpeed

open scoped Manifold Topology

noncomputable section

namespace Yau.Proofs.C07CurveConcatAux

open Yau Set Filter MeasureTheory

variable {n : ℕ} {M : ComplexManifold n} {k : HermitianField M} {x y z : M.Carrier}

theorem concat_speed_left_ae (γ : PiecewiseC1Curve x y) (η : PiecewiseC1Curve y z) :
    curveSpeed k (concatPiecewise γ η) =ᵐ[volume.restrict (Icc (0 : ℝ) (1 / 2))]
      (fun t => 2 * curveSpeed k γ (2 * t)) := by
  have hnb := (concatBreakpoints γ η).finite_toSet.countable.ae_notMem volume
  filter_upwards [ae_restrict_of_ae hnb, ae_restrict_mem measurableSet_Icc] with t hb ht
  exact concat_speed_left k γ η (lt_of_le_of_ne ht.2 (concat_half_ne γ η hb))
    (concat_left_not_break γ η hb)

theorem concat_speed_right_ae (γ : PiecewiseC1Curve x y) (η : PiecewiseC1Curve y z) :
    curveSpeed k (concatPiecewise γ η) =ᵐ[volume.restrict (Icc (1 / 2 : ℝ) 1)]
      (fun t => 2 * curveSpeed k η (2 * t - 1)) := by
  have hnb := (concatBreakpoints γ η).finite_toSet.countable.ae_notMem volume
  filter_upwards [ae_restrict_of_ae hnb, ae_restrict_mem measurableSet_Icc] with t hb ht
  exact concat_speed_right k γ η (lt_of_le_of_ne ht.1 (concat_half_ne γ η hb).symm)
    (concat_right_not_break γ η hb)

theorem intervalIntegral_eq_Icc {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) :
    (∫ t in a..b, f t) = ∫ t in Icc a b, f t := by
  rw [intervalIntegral.integral_of_le hab, integral_Icc_eq_integral_Ioc]

/-- The explicit concatenation is integrable in the original metric and
has length exactly equal to the sum, by the two affine changes of variables. -/
theorem concat_integrable_length (γ : IntegrableCurve k x y) (η : IntegrableCurve k y z) :
    IntegrableOn (curveSpeed k (concatPiecewise γ.1 η.1)) (Icc (0 : ℝ) 1) ∧
      curveLength k (concatPiecewise γ.1 η.1) = curveLength k γ.1 + curveLength k η.1 := by
  have hγ : IntervalIntegrable (curveSpeed k γ.1) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).2 γ.2
  have hη : IntervalIntegrable (curveSpeed k η.1) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).2 η.2
  have hL : IntervalIntegrable (fun t => 2 * curveSpeed k γ.1 (2 * t)) volume 0 (1 / 2) := by
    simpa using (hγ.comp_mul_left (c := 2)).const_mul 2
  have hR : IntervalIntegrable (fun t => 2 * curveSpeed k η.1 (2 * t - 1)) volume (1 / 2) 1 := by
    simpa using ((hη.comp_sub_right 1).comp_mul_left (c := 2)).const_mul 2
  have hζL : IntegrableOn (curveSpeed k (concatPiecewise γ.1 η.1)) (Icc (0 : ℝ) (1 / 2)) :=
    ((intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)).1 hL).congr
      (concat_speed_left_ae γ.1 η.1).symm
  have hζR : IntegrableOn (curveSpeed k (concatPiecewise γ.1 η.1)) (Icc (1 / 2 : ℝ) 1) :=
    ((intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)).1 hR).congr
      (concat_speed_right_ae γ.1 η.1).symm
  have hint : IntegrableOn (curveSpeed k (concatPiecewise γ.1 η.1)) (Icc (0 : ℝ) 1) := by
    apply (hζL.union hζR).mono_set
    intro t ht
    by_cases h : t ≤ 1 / 2
    · exact Or.inl ⟨ht.1, h⟩
    · exact Or.inr ⟨le_of_not_ge h, ht.2⟩
  have hleftEq : (∫ t in (0 : ℝ)..(1 / 2), curveSpeed k (concatPiecewise γ.1 η.1) t) =
      ∫ t in (0 : ℝ)..(1 / 2), 2 * curveSpeed k γ.1 (2 * t) := by
    rw [intervalIntegral_eq_Icc (by norm_num : (0 : ℝ) ≤ 1 / 2),
      intervalIntegral_eq_Icc (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    exact integral_congr_ae (concat_speed_left_ae γ.1 η.1)
  have hrightEq : (∫ t in (1 / 2 : ℝ)..1, curveSpeed k (concatPiecewise γ.1 η.1) t) =
      ∫ t in (1 / 2 : ℝ)..1, 2 * curveSpeed k η.1 (2 * t - 1) := by
    rw [intervalIntegral_eq_Icc (by norm_num : (1 / 2 : ℝ) ≤ 1),
      intervalIntegral_eq_Icc (by norm_num : (1 / 2 : ℝ) ≤ 1)]
    exact integral_congr_ae (concat_speed_right_ae γ.1 η.1)
  have hleftEval : (∫ t in (0 : ℝ)..(1 / 2), 2 * curveSpeed k γ.1 (2 * t)) = curveLength k γ.1 := by
    have hs := intervalIntegral.smul_integral_comp_mul_left (f := curveSpeed k γ.1)
      (a := (0 : ℝ)) (b := 1 / 2) (2 : ℝ)
    norm_num only [smul_eq_mul] at hs
    rw [intervalIntegral.integral_const_mul]
    exact hs.trans (intervalIntegral_eq_Icc zero_le_one)
  have hrightEval : (∫ t in (1 / 2 : ℝ)..1, 2 * curveSpeed k η.1 (2 * t - 1)) = curveLength k η.1 := by
    have hs := intervalIntegral.smul_integral_comp_mul_sub (f := curveSpeed k η.1)
      (a := (1 / 2 : ℝ)) (b := 1) (2 : ℝ) (1 : ℝ)
    norm_num only [smul_eq_mul] at hs
    rw [intervalIntegral.integral_const_mul]
    exact hs.trans (intervalIntegral_eq_Icc zero_le_one)
  have hζLi := (intervalIntegrable_iff_integrableOn_Icc_of_le
    (by norm_num : (0 : ℝ) ≤ 1 / 2)).2 hζL
  have hζRi := (intervalIntegrable_iff_integrableOn_Icc_of_le
    (by norm_num : (1 / 2 : ℝ) ≤ 1)).2 hζR
  refine ⟨hint, ?_⟩
  change (∫ t in Icc (0 : ℝ) 1, curveSpeed k (concatPiecewise γ.1 η.1) t) = _
  rw [← intervalIntegral_eq_Icc zero_le_one,
    ← intervalIntegral.integral_add_adjacent_intervals hζLi hζRi,
    hleftEq, hrightEq, hleftEval, hrightEval]

theorem exists_curve_concat (γ : IntegrableCurve k x y) (η : IntegrableCurve k y z) :
    ∃ ζ : IntegrableCurve k x z,
      (∀ t ∈ Icc (0 : ℝ) (1 / 2), ζ.1 t = γ.1 (2 * t)) ∧
      (∀ t ∈ Icc (1 / 2 : ℝ) 1, ζ.1 t = η.1 (2 * t - 1)) ∧
      curveLength k ζ.1 = curveLength k γ.1 + curveLength k η.1 := by
  obtain ⟨hint, hlen⟩ := concat_integrable_length γ η
  refine ⟨⟨concatPiecewise γ.1 η.1, hint⟩, ?_, ?_, hlen⟩
  · intro t ht
    exact concatPath_left γ.1 η.1 ht.2
  · intro t ht
    exact concatPath_right γ.1 η.1 ht.1

end Yau.Proofs.C07CurveConcatAux
