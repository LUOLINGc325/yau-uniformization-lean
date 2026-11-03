import Yau.Proofs.C04NormalModelJetsForms

/-! One uniform all-order budget for the inverse, real Gram metric, and
conjugated complex operator of the same normal model. -/

noncomputable section
open scoped Topology ContDiff

namespace Yau.Proofs.C04Aux
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem normal_model_complex_jet_bound
    (I : E →L[ℝ] E) (hI : ‖I‖ ≤ 1) (A : E → E →L[ℝ] E)
    (hA : ContDiff ℝ ∞ A) (R : ℝ)
    (hinv : ContDiffOn ℝ ∞ (fun y => (A y).inverse) (Metric.ball (0 : E) R))
    (B P : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j) (hP : ∀ j, 0 ≤ P j)
    (x : E) (hx : x ∈ Metric.ball (0 : E) R)
    (hjet : ∀ j, ‖iteratedFDeriv ℝ j A x‖ ≤ B j)
    (hijet : ∀ j, ‖iteratedFDeriv ℝ j (fun y => (A y).inverse) x‖ ≤ P j) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun y => normalModelComplex I (A y)) x‖ ≤
      ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * P i * B (m - i) := by
  have hIA : ContDiff ℝ ∞ (fun y => I.comp (A y)) := contDiff_const.clm_comp hA
  have hb := (ContinuousLinearMap.compL ℝ E E E).norm_iteratedFDerivWithin_le_of_bilinear_of_le_one hinv
      hIA.contDiffOn Metric.isOpen_ball.uniqueDiffOn hx
      (by simp : (m : ℕ∞ω) ≤ ∞) (ContinuousLinearMap.norm_compL_le ℝ E E E)
  simp_rw [iteratedFDerivWithin_of_isOpen _ Metric.isOpen_ball hx] at hb
  change ‖iteratedFDeriv ℝ m (fun y => normalModelComplex I (A y)) x‖ ≤ _ at hb
  apply hb.trans
  apply Finset.sum_le_sum
  intro i hi
  gcongr
  · exact mul_nonneg (Nat.cast_nonneg _) (hP i)
  · exact hijet i
  · exact (normal_model_left_composition_jet_bound I hI A hA (m - i) x).trans (hjet _)

theorem exists_normal_model_jet_bounds (B : ℕ → ℝ) (hB : ∀ m, 0 < B m) :
    ∃ C : ℕ → ℝ, (∀ m, 0 < C m) ∧
      ∀ R : ℝ, 0 < R → ∀ (A : E → E →L[ℝ] E) (I : E →L[ℝ] E),
        ‖I‖ ≤ 1 → ContDiff ℝ ∞ A →
        (∀ x ∈ Metric.ball (0 : E) R,
          ‖A x - ContinuousLinearMap.id ℝ E‖ ≤ (1 / 4 : ℝ)) →
        (∀ m x, x ∈ Metric.ball (0 : E) R → ‖iteratedFDeriv ℝ m A x‖ ≤ B m) →
        ∀ m x, x ∈ Metric.ball (0 : E) R →
          ‖iteratedFDeriv ℝ m (fun y => (A y).inverse) x‖ ≤ C m ∧
          ‖iteratedFDeriv ℝ m (fun y => normalModelMetric (A y)) x‖ ≤ C m ∧
          ‖iteratedFDeriv ℝ m (fun y => normalModelComplex I (A y)) x‖ ≤ C m := by
  obtain ⟨P, hPpos, hPb⟩ := exists_normal_inverse_jet_bounds (E := E) B hB
  let G : ℕ → ℝ := fun m => 2 * ∑ i ∈ Finset.range (m + 1),
    (m.choose i : ℝ) * B i * B (m - i)
  let J : ℕ → ℝ := fun m => ∑ i ∈ Finset.range (m + 1),
    (m.choose i : ℝ) * P i * B (m - i)
  have hG (m : ℕ) : 0 ≤ G m := by
    dsimp [G]
    exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun i hi =>
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hB i).le) (hB _).le)
  have hJ (m : ℕ) : 0 ≤ J m := by
    dsimp [J]
    exact Finset.sum_nonneg fun i hi =>
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hPpos i).le) (hB _).le
  let C : ℕ → ℝ := fun m => 1 + P m + G m + J m
  have hC (m : ℕ) : 0 < C m := by
    have hp := (hPpos m).le
    have hg := hG m
    have hj := hJ m
    dsimp [C]
    linarith
  refine ⟨C, hC, ?_⟩
  intro R hR A I hI hA hnear hjet
  obtain ⟨hinv, hInvBound⟩ := hPb R hR A hA hnear hjet
  intro m x hx
  have hi := hInvBound m x hx
  have hg : ‖iteratedFDeriv ℝ m (fun y => normalModelMetric (A y)) x‖ ≤ G m :=
    normal_model_metric_jet_bound A hA B (fun j => (hB j).le) x (fun j => hjet j x hx) m
  have hj : ‖iteratedFDeriv ℝ m (fun y => normalModelComplex I (A y)) x‖ ≤ J m :=
    normal_model_complex_jet_bound I hI A hA R hinv B P (fun j => (hB j).le)
      (fun j => (hPpos j).le) x hx (fun j => hjet j x hx) (fun j => hInvBound j x hx) m
  have hp0 := (hPpos m).le
  have hg0 := hG m
  have hj0 := hJ m
  exact ⟨hi.trans (by dsimp [C]; linarith), hg.trans (by dsimp [C]; linarith),
    hj.trans (by dsimp [C]; linarith)⟩

end Yau.Proofs.C04Aux
