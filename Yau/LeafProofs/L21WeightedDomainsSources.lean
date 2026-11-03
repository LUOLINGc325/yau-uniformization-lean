import Yau.LeafProofs.L21WeightedDomainsCoercivity

open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

theorem weightedDomains_memLp_of_continuousOn_ball_two (K : ℝ) (hK : 0 ≤ K)
    {f : X n → ℂ} (hf : ContinuousOn f (Metric.ball 0 2)) :
    MemLp f 2 (weightedBallMeasure n K) := by
  have hfC := hf.mono weightedDomains_closedBall_one_subset_ball_two
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0 : X n) (1 : ℝ)).exists_bound_of_continuousOn hfC
  letI : IsFiniteMeasure ((Yau.lebesgueC n).restrict (Metric.closedBall 0 1)) :=
    isFiniteMeasure_restrict.mpr (by
      rw [Yau.LeafProofs.lebesgueC_eq_volume]
      exact (isCompact_closedBall (0 : X n) (1 : ℝ)).measure_lt_top.ne)
  have hMem : MemLp f 2 ((Yau.lebesgueC n).restrict (Metric.closedBall 0 1)) :=
    MemLp.of_bound (hfC.aestronglyMeasurable Metric.isClosed_closedBall.measurableSet) C
      ((ae_restrict_mem Metric.isClosed_closedBall.measurableSet).mono (fun x hx => hC x hx))
  exact hMem.mono_measure ((weightedBallMeasure_le_restrict K hK).trans
    (Measure.restrict_mono Metric.ball_subset_closedBall le_rfl))

theorem weightedDomains_dbarA_coordinate
    (A : X n → Matrix (Fin n) (Fin n) ℂ) (j k : Fin n) (x : X n) :
    dbarA A j (fun y => y k) x = A x j k := by
  have hd : fderiv ℝ (fun y : X n => y k) x =
      (EuclideanSpace.proj k : X n →L[ℂ] ℂ).restrictScalars ℝ :=
    ((EuclideanSpace.proj k : X n →L[ℂ] ℂ).restrictScalars ℝ).fderiv
  have hBar (v : X n) : Yau.wirtBar (fun y : X n => y k) x v = 0 := by
    unfold Yau.wirtBar
    rw [hd]
    change (1/2 : ℂ)*(v k+Complex.I*(Complex.I*v k)) = 0
    rw [← mul_assoc,Complex.I_mul_I]
    ring
  have hHol (v : X n) : Yau.wirt (fun y : X n => y k) x v = v k := by
    unfold Yau.wirt
    rw [hd]
    change (1/2 : ℂ)*(v k-Complex.I*(Complex.I*v k)) = v k
    rw [← mul_assoc,Complex.I_mul_I]
    ring
  simp [dbarA,hBar,hHol,Yau.stdVec,PiLp.single_apply]

theorem weightedMaximalT_graph_weak_scaled_representative (K : ℝ) (hK : 0 ≤ K)
    (A : X n → Matrix (Fin n) (Fin n) ℂ) (hA : MatrixSmoothOn A (Metric.ball 0 1))
    (u : WeightedScalar n K) (f : WeightedOneForm n K)
    (w : X n → Fin n → ℂ)
    (hGraph : (u,f) ∈ (weightedMaximalT K hK A hA).graph)
    (hRep : (f : X n → X n) =ᵐ[weightedBallMeasure n K]
      (fun x => WithLp.toLp 2 (fun j => (rho x : ℂ)*w x j))) :
    DbarWeakOn A (u : X n → ℂ) w (Metric.ball 0 1) := by
  have hWeak := weightedMaximalT_graph_dbarWeakOn K hK A hA u f hGraph
  have hRepB := (weightedBall_ae_eq_iff K _ _).mp hRep
  intro j ψ hψ hc hs
  calc
    _ = ∫ x in Metric.ball (0 : X n) 1, (ψ x : ℂ)*w x j ∂Yau.lebesgueC n :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
        rw [image_eq_zero_of_notMem_tsupport (fun hh => hx (hs hh))]
        simp)).symm
    _ = ∫ x in Metric.ball (0 : X n) 1, (ψ x : ℂ)*(f x j/(rho x : ℂ)) ∂Yau.lebesgueC n := by
      apply integral_congr_ae
      filter_upwards [hRepB,ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx hxb
      have hρ : (rho x : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (rho_pos hxb))
      have he := congrArg (fun z : X n => z j) hx
      change f x j = (rho x : ℂ)*w x j at he
      rw [he,mul_div_cancel_left₀ _ hρ]
    _ = ∫ x, (ψ x : ℂ)*(f x j/(rho x : ℂ)) ∂Yau.lebesgueC n :=
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
        rw [image_eq_zero_of_notMem_tsupport (fun hh => hx (hs hh))]
        simp)
    _ = _ := hWeak j ψ hψ hc hs

end Yau.LeafProofs.L21Aux
