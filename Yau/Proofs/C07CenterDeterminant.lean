import Yau.Proofs.Y03CenterFrame

/-! The determinant of the same centered chart transition is fixed by the volume clock. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter

noncomputable section

namespace Yau.Proofs.C07Aux

open Yau Yau.Blueprint Yau.Blueprint.Alignment
open Yau.Blueprint.Alignment.Y03Proof

variable {n : ℕ}

theorem frame_transition_det_norm (H₀ H₁ P₀ P₁ A : Herm n)
    (hH₀ : H₀.PosDef) (hH₁ : H₁.PosDef)
    (h₀ : P₀.conjTranspose * H₀ * P₀ = 1)
    (h₁ : P₁.conjTranspose * H₁ * P₁ = 1)
    (hchain : P₁ * A = P₀) (δ : ℝ)
    (hclock : Real.log (H₁.det.re / H₀.det.re) = -δ) :
    ‖A.det‖ = Real.exp (-δ / 2) := by
  have hquad : A.conjTranspose * A = P₀.conjTranspose * H₁ * P₀ := by
    calc
      A.conjTranspose * A = A.conjTranspose * (P₁.conjTranspose * H₁ * P₁) * A := by
        rw [h₁, Matrix.mul_one]
      _ = (P₁ * A).conjTranspose * H₁ * (P₁ * A) := by
        rw [Matrix.conjTranspose_mul]
        noncomm_ring
      _ = _ := by rw [hchain]
  have hdet₀ := congrArg (fun B : Herm n => ‖B.det‖) h₀
  have hdetA := congrArg (fun B : Herm n => ‖B.det‖) hquad
  simp only [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one,
    norm_mul, norm_star, norm_one] at hdet₀ hdetA
  have hH₀pos := (Complex.pos_iff.mp hH₀.det_pos).1
  have hH₁pos := (Complex.pos_iff.mp hH₁.det_pos).1
  have hH₀norm : ‖H₀.det‖ = H₀.det.re := (Complex.re_eq_norm.mpr hH₀.det_pos.le).symm
  have hH₁norm : ‖H₁.det‖ = H₁.det.re := (Complex.re_eq_norm.mpr hH₁.det_pos.le).symm
  have hsq : ‖A.det‖ ^ 2 = H₁.det.re / H₀.det.re := by
    apply (eq_div_iff hH₀pos.ne').mpr
    rw [← hH₀norm, ← hH₁norm]
    calc
      ‖A.det‖ ^ 2 * ‖H₀.det‖ = (‖P₀.det‖ * ‖H₁.det‖ * ‖P₀.det‖) * ‖H₀.det‖ := by
        rw [pow_two, hdetA]
      _ = (‖P₀.det‖ * ‖H₀.det‖ * ‖P₀.det‖) * ‖H₁.det‖ := by ring
      _ = ‖H₁.det‖ := by rw [hdet₀, one_mul]
  have hApos : 0 < ‖A.det‖ := by
    have hspos : 0 < ‖A.det‖ ^ 2 := by rw [hsq]; exact div_pos hH₁pos hH₀pos
    nlinarith [norm_nonneg A.det]
  have hlog := congrArg Real.log hsq
  rw [Real.log_pow, hclock] at hlog
  have hlogA : Real.log ‖A.det‖ = -δ / 2 := by norm_num at hlog; linarith
  rw [← hlogA, Real.exp_log hApos]

theorem transition_center_det_norm {X : KahlerManifold n} {o : Pt X}
    {h : Flow X} {U P ρ : STF X} (hflow : FlowStage X o h U P ρ)
    {Φ Ψ : ComplexVector n → Pt X} {F : ComplexVector n → ComplexVector n}
    {t u r R q c C c' C' : ℝ} (ht : 0 ≤ t) (hu : 0 ≤ u) (hq : 0 < q) (hR : 0 < R)
    (hΦ : UnitaryChart (h t) o Φ r c C)
    (hΨ : UnitaryChart (h u) o Ψ R c' C')
    (hF : DifferentiableOn ℂ F (Metric.ball 0 q)) (hFzero : F 0 = 0)
    (hgerm : ∀ᶠ z in 𝓝 0, Ψ (F z) = Φ z) :
    ‖LinearMap.det (centerDeriv F).toLinearMap‖ =
      Real.exp (-(ρ o u - ρ o t) / 2) := by
  have hgpos (k : HermitianField X.manifold) : (gMat k o).PosDef :=
    hMat_posDef k o (chartPt o o) (mem_extChartAt_target o)
  have hgdetpos (k : HermitianField X.manifold) : 0 < (gMat k o).det.re :=
    (Complex.pos_iff.mp (hgpos k).det_pos).1
  have hclock : Real.log ((gMat (h u) o).det.re / (gMat (h t) o).det.re) =
      -(ρ o u - ρ o t) := by
    rcases hflow.1 with ⟨_, _, _, _, _, _, _, _, hP, hρ, _⟩
    have hPt := hP o t ht
    have hPu := hP o u hu
    have hρt := (hρ o t ht).1
    have hρu := (hρ o u hu).1
    rw [Real.log_div (hgdetpos (h t)).ne' (hgdetpos X.metric.form).ne'] at hPt
    rw [Real.log_div (hgdetpos (h u)).ne' (hgdetpos X.metric.form).ne'] at hPu
    rw [Real.log_div (hgdetpos (h u)).ne' (hgdetpos (h t)).ne']
    linarith
  rw [← derivativeMatrix_det]
  exact frame_transition_det_norm (gMat (h t) o) (gMat (h u) o)
    (centerFrameMatrix o Φ) (centerFrameMatrix o Ψ) (derivativeMatrix F)
    (hgpos _) (hgpos _) (unitaryChart_centerFrame_gram hΦ)
    (unitaryChart_centerFrame_gram hΨ)
    (centerFrameMatrix_chain o hq hR hΨ.1.1 hF hFzero hgerm) _ hclock

end Yau.Proofs.C07Aux
