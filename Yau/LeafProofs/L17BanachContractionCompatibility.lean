import Yau.LeafProofs.L17BanachContractionStability

noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BanachContractionAux

variable {Xh Yh Xl Yl : Type*}
    [NormedAddCommGroup Xh] [NormedSpace ℝ Xh] [NormedAddCommGroup Yh] [NormedSpace ℝ Yh]
    [NormedAddCommGroup Xl] [NormedSpace ℝ Xl] [NormedAddCommGroup Yl] [NormedSpace ℝ Yl]

theorem ball_equations_compatible (J : Xh →L[ℝ] Xl) (K : Yh →L[ℝ] Yl)
    (eh : Xh ≃L[ℝ] Yh) (el : Xl ≃L[ℝ] Yl) (fh : Yh) (fl : Yl)
    (Nh : Xh → Yh) (Nl : Xl → Yl) {rh rl Ll : ℝ}
    (hLip : ∀ u v, ‖u‖ ≤ rl → ‖v‖ ≤ rl → ‖Nl u-Nl v‖ ≤ Ll*‖u-v‖)
    (hSmall : ‖el.symm.toContinuousLinearMap‖*Ll ≤ 1/2)
    (hRadius : ‖J‖*rh ≤ rl) (hf : fl=K fh)
    (hN : ∀ u, K (Nh u)=Nl (J u)) (he : ∀ u, K (eh u)=el (J u))
    {uh : Xh} {ul : Xl} (huh : ‖uh‖ ≤ rh) (hul : ‖ul‖ ≤ rl)
    (heqh : eh uh=fh+Nh uh) (heql : el ul=fl+Nl ul) : J uh=ul := by
  have hJ : ‖J uh‖ ≤ rl := calc
    ‖J uh‖ ≤ ‖J‖*‖uh‖ := J.le_opNorm _
    _ ≤ ‖J‖*rh := mul_le_mul_of_nonneg_left huh (norm_nonneg _)
    _ ≤ rl := hRadius
  have heqJ : el (J uh)=fl+Nl (J uh) := by
    rw [← he,heqh,map_add,hN,← hf]
  exact ball_equation_unique el fl Nl hLip hSmall hJ hul heqJ heql

variable [CompleteSpace Xh] [CompleteSpace Xl]

theorem ballSolution_compatible (J : Xh →L[ℝ] Xl) (K : Yh →L[ℝ] Yl)
    (eh : Xh ≃L[ℝ] Yh) (el : Xl ≃L[ℝ] Yl) (fh : Yh) (fl : Yl)
    (Nh : Xh → Yh) (Nl : Xl → Yl) (rh Lh rl Ll : ℝ)
    (hrh : 0 ≤ rh) (hrl : 0 ≤ rl)
    (hLiph : ∀ u v, ‖u‖ ≤ rh → ‖v‖ ≤ rh → ‖Nh u-Nh v‖ ≤ Lh*‖u-v‖)
    (hLipl : ∀ u v, ‖u‖ ≤ rl → ‖v‖ ≤ rl → ‖Nl u-Nl v‖ ≤ Ll*‖u-v‖)
    (hSmallh : ‖eh.symm.toContinuousLinearMap‖*Lh ≤ 1/2)
    (hSmalll : ‖el.symm.toContinuousLinearMap‖*Ll ≤ 1/2)
    (hZeroh : ‖eh.symm (fh+Nh 0)‖ ≤ rh/2) (hZerol : ‖el.symm (fl+Nl 0)‖ ≤ rl/2)
    (hRadius : ‖J‖*rh ≤ rl) (hf : fl=K fh)
    (hN : ∀ u, K (Nh u)=Nl (J u)) (he : ∀ u, K (eh u)=el (J u)) :
    J (ballSolution eh fh Nh rh Lh hrh hLiph hSmallh hZeroh)=
      ballSolution el fl Nl rl Ll hrl hLipl hSmalll hZerol :=
  ball_equations_compatible J K eh el fh fl Nh Nl hLipl hSmalll hRadius hf hN he
    (ballSolution_mem eh fh Nh rh Lh hrh hLiph hSmallh hZeroh)
    (ballSolution_mem el fl Nl rl Ll hrl hLipl hSmalll hZerol)
    (ballSolution_equation eh fh Nh rh Lh hrh hLiph hSmallh hZeroh)
    (ballSolution_equation el fl Nl rl Ll hrl hLipl hSmalll hZerol)

end Yau.LeafProofs.L17BanachContractionAux
