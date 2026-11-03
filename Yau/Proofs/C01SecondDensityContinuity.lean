import Yau.Proofs.C01ParameterSecondIntegral

/-! The actual second parameter derivatives of a C2 scalar density
are continuous on its spatial slice, so their compact integrals are genuine. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.C01Aux

theorem second_parameter_density_continuousOn
    (F : ℝ × ℝ → ℝ) (I J : Set ℝ) (hI : IsOpen I) (hJ : IsOpen J)
    (hF : ContDiffOn ℝ 2 F (I ×ˢ J)) (a : ℝ) (ha : a ∈ I) :
    ContinuousOn (fun u => deriv (deriv (fun r => F (r, u))) a) J := by
  let G : ℝ × ℝ → ℝ := fun p => Parametric.parameterDerivative F p 1
  have hG : ContDiffOn ℝ 1 G (I ×ˢ J) :=
    (Parametric.parameterDerivative_contDiffOn hI hJ 1 hF).clm_apply contDiffOn_const
  let H : ℝ × ℝ → ℝ := fun p => Parametric.parameterDerivative G p 1
  have hH : ContDiffOn ℝ 0 H (I ×ˢ J) :=
    (Parametric.parameterDerivative_contDiffOn hI hJ 0 hG).clm_apply contDiffOn_const
  have hslice : ContinuousOn (fun u => H (a, u)) J :=
    hH.continuousOn.comp (continuousOn_const.prodMk continuousOn_id) (fun u hu => ⟨ha, hu⟩)
  apply hslice.congr
  intro u hu
  have hEq : (fun r => G (r, u)) =ᶠ[𝓝 a] deriv (fun r => F (r, u)) := by
    filter_upwards [hI.mem_nhds ha] with r hr
    have HD : DifferentiableAt ℝ F (r, u) :=
      (hF.contDiffAt ((hI.prod hJ).mem_nhds ⟨hr, hu⟩)).differentiableAt (by norm_num)
    exact (Parametric.parameterDerivative_hasFDerivAt F HD).hasDerivAt.deriv.symm
  have HDG : DifferentiableAt ℝ G (a, u) :=
    (hG.contDiffAt ((hI.prod hJ).mem_nhds ⟨ha, hu⟩)).differentiableAt_one
  have HG := (Parametric.parameterDerivative_hasFDerivAt G HDG).hasDerivAt.deriv
  exact hEq.deriv_eq.symm.trans HG

theorem second_parameter_density_integrableOn_unit
    (F : ℝ × ℝ → ℝ) (I J : Set ℝ) (hI : IsOpen I) (hJ : IsOpen J)
    (hunit : Set.Icc (0 : ℝ) 1 ⊆ J)
    (hF : ContDiffOn ℝ 2 F (I ×ˢ J)) (a : ℝ) (ha : a ∈ I) :
    IntegrableOn (fun u => deriv (deriv (fun r => F (r, u))) a) (Set.Icc (0 : ℝ) 1) :=
  ((second_parameter_density_continuousOn F I J hI hJ hF a ha).mono hunit).integrableOn_compact
    (isCompact_Icc (a := (0 : ℝ)) (b := 1))

end Yau.NodeProofs.C01Aux
