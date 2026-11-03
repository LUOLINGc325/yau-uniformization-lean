import Yau.Proofs.C01ScalarParameterIntegral

/-! Second derivatives of a genuine C2 compact scalar integral are
the integrals of the genuine second slice derivatives. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.C01Aux

theorem scalar_unitIntegral_second_derivative
    (F : ℝ × ℝ → ℝ) (I J : Set ℝ) (hI : IsOpen I) (hJ : IsOpen J)
    (hunit : Set.Icc (0 : ℝ) 1 ⊆ J) (hF : ContDiffOn ℝ 2 F (I ×ˢ J))
    (a : ℝ) (ha : a ∈ I) :
    deriv (deriv (fun r => ∫ u in Set.Icc (0 : ℝ) 1, F (r, u))) a =
      ∫ u in Set.Icc (0 : ℝ) 1, deriv (deriv (fun r => F (r, u))) a := by
  let G : ℝ × ℝ → ℝ := fun p => Parametric.parameterDerivative F p 1
  have hG : ContDiffOn ℝ 1 G (I ×ˢ J) :=
    (Parametric.parameterDerivative_contDiffOn hI hJ 1 hF).clm_apply contDiffOn_const
  have hfirst (r : ℝ) (hr : r ∈ I) (u : ℝ) (hu : u ∈ J) :
      HasDerivAt (fun s => F (s, u)) (G (r, u)) r := by
    have HD : DifferentiableAt ℝ F (r, u) :=
      (hF.contDiffAt ((hI.prod hJ).mem_nhds ⟨hr, hu⟩)).differentiableAt (by norm_num)
    exact (Parametric.parameterDerivative_hasFDerivAt F HD).hasDerivAt
  have hIntFirst (r : ℝ) (hr : r ∈ I) :
      deriv (fun s => ∫ u in Set.Icc (0 : ℝ) 1, F (s, u)) r =
        ∫ u in Set.Icc (0 : ℝ) 1, G (r, u) :=
    (scalar_unitIntegral_hasDerivAt F I J hI hJ hunit (hF.of_le (by norm_num)) r hr
      (fun u => G (r, u)) (fun u hu => hfirst r hr u (hunit hu))).deriv
  have heq : deriv (fun r => ∫ u in Set.Icc (0 : ℝ) 1, F (r, u)) =ᶠ[𝓝 a]
      (fun r => ∫ u in Set.Icc (0 : ℝ) 1, G (r, u)) := by
    filter_upwards [hI.mem_nhds ha] with r hr
    exact hIntFirst r hr
  rw [heq.deriv_eq]
  have hsecond (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
      HasDerivAt (fun r => G (r, u)) (deriv (deriv (fun r => F (r, u))) a) a := by
    have HG : ContDiffAt ℝ 1 (fun r => G (r, u)) a :=
      (hG.contDiffAt ((hI.prod hJ).mem_nhds ⟨ha, hunit hu⟩)).comp a
        (contDiffAt_id.prodMk contDiffAt_const)
    have HD := HG.differentiableAt_one.hasDerivAt
    have hEq : (fun r => G (r, u)) =ᶠ[𝓝 a] (deriv (fun r => F (r, u))) := by
      filter_upwards [hI.mem_nhds ha] with r hr
      exact (hfirst r hr u (hunit hu)).deriv.symm
    rw [hEq.deriv_eq] at HD
    exact HD
  exact (scalar_unitIntegral_hasDerivAt G I J hI hJ hunit hG a ha
    (fun u => deriv (deriv (fun r => F (r, u))) a) hsecond).deriv

end Yau.NodeProofs.C01Aux
