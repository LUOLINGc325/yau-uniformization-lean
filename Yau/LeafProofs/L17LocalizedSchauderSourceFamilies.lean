import Yau.LeafProofs.L17LocalizedSchauderFamilyBounds

open Set Metric
open scoped ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17LocalizedSchauderAux
open Yau.LeafProofs.L17Aux Yau.LeafProofs.L17HolderAux Yau.LeafProofs.L17SchauderAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

theorem unitValueFamily_data (P : UniformChartPartition g) (T : ℝ) (hT : 0 ≤ T)
    (v : P.centers → ComplexVector n × Time T → ℝ)
    (D : P.centers → ComplexVector n × Time T → D1 n)
    (H : P.centers → ComplexVector n × Time T → D2 n)
    (b : P.centers → ComplexVector n × Time T → ℝ)
    (hTrue : LocalTrueJets P T hT v D H b) {gamma F : ℝ}
    (hBounds : LocalScaledJetBounds P T gamma F v D H b) :
    UnitLocalJetData P T 2 gamma F (fun p t => unitValue P.radius (fun z => v p (z,t))) := by
  refine ⟨?_,?_,?_⟩
  · intro p t
    exact localUnitValue_contDiffOn_two P T hT v D H b hTrue p t
  · intro p t z hz j hj
    exact localUnitValue_two_jet_norm_le P T hT v D H b hTrue hBounds p t hz j hj
  · intro p t s z w hz hw j hj
    exact localUnitValue_two_jet_sub_norm_le P T hT v D H b hTrue hBounds p t s hz hw j hj

theorem unitTimeFamily_data (P : UniformChartPartition g) (T : ℝ) (hT : 0 ≤ T)
    (v : P.centers → ComplexVector n × Time T → ℝ)
    (D : P.centers → ComplexVector n × Time T → D1 n)
    (H : P.centers → ComplexVector n × Time T → D2 n)
    (b : P.centers → ComplexVector n × Time T → ℝ)
    (hTrue : LocalTrueJets P T hT v D H b) {gamma F : ℝ}
    (hBounds : LocalScaledJetBounds P T gamma F v D H b) :
    UnitLocalJetData P T 0 gamma F (fun p t z => b p (P.radius • z,t)) := by
  refine ⟨?_,?_,?_⟩
  · intro p t
    apply contDiffOn_zero.mpr
    have hScale : Continuous (fun z : ComplexVector n => (P.radius • z,t)) := by fun_prop
    exact ((hTrue.1 p).2.2.2).comp
      hScale.continuousOn
      (fun z hz => ⟨radius_smul_mem_ball_two P hz,mem_univ _⟩)
  · intro p t z hz j hj
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
    subst j
    simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] using
      (hBounds.1 p (P.radius • z,t) (radius_smul_mem_ball_two P hz)).2.2.2
  · intro p t s z w hz hw j hj
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
    subst j
    have hh := (hBounds.2 p (P.radius • z,t) (P.radius • w,s)
      (radius_smul_mem_ball_two P hz) (radius_smul_mem_ball_two P hw)).2.2.2
    rw [localScaledDistance_radius_eq P.radius_pos] at hh
    simpa only [norm_iteratedFDeriv_zero_sub,Real.norm_eq_abs] using hh

theorem cutoffUnitFamily_unitValue_eq (P : UniformChartPartition g) (hρone : P.radius ≤ 1)
    {T : ℝ} (v : P.centers → ComplexVector n × Time T → ℝ)
    (p : P.centers) (q : M.Carrier) (t : Time T) :
    cutoffUnitFamily P hρone (fun p t => unitValue P.radius (fun z => v p (z,t))) p q t =
      unitLocalizedTerm P T p q (v p) t :=
  (unitLocalizedTerm_eq_product P T hρone p q (v p) t).symm

end Yau.LeafProofs.L17LocalizedSchauderAux
