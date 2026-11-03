import Yau.LeafProofs.L17LocalScalarAssemblyLinearity

open Set Metric
open scoped Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17LocalScalarAssemblyAux
open L17Aux L17HolderAux L17SchauderAux L17LocalizedSchauderAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

theorem scalarAssemblyTerm_of_compatible (P : UniformChartPartition g) {T γ : ℝ}
    (u : LocalHolderSpace ℝ P T γ) (F : Cylinder M T → ℝ)
    (hF : ∀ (p : P.centers) (zt : ChartCylinder P T), localFun ℝ u ⟨p,zt⟩=F (chartPoint P T p zt))
    (p : P.centers) (q : Cylinder M T) : scalarAssemblyTerm P u p q=P.weight p q.1*F q := by
  by_cases hw : P.weight p q.1=0
  · unfold scalarAssemblyTerm
    split_ifs <;> simp only [hw,zero_mul]
  · obtain ⟨hx,hz⟩ := weight_nonzero_target_inverse_ball P p hw
    rw [scalarAssemblyTerm,dite_eq_left hx,dite_eq_left hz,hF]
    simp only [chartPoint,(P.charts.chart p).right_inv hx,Prod.mk.eta]

theorem scalarAssemblyFunction_of_compatible (P : UniformChartPartition g) {T γ : ℝ}
    (u : LocalHolderSpace ℝ P T γ) (F : Cylinder M T → ℝ)
    (hF : ∀ (p : P.centers) (zt : ChartCylinder P T), localFun ℝ u ⟨p,zt⟩=F (chartPoint P T p zt)) :
    scalarAssemblyFunction P u=F := by
  funext q
  calc
    scalarAssemblyFunction P u q=(∑ᶠ p : P.centers, P.weight p q.1*F q) := by
      apply finsum_congr
      intro p
      exact scalarAssemblyTerm_of_compatible P u F hF p q
    _ = (∑ᶠ p : P.centers, P.weight p q.1)*F q := by
      simpa only [smul_eq_mul] using (finsum_smul (fun p : P.centers => P.weight p q.1) (F q)).symm
    _ = F q := by rw [P.weight_sum,one_mul]

theorem scalarAssemblyFunction_of_same_values (P : UniformChartPartition g) {T α β : ℝ}
    (u : LocalHolderSpace ℝ P T α) (v : LocalHolderSpace ℝ P T β)
    (h : ∀ (p : P.centers) (zt : ChartCylinder P T), localFun ℝ u ⟨p,zt⟩=localFun ℝ v ⟨p,zt⟩) :
    scalarAssemblyFunction P u=scalarAssemblyFunction P v := by
  funext q
  apply finsum_congr
  intro p
  unfold scalarAssemblyTerm
  split_ifs <;> simp only [h]

end Yau.LeafProofs.L17LocalScalarAssemblyAux
