import Yau.LeafProofs.L21WeightedDomainsLocalTests

open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

def weightedRealCompactTest (ψ : X n → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hcψ : HasCompactSupport ψ) (hsψ : tsupport ψ ⊆ Metric.ball 0 1) :
    CompactTest (Metric.ball (0 : X n) 1) :=
  ⟨fun x => (ψ x : ℂ),Complex.ofRealCLM.contDiff.comp hψ,
    hcψ.comp_left Complex.ofReal_zero,(tsupport_comp_subset Complex.ofReal_zero ψ).trans hsψ⟩

theorem weightedRowTranspose_eq_divergence {α β ι : Type*} [Fintype α] [Fintype ι]
    (v : ι → X n) (a : β → α → ι → X n → ℂ) (b : β → α → X n → ℂ)
    (ha : ∀ r c i, ContDiffOn ℝ ∞ (a r c i) (Metric.ball 0 1)) (r : β) (c : α)
    (ψ : CompactTest (Metric.ball (0 : X n) 1)) {x : X n} (hx : x ∈ Metric.ball 0 1) :
    weightedRowTranspose v a b r c ψ x =
      -(∑ i, fderiv ℝ (fun y => a r c i y*ψ y) x (v i))+b r c x*ψ x := by
  unfold weightedRowTranspose
  congr 2
  apply Finset.sum_congr rfl
  intro i hi
  rw [fderiv_fun_mul (((ha r c i).contDiffAt (Metric.isOpen_ball.mem_nhds hx)).differentiableAt (by simp))
    (ψ.property.1.differentiable (by simp) x)]
  simp only [_root_.add_apply,_root_.smul_apply,smul_eq_mul]
  ring

theorem weightedTTranspose_rhoInverse_real
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A (Metric.ball 0 1))
    (j : Fin n) (ψ : X n → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hcψ : HasCompactSupport ψ) (hsψ : tsupport ψ ⊆ Metric.ball 0 1) (x : X n) :
    weightedRowTranspose Yau.realVec (weightedTPrincipal A) (fun _ _ _ => 0) j ()
      (weightedRhoInverseTest (weightedRealCompactTest ψ hψ hcψ hsψ)) x = transposeRow A j ψ x := by
  let ψC := weightedRealCompactTest ψ hψ hcψ hsψ
  by_cases hx : x ∈ Metric.ball (0 : X n) 1
  · rw [weightedRowTranspose_eq_divergence Yau.realVec (weightedTPrincipal A) (fun _ _ _ => 0)
      (weightedTPrincipal_smooth hA) j () (weightedRhoInverseTest ψC) hx]
    simp only [zero_mul,add_zero]
    simp_rw [weightedTPrincipal_mul_rhoInverseTest]
    unfold transposeRow
    congr 1
    apply Finset.sum_congr rfl
    intro a ha
    rw [fderiv_fun_mul (((dbarRealCoefficient_smoothOn hA j a).contDiffAt
      (Metric.isOpen_ball.mem_nhds hx)).differentiableAt (by simp)) (ψC.property.1.differentiable (by simp) x)]
    simp only [_root_.add_apply,_root_.smul_apply,smul_eq_mul,ψC,weightedRealCompactTest,
      fderiv_ofReal_apply (hψ.differentiable (by simp) x)]
    ring
  · have hn : x ∉ tsupport (weightedRhoInverseTest ψC) :=
      fun hh => hx ((weightedRhoInverseTest ψC).property.2.2 hh)
    have hzero := image_eq_zero_of_notMem_tsupport (show x ∉ tsupport
      (weightedRowTranspose Yau.realVec (weightedTPrincipal A) (fun _ _ _ => 0) j ()
        (weightedRhoInverseTest ψC)) from fun hh => hn (weightedRowTranspose_tsupport_subset _ _ _ _ _ _ hh))
    have hnψ : x ∉ tsupport ψ := fun hh => hx (hsψ hh)
    rw [hzero]
    simp only [transposeRow,image_eq_zero_of_notMem_tsupport hnψ,
      fderiv_of_notMem_tsupport ℝ hnψ,_root_.zero_apply,Complex.ofReal_zero,
      mul_zero,add_zero,Finset.sum_const_zero,neg_zero]

theorem weightedMaximalT_graph_unweighted (K : ℝ) (hK : 0 ≤ K)
    (A : X n → Matrix (Fin n) (Fin n) ℂ) (hA : MatrixSmoothOn A (Metric.ball 0 1))
    (u : WeightedScalar n K) (f : WeightedOneForm n K) :
    (u,f) ∈ (weightedMaximalT K hK A hA).graph ↔
      ∀ j (ψ : CompactTest (Metric.ball (0 : X n) 1)),
        (∫ x, ψ x*f x j ∂Yau.lebesgueC n) =
          ∫ x, weightedRowTranspose Yau.realVec (weightedTPrincipal A) (fun _ _ _ => 0) j () ψ x*u x
            ∂Yau.lebesgueC n := by
  unfold weightedMaximalT
  rw [weightedMaximalRows_graph _ _ _ _ _ _ _ _ _ (weightedField_eq_zero_of_projections K),
    weightedRowsGraph_mem_iff]
  simp only [weightedField_compactFunctional_apply]
  simp only [Fintype.sum_unique,ContinuousLinearMap.id_apply,weightedCompactFunctional_apply]
  rfl


/-- The maximal weighted equation has the exact original unweighted
Dbar distribution meaning after division by the genuinely positive rho. -/
theorem weightedMaximalT_graph_dbarWeakOn (K : ℝ) (hK : 0 ≤ K)
    (A : X n → Matrix (Fin n) (Fin n) ℂ) (hA : MatrixSmoothOn A (Metric.ball 0 1))
    (u : WeightedScalar n K) (f : WeightedOneForm n K)
    (hGraph : (u,f) ∈ (weightedMaximalT K hK A hA).graph) :
    DbarWeakOn A (u : X n → ℂ) (fun x j => f x j/(rho x : ℂ)) (Metric.ball 0 1) := by
  intro j ψ hψ hcψ hsψ
  have he := (weightedMaximalT_graph_unweighted K hK A hA u f).mp hGraph j
    (weightedRhoInverseTest (weightedRealCompactTest ψ hψ hcψ hsψ))
  simp_rw [weightedTTranspose_rhoInverse_real hA j ψ hψ hcψ hsψ] at he
  calc
    _ = ∫ x, weightedRhoInverseTest (weightedRealCompactTest ψ hψ hcψ hsψ) x*f x j
        ∂Yau.lebesgueC n := by
      apply integral_congr_ae
      filter_upwards [] with x
      change (ψ x : ℂ)*(f x j/(rho x : ℂ)) = ((((rho x)⁻¹ : ℝ) : ℂ)*(ψ x : ℂ))*f x j
      rw [Complex.ofReal_inv,div_eq_mul_inv]
      ring
    _ = _ := he
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact mul_comm _ _

theorem weightedMaximalT_dbarWeakOn (K : ℝ) (hK : 0 ≤ K)
    (A : X n → Matrix (Fin n) (Fin n) ℂ) (hA : MatrixSmoothOn A (Metric.ball 0 1))
    (u : (weightedMaximalT K hK A hA).domain) :
    DbarWeakOn A ((u : WeightedScalar n K) : X n → ℂ)
      (fun x j => (weightedMaximalT K hK A hA u) x j/(rho x : ℂ)) (Metric.ball 0 1) :=
  weightedMaximalT_graph_dbarWeakOn K hK A hA _ _ ((weightedMaximalT K hK A hA).mem_graph u)


theorem weightedOneForm_div_rho_locallyL2On (K : ℝ) (f : WeightedOneForm n K) (j : Fin n) :
    LocallyL2On (fun x => f x j/(rho x : ℂ)) (Metric.ball 0 1) := by
  intro S hS hSB
  have hc : ContinuousOn (fun x : X n => (((rho x)⁻¹ : ℝ) : ℂ)) (Metric.ball 0 1) :=
    (Complex.ofRealCLM.contDiff.comp_contDiffOn
      (contDiff_rho.contDiffOn.inv (fun x hx => (rho_pos hx).ne'))).continuousOn
  have hh := Yau.LeafProofs.L14Aux.memLp_continuousOn_mul_compact S hS _ _
    (hc.mono hSB) (weightedOneForm_component_locallyL2On K f j S hS hSB)
  convert hh using 1
  funext x
  rw [Complex.ofReal_inv,div_eq_mul_inv]
  exact mul_comm _ _

end Yau.LeafProofs.L21Aux
