import Yau.LeafProofs.L23RoughLapCurvature

/-! The exact quadratic curvature evolution of the original local Ricci
flow, with the project's explicit real-Laplacian normalization. -/

noncomputable section
open scoped Topology ContDiff Matrix

namespace Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : ComplexManifold n}

theorem riemannCoeff_raise_last (h : HermitianField M) (c : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget c) (i j k p : RIdx n) :
    riemannCoeff h c z i j k p=
      ∑ q, (realMetricFn h c z)⁻¹ p q*rmTensor h c z ![i,j,k,q] := by
  let G := realMetricFn h c z
  let V : RIdx n → ℝ := fun l => riemannCoeff h c z i j k l
  have hsym : Gᵀ=G := L18Aux.realMetricFn_isSymm h c z
  have hInv : G⁻¹*G=1 := Matrix.nonsing_inv_mul G
    (isUnit_iff_ne_zero.mpr (L12Aux.realMetricFn_posDef h c z hz).det_pos.ne')
  change V p=(G⁻¹*ᵥ(Gᵀ*ᵥV)) p
  rw [hsym,Matrix.mulVec_mulVec,hInv,Matrix.one_mulVec]

theorem rmTensor_evolution_four
    (h : ℝ → HermitianField M) (O : Set M.Carrier) (a b σ : ℝ) (hO : IsOpen O)
    (hflow : LocalRealRicciFlow h O (Set.Icc a b) σ)
    (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (hx : chartInv c z ∈ O) (t : ℝ) (ht : t ∈ Set.Ioo a b) (i j k l : RIdx n) :
    jetParabolicTensor h c 0 z t σ ![i,j,k,l]=
      σ*rmReaction (h t) c z ![i,j,k,l] := by
  have hh := metricFamilySmooth_slice h hflow.1 ⟨ht.1.le,ht.2.le⟩
  have htime := localRealRicciFlow_rmTensor_secondRicci_hasDerivAt
    h O a b σ hO hflow c hz hx t ht i j k l
  have hRc (v : Fin 2 → RIdx n) : ContDiffOn ℝ ∞
      (fun w => ricciTensor (h t) c w v) (chartTarget c) :=
    realRicciCoeff_contDiffOn (h t) hh c (v 0) (v 1)
  have hcomm := covariantD_commutator (h t) hh c (ricciTensor (h t) c) hRc hz i j ![k,l]
  change covariantD (h t) c (covariantD (h t) c (ricciTensor (h t) c)) z ![i,j,k,l]-
    covariantD (h t) c (covariantD (h t) c (ricciTensor (h t) c)) z ![j,i,k,l]=
      curvatureAction (h t) c z i j (ricciTensor (h t) c z) ![k,l] at hcomm
  have hcomm' : covariantD (h t) c (covariantD (h t) c (ricciTensor (h t) c)) z ![i,j,k,l]=
      covariantD (h t) c (covariantD (h t) c (ricciTensor (h t) c)) z ![j,i,k,l]+
        curvatureAction (h t) c z i j (ricciTensor (h t) c z) ![k,l] := by linarith [hcomm]
  have hloss : (∑ p, realRicciCoeff (h t) c z p l*riemannCoeff (h t) c z i j k p)=
      ∑ p, ∑ q, realRicciCoeff (h t) c z l p*(realMetricFn (h t) c z)⁻¹ p q*
        rmTensor (h t) c z ![i,j,k,q] := by
    apply Finset.sum_congr rfl
    intro p _
    rw [realRicciCoeff_symm (h t) hh c hz p l,riemannCoeff_raise_last (h t) c hz,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    ring
  change deriv (fun s => rmTensor (h s) c z ![i,j,k,l]) t-
    (σ/2)*roughLap (h t) c (rmTensor (h t) c) z ![i,j,k,l]=_
  rw [htime.deriv,roughLap_rmTensor_secondRicci (h t) hh c hz,
    hloss,hcomm']
  simp only [rmReaction]
  change _=σ*(-(∑ p, ∑ q, realRicciCoeff (h t) c z l p*(realMetricFn (h t) c z)⁻¹ p q*
    rmTensor (h t) c z ![i,j,k,q])-
      (1/2 : ℝ)*curvatureAction (h t) c z i j (ricciTensor (h t) c z) ![k,l]-
        (1/2 : ℝ)*(∑ a, ∑ b, (realMetricFn (h t) c z)⁻¹ a b*
          (curvatureAction (h t) c z b i (rmTensor (h t) c z) ![a,j,k,l]-
            curvatureAction (h t) c z b j (rmTensor (h t) c z) ![a,i,k,l])))
  ring

theorem fixedChartRmEvolution (n : ℕ) : FixedChartRmEvolutionGap n := by
  intro M h O a b σ hO hab hσ hflow c z hz hx t ht v
  have hv : v=![v 0,v 1,v 2,v 3] := by funext s; fin_cases s <;> rfl
  rw [hv]
  exact rmTensor_evolution_four h O a b σ hO hflow c hz hx t ht (v 0) (v 1) (v 2) (v 3)

end Yau.LeafProofs.L23Aux
