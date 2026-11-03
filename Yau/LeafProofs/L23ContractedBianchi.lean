import Yau.LeafProofs.L23CurvatureJetSymmetry
import Yau.LeafProofs.L23RicciCovariantTrace

/-! Exact contracted Bianchi identities for the original actual tensors. -/

noncomputable section
open scoped Topology ContDiff

namespace Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : ComplexManifold n}

theorem covariantD_rmTensor_divergence (h : HermitianField M) (hh : MetricSmooth h)
    (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c) (j k l : RIdx n) :
    (∑ a, ∑ b, (realMetricFn h c z)⁻¹ a b*
      covariantD h c (rmTensor h c) z ![a,b,j,k,l])=
      -covariantD h c (ricciTensor h c) z ![k,j,l]+
        covariantD h c (ricciTensor h c) z ![l,j,k] := by
  have hsum : (∑ a, ∑ b, (realMetricFn h c z)⁻¹ a b*
      (covariantD h c (rmTensor h c) z ![a,b,j,k,l]+
        covariantD h c (rmTensor h c) z ![k,a,l,j,b]-
          covariantD h c (rmTensor h c) z ![l,a,k,j,b]))=0 := by
    apply Finset.sum_eq_zero
    intro a _
    apply Finset.sum_eq_zero
    intro b _
    apply mul_eq_zero_of_right
    have hB := covariantD_rmTensor_secondBianchi h hh c hz a k l b j
    have h1 := covariantD_rmTensor_pair_swap h hh c hz a k l b j
    have h2 := covariantD_rmTensor_swap_first h hh c hz k l a b j
    have h3 := covariantD_rmTensor_swap_last h hh c hz k a l b j
    have h4 := covariantD_rmTensor_swap_last h hh c hz l a k b j
    linarith [hB,h1,h2,h3,h4]
  simp only [mul_add,mul_sub,Finset.sum_add_distrib,Finset.sum_sub_distrib] at hsum
  rw [←covariantD_ricciTensor_trace h hh c hz k l j,
    ←covariantD_ricciTensor_trace h hh c hz l k j,
    covariantD_ricciTensor_symm h hh c hz k l j,
    covariantD_ricciTensor_symm h hh c hz l k j] at hsum
  linarith [hsum]

theorem covariantD_rmTensor_contractedBianchi (h : HermitianField M) (hh : MetricSmooth h)
    (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c) (i j q : RIdx n) :
    (∑ a, ∑ b, (realMetricFn h c z)⁻¹ a b*
      covariantD h c (rmTensor h c) z ![a,i,b,j,q])=
      covariantD h c (ricciTensor h c) z ![j,i,q]-
        covariantD h c (ricciTensor h c) z ![q,i,j] := by
  have hneg : (∑ a, ∑ b, (realMetricFn h c z)⁻¹ a b*
      covariantD h c (rmTensor h c) z ![a,i,b,j,q])=
      -(∑ a, ∑ b, (realMetricFn h c z)⁻¹ a b*
        covariantD h c (rmTensor h c) z ![a,b,i,j,q]) := by
    simp only [covariantD_rmTensor_swap_first h hh c hz (i := i),mul_neg,
      Finset.sum_neg_distrib]
  rw [hneg,covariantD_rmTensor_divergence h hh c hz i j q]
  ring

end Yau.LeafProofs.L23Aux
