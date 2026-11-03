import Yau.LeafProofs.L23BianchiDifferentiated
import Yau.LeafProofs.L23DivergenceDifferentiated

/-! The actual rough Laplacian of Rm, with all curvature commutators
explicit and the second Ricci derivatives in the fixed chosen order. -/

noncomputable section
open scoped Topology ContDiff

namespace Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : ComplexManifold n}

theorem roughLap_rmTensor_secondRicci (h : HermitianField M) (hh : MetricSmooth h)
    (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c) (i j k l : RIdx n) :
    roughLap h c (rmTensor h c) z ![i,j,k,l]=
      -covariantD h c (covariantD h c (ricciTensor h c)) z ![i,k,j,l]+
        covariantD h c (covariantD h c (ricciTensor h c)) z ![i,l,j,k]+
          covariantD h c (covariantD h c (ricciTensor h c)) z ![j,k,i,l]-
            covariantD h c (covariantD h c (ricciTensor h c)) z ![j,l,i,k]+
              (∑ a, ∑ b, (realMetricFn h c z)⁻¹ a b*
                (curvatureAction h c z b i (rmTensor h c z) ![a,j,k,l]-
                  curvatureAction h c z b j (rmTensor h c z) ![a,i,k,l])) := by
  have hpoint (a b : RIdx n) :
      covariantD h c (covariantD h c (rmTensor h c)) z ![a,b,i,j,k,l]=
        covariantD h c (covariantD h c (rmTensor h c)) z ![i,a,b,j,k,l]-
          covariantD h c (covariantD h c (rmTensor h c)) z ![j,a,b,i,k,l]+
            (curvatureAction h c z a i (rmTensor h c z) ![b,j,k,l]-
              curvatureAction h c z a j (rmTensor h c z) ![b,i,k,l]) := by
    have hB := covariantD_twice_rmTensor_bianchi h hh c hz a b i j k l
    have hi := covariantD_commutator h hh c (rmTensor h c) (rmTensor_contDiffOn h hh c)
      hz a i ![b,j,k,l]
    have hj := covariantD_commutator h hh c (rmTensor h c) (rmTensor_contDiffOn h hh c)
      hz a j ![b,i,k,l]
    change covariantD h c (covariantD h c (rmTensor h c)) z ![a,i,b,j,k,l]-
      covariantD h c (covariantD h c (rmTensor h c)) z ![i,a,b,j,k,l]=
        curvatureAction h c z a i (rmTensor h c z) ![b,j,k,l] at hi
    change covariantD h c (covariantD h c (rmTensor h c)) z ![a,j,b,i,k,l]-
      covariantD h c (covariantD h c (rmTensor h c)) z ![j,a,b,i,k,l]=
        curvatureAction h c z a j (rmTensor h c z) ![b,i,k,l] at hj
    linarith [hB,hi,hj]
  have hc : (∑ a, ∑ b, (realMetricFn h c z)⁻¹ a b*
      (curvatureAction h c z a i (rmTensor h c z) ![b,j,k,l]-
        curvatureAction h c z a j (rmTensor h c z) ![b,i,k,l]))=
      ∑ a, ∑ b, (realMetricFn h c z)⁻¹ a b*
        (curvatureAction h c z b i (rmTensor h c z) ![a,j,k,l]-
          curvatureAction h c z b j (rmTensor h c z) ![a,i,k,l]) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [(L18Aux.realMetricFn_isSymm h c z).inv.apply b a]
  change (∑ a, ∑ b, (realMetricFn h c z)⁻¹ a b*
    covariantD h c (covariantD h c (rmTensor h c)) z ![a,b,i,j,k,l])=_
  simp_rw [hpoint,mul_add,mul_sub,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  have hd1 := covariantD_rmTensor_divergence_derivative h hh c hz i j k l
  have hd2 := covariantD_rmTensor_divergence_derivative h hh c hz j i k l
  have hc' := hc
  simp only [mul_sub,Finset.sum_sub_distrib] at hc'
  rw [hd1,hd2,hc']
  ring

end Yau.LeafProofs.L23Aux
