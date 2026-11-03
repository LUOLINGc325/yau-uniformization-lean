import Yau.LeafProofs.L23ConnectionTime

/-! Direct time differentiation of the actual curvature coefficient formula. -/

noncomputable section
open scoped Topology ContDiff

namespace Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : ComplexManifold n}

def dotChristoffel (h : ℝ → HermitianField M) (c : M.Carrier)
    (z : ComplexVector n) (t : ℝ) (p i j : RIdx n) : ℝ :=
  deriv (fun s => christoffel (h s) c z p i j) t

theorem rDeriv_christoffel_time_hasDerivAt
    (h : ℝ → HermitianField M) (a b : ℝ) (hh : MetricFamilySmooth h (Set.Icc a b))
    (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (t : ℝ) (ht : t ∈ Set.Ioo a b) (p i j l : RIdx n) :
    HasDerivAt (fun s => rDeriv (fun w => christoffel (h s) c w p i j) z l)
      (rDeriv (fun w => dotChristoffel h c w t p i j) z l) t := by
  have hJ : ContDiffAt ℝ 2 (fun u : ComplexVector n × ℝ =>
      christoffel (h u.2) c u.1 p i j) (z,t) :=
    ((christoffelFamilySmooth_joint h a b hh c p i j).contDiffAt
      ((isOpen_flowChartDomain c a b).mem_nhds ⟨hz,ht⟩)).of_le (by simp)
  exact joint_spatial_time_hasDerivAt _ z t hJ l

theorem riemannCoeff_time_hasDerivAt
    (h : ℝ → HermitianField M) (a b : ℝ) (hh : MetricFamilySmooth h (Set.Icc a b))
    (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (t : ℝ) (ht : t ∈ Set.Ioo a b) (i j k l : RIdx n) :
    HasDerivAt (fun s => riemannCoeff (h s) c z i j k l)
      (rDeriv (fun w => dotChristoffel h c w t l j k) z i-
        rDeriv (fun w => dotChristoffel h c w t l i k) z j+
          ∑ p, ((dotChristoffel h c z t p j k*christoffel (h t) c z l i p+
            christoffel (h t) c z p j k*dotChristoffel h c z t l i p)-
              (dotChristoffel h c z t p i k*christoffel (h t) c z l j p+
                christoffel (h t) c z p i k*dotChristoffel h c z t l j p))) t := by
  have hΓ (p i j : RIdx n) :
      HasDerivAt (fun s => christoffel (h s) c z p i j)
        (dotChristoffel h c z t p i j) t :=
    (christoffel_time_differentiableAt h a b hh c hz t ht p i j).hasDerivAt
  have hD := ((rDeriv_christoffel_time_hasDerivAt h a b hh c hz t ht l j k i).sub
    (rDeriv_christoffel_time_hasDerivAt h a b hh c hz t ht l i k j)).add
      (HasDerivAt.fun_sum (u := Finset.univ) (fun p _ =>
        ((hΓ p j k).mul (hΓ l i p)).sub ((hΓ p i k).mul (hΓ l j p))))
  exact hD

theorem dotChristoffel_lower_symm (h : ℝ → HermitianField M) (c : M.Carrier)
    (z : ComplexVector n) (t : ℝ) (p i j : RIdx n) :
    dotChristoffel h c z t p i j=dotChristoffel h c z t p j i := by
  unfold dotChristoffel
  congr 1
  funext s
  exact L12Aux.christoffel_symm_lower (h s) c z p i j

end Yau.LeafProofs.L23Aux
