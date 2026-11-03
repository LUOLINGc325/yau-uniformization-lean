import Yau.Proofs.G01

/-! Conjugation and Kähler index symmetries of the actual Chern calculator. -/
noncomputable section
open Filter
open scoped Manifold Topology ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.P06Aux
open Yau Yau.LeafProofs Yau.NodeProofs.G01Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem chernInChart_star
    (h : HermitianField M) (hs : MetricSmooth h)
    (x : M.Carrier) (z : ComplexVector n) (hz : z ∈ chartTarget x)
    (i j k l : Fin n) :
    star (chernInChart h x z i j k l) = chernInChart h x z j i l k := by
  have hfun (a b : Fin n) : (fun w => star (hMat h x w a b)) = fun w => hMat h x w b a := by
    funext w
    exact (L12Aux.hMat_isHermitian h x w).apply b a
  have hw (a b q : Fin n) :
      star (wirt (fun w => hMat h x w a b) z (stdVec q)) =
        wirtBar (fun w => hMat h x w b a) z (stdVec q) := by
    rw [← L14Aux.wirtBar_star, hfun]
  have hwb (a b q : Fin n) :
      star (wirtBar (fun w => hMat h x w a b) z (stdVec q)) =
        wirt (fun w => hMat h x w b a) z (stdVec q) := by
    rw [← L14Aux.wirt_star, hfun]
  have hsecond :
      star (wirt (fun w => wirtBar (fun q => hMat h x q j i) w (stdVec l)) z (stdVec k)) =
        wirt (fun w => wirtBar (fun q => hMat h x q i j) w (stdVec k)) z (stdVec l) := by
    rw [← L14Aux.wirtBar_star]
    have he : (fun w => star (wirtBar (fun q => hMat h x q j i) w (stdVec l))) =
        fun w => wirt (fun q => hMat h x q i j) w (stdVec l) := by
      funext w
      rw [← L14Aux.wirt_star, hfun]
    rw [he]
    have hf : ContDiffAt ℝ 2 (fun w => hMat h x w i j) z :=
      ((L17Aux.hMat_contDiffOn_of_metricSmooth h hs x i j).contDiffAt
        ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).of_le (by simp)
    exact (L14Aux.wirt_wirtBar_comm _ z hf (stdVec k) (stdVec l)).symm
  have hi : (hMat h x z)⁻¹.IsHermitian := (L12Aux.hMat_posDef h x z hz).inv.isHermitian
  simp only [chernInChart, star_add, star_neg, star_sum, star_mul, hsecond, hw, hwb]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  rw [hi.apply p q]
  ring

theorem chernInChart_antiholomorphic_symm
    (h : HermitianField M) (hs : MetricSmooth h) (hk : KahlerClosed h)
    (x : M.Carrier) (z : ComplexVector n) (hz : z ∈ chartTarget x)
    (i j k l : Fin n) :
    chernInChart h x z i j k l = chernInChart h x z i l k j := by
  apply star_injective
  rw [chernInChart_star h hs x z hz, chernInChart_star h hs x z hz]
  exact chern_holomorphic_symm h hs hk x z hz j i l k

theorem chernInChart_pair_exchange
    (h : HermitianField M) (hs : MetricSmooth h) (hk : KahlerClosed h)
    (x : M.Carrier) (z : ComplexVector n) (hz : z ∈ chartTarget x)
    (i j k l : Fin n) :
    chernInChart h x z i j k l = chernInChart h x z k l i j := by
  rw [chern_holomorphic_symm h hs hk x z hz i j k l,
    chernInChart_antiholomorphic_symm h hs hk x z hz k j i l]

end Yau.NodeProofs.P06Aux
