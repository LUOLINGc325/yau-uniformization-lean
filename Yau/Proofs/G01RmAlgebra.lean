import Yau.Proofs.G01Calculator

noncomputable section
open scoped Manifold Topology ContDiff Matrix
namespace Yau.NodeProofs.G01Aux
open Yau Yau.LeafProofs
variable {n : ℕ} {M : ComplexManifold n}

def realRmInChart (h : HermitianField M) (x : M.Carrier) (z : ComplexVector n)
    (U V W Z : ComplexVector n) : ℝ :=
  ∑ a, ∑ b, ∑ c, ∑ d, L12Aux.curvature4 h x z a b c d *
    realCoord U a * realCoord V b * realCoord W c * realCoord Z d

theorem paperRm_eq_realRmInChart (h : HermitianField M) (x : M.Carrier)
    (U V W Z : TangentVector M x) :
    paperRm h x U V W Z = realRmInChart h x (chartPt x x)
      (tangentCoords x x U) (tangentCoords x x V)
      (tangentCoords x x W) (tangentCoords x x Z) := by
  unfold paperRm realRmInChart
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.sum_comm]
  simp only [L12Aux.curvature4, Finset.sum_mul]

theorem realRmInChart_swap_first (h : HermitianField M) (x : M.Carrier)
    (z U V W Z : ComplexVector n) :
    realRmInChart h x z U V W Z = -realRmInChart h x z V U W Z := by
  unfold realRmInChart
  simp only [← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro d _
  rw [L12Aux.curvature4_swap_first h x z b a c d]
  ring

theorem paperRm_swap_first (h : HermitianField M) (x : M.Carrier)
    (U V W Z : TangentVector M x) :
    paperRm h x U V W Z = -paperRm h x V U W Z := by
  rw [paperRm_eq_realRmInChart, paperRm_eq_realRmInChart]
  exact realRmInChart_swap_first _ _ _ _ _ _ _

theorem paperRm_self_first (h : HermitianField M) (x : M.Carrier)
    (U W Z : TangentVector M x) : paperRm h x U U W Z = 0 := by
  have he := paperRm_swap_first h x U U W Z
  linarith

theorem hermitianNormSq_smul {V : Type*} [AddCommGroup V] [Module ℂ V]
    (h : HermitianInnerProduct V) (c : ℂ) (u : V) :
    hermitianNormSq h (c • u) = Complex.normSq c * hermitianNormSq h u := by
  simp only [hermitianNormSq, h.map_smul_left, h.map_smul_right]
  simp [Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
  ring

end Yau.NodeProofs.G01Aux
