import Yau.Proofs.P03ManifoldPoleStrictifier
import Yau.Proofs.P03FinitePoleWeights

open scoped Manifold Topology ContDiff Matrix ComplexOrder

noncomputable section

namespace Yau.NodeProofs.P03Aux

open Yau.LeafProofs.L22Aux

variable {n : ℕ} {M : ComplexManifold n} {ι : Type*} [Fintype ι]

/-- The multiplier is chosen once for the complete finite pole family,
before every regularization index and every original chart. -/
theorem exists_finitePoleWeight_strictifier (ψ : M.Carrier → ℝ) (hψ : IsSmoothStrictPsh ψ)
    (a : ι → M.Carrier) (b : ∀ i, SmoothBumpFunction 𝓘(ℝ, ComplexVector n) (a i))
    (c : ℝ) (hc : 0 ≤ c) :
    ∃ k : ℝ, 1 ≤ k ∧
      (∀ j : ℕ, IsSmoothStrictPsh (finitePoleWeight ψ k c a b j)) ∧
      ∀ j : ℕ, ∀ p : M.Carrier, ∀ z ∈ chartTarget p, ∀ v,
        complexLeviQuadratic (inChart p ψ) z v ≤
          complexLeviQuadratic (inChart p (finitePoleWeight ψ k c a b j)) z v := by
  classical
  have hex (i : ι) := exists_manifold_pole_strictifier ψ hψ (a i) (b i) c hc
  choose κ hκ hκbound using hex
  let k : ℝ := 1 + ∑ i, (κ i - 1)
  have hk : 1 ≤ k := by
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => sub_nonneg.mpr (hκ i)))
  have hdom (j : ℕ) (p : M.Carrier) (z : ComplexVector n) (hz : z ∈ chartTarget p)
      (v : ComplexVector n) :
      complexLeviQuadratic (inChart p ψ) z v ≤
        complexLeviQuadratic (inChart p (finitePoleWeight ψ k c a b j)) z v := by
    have hf : ContDiffAt ℝ 2 (inChart p ψ) z :=
      ((hψ.1 p).contDiffAt ((isOpen_extChartAt_target p).mem_nhds hz)).of_le (by simp)
    have hP (i : ι) : ContDiffAt ℝ 2
        (inChart p (manifoldCutoffPole c (b i) (poleEpsilon j))) z :=
      ((manifoldCutoffPole_smooth c (b i) (poleEpsilon_pos j) p).contDiffAt
        ((isOpen_extChartAt_target p).mem_nhds hz)).of_le (by simp)
    have hi (i : ι) : (1 - κ i) * complexLeviQuadratic (inChart p ψ) z v ≤
        complexLeviQuadratic (inChart p (manifoldCutoffPole c (b i) (poleEpsilon j))) z v := by
      have hb := hκbound i j p z hz v
      change complexLeviQuadratic (inChart p ψ) z v ≤
        complexLeviQuadratic (fun w => κ i * inChart p ψ w +
          inChart p (manifoldCutoffPole c (b i) (poleEpsilon j)) w) z v at hb
      rw [complexLeviQuadratic_add (contDiffAt_const.mul hf) (hP i),
        complexLeviQuadratic_const_mul hf] at hb
      nlinarith
    have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) => hi i)
    have he : (∑ i, (1 - κ i) * complexLeviQuadratic (inChart p ψ) z v) =
        (1 - k) * complexLeviQuadratic (inChart p ψ) z v := by
      rw [← Finset.sum_mul]
      congr 1
      dsimp only [k]
      simp only [Finset.sum_sub_distrib]
      ring
    rw [he] at hs
    change complexLeviQuadratic (inChart p ψ) z v ≤
      complexLeviQuadratic (fun w => k * inChart p ψ w +
        ∑ i, inChart p (manifoldCutoffPole c (b i) (poleEpsilon j)) w) z v
    rw [complexLeviQuadratic_add (contDiffAt_const.mul hf)
        (ContDiffAt.sum (fun i _ => hP i)),
      complexLeviQuadratic_const_mul hf,
      complexLeviQuadratic_finset_sum Finset.univ _ z v (fun i _ => hP i)]
    nlinarith
  refine ⟨k, hk, ?_, hdom⟩
  intro j
  refine ⟨finitePoleWeight_smooth ψ hψ.1 k c a b j, ?_⟩
  intro p
  have hf : ContDiffAt ℝ 2 (inChart p ψ) (chartPt p p) :=
    ((hψ.1 p).contDiffAt ((isOpen_extChartAt_target p).mem_nhds
      (mem_extChartAt_target p))).of_le (by simp)
  have hg : ContDiffAt ℝ 2 (inChart p (finitePoleWeight ψ k c a b j)) (chartPt p p) :=
    ((finitePoleWeight_smooth ψ hψ.1 k c a b j p).contDiffAt
      ((isOpen_extChartAt_target p).mem_nhds (mem_extChartAt_target p))).of_le (by simp)
  apply (leviC_posDef_iff hg).mpr
  intro v hv
  exact ((leviC_posDef_iff hf).mp (hψ.2 p) v hv).trans_le
    (hdom j p (chartPt p p) (mem_extChartAt_target p) v)

end Yau.NodeProofs.P03Aux
