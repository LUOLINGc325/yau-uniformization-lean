import Yau.Proofs.P04PoleAnnulusBounds
import Yau.Proofs.P04CompactLeviDomination
import Yau.LeafProofs.L17RicciNaturality

noncomputable section
open Set
open scoped Topology ContDiff Manifold Matrix ComplexOrder

namespace Yau.Proofs.P04Aux
open Yau Yau.LeafProofs
variable {n : ℕ} {M : ComplexManifold n}

/-- The compact annulus selects ONE scalar for all regularization parameters.
The chart positivity input is supplied by the genuine strict psh weight. -/
theorem pole_annulus_uniform_domination (p : M.Carrier) {χ : ComplexVector n → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (c : ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (hs : poleAnnulus (chartPt p p) ρ ⊆ chartTarget p)
    {ψ : M.Carrier → ℝ} (hψ : SmoothFn ψ)
    (hψpos : ∀ z ∈ chartTarget p, (leviC (inChart p ψ) z).PosDef) :
    ∃ k : ℝ, 1 ≤ k ∧ ∀ ε ∈ Icc (0 : ℝ) ρ, ∀ z ∈ poleAnnulus (chartPt p p) ρ,
      (((k-1 : ℝ) : ℂ) • leviC (inChart p ψ) z+
        leviC (regularizedPoleModel χ (chartPt p p) c ε) z).PosSemidef := by
  let z₀ := chartPt p p
  let K : Set (ℝ × ComplexVector n) := Icc (0 : ℝ) ρ ×ˢ poleAnnulus z₀ ρ
  have hK : IsCompact K := isCompact_Icc.prod (poleAnnulus_isCompact z₀ ρ)
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let A : K → Matrix (Fin n) (Fin n) ℂ := fun q => leviC (inChart p ψ) q.1.2
  let E : K → Matrix (Fin n) (Fin n) ℂ :=
    fun q => leviC (regularizedPoleModel χ z₀ c q.1.1) q.1.2
  have hA : Continuous A := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact (L14Aux.leviC_contDiffOn ψ hψ p i j).continuousOn.comp_continuous
      (continuous_snd.comp continuous_subtype_val) (fun q => hs q.2.2)
  let U : Set (ℝ × ComplexVector n) := {q | q.2 ≠ z₀}
  have hU : IsOpen U := isOpen_ne_fun continuous_snd continuous_const
  have hF : ContDiffOn ℝ ∞
      (fun q : ℝ × ComplexVector n => regularizedPoleModel χ z₀ c q.1 q.2) U := by
    intro q hq
    exact (regularizedPoleModel_joint_off_center hχ z₀ c q hq).contDiffWithinAt
  have hKU : K ⊆ U := fun q hq => poleAnnulus_ne_center z₀ hρ hq.2
  have hE : Continuous E :=
    continuousOn_iff_continuous_domRestrict.mp ((joint_leviC_continuousOn hU hF).mono hKU)
  have hpos (q : K) : (A q).PosDef := hψpos q.1.2 (hs q.2.2)
  have hHerm (q : K) : (E q).IsHermitian := by
    have hf : ContDiffAt ℝ 2
        (fun a : ℝ × ComplexVector n => regularizedPoleModel χ z₀ c a.1 a.2) q.1 :=
      (regularizedPoleModel_joint_off_center hχ z₀ c q.1 (hKU q.2)).of_le (by simp)
    exact L22Aux.leviC_isHermitian (hf.comp q.1.2 (contDiffAt_const.prodMk contDiffAt_id))
  obtain ⟨k,hk,hdom⟩ := compact_posDef_dominates_error A E hA hE hpos hHerm
  exact ⟨k,hk,fun ε hε z hz => hdom ⟨(ε,z),hε,hz⟩⟩

end Yau.Proofs.P04Aux
