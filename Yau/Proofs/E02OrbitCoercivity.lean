import Yau.Proofs.E02OrbitNormalization
import Yau.Proofs.E02UniformVerticalLower

open Matrix Filter Set
open scoped Topology Matrix ComplexOrder
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint

/-- The limit may be ANY point of the compact equality orbit. Its
normalizations suffice for a uniform vertical coefficient; no continuity
or boundedness of the actual Peano matrices is assumed. -/
theorem eventually_vertical_blocks_of_orbit_limit {n m : ℕ}
    (a : ComplexVector n × ℝ) (α : Fin m → ℝ) (hα : ∀ i, 0 < α i)
    (η₀ : Fin m → ComplexVector n) (B : Herm n) (hB : B.PosDef)
    (hGram₀ : weightedColumns α η₀*(weightedColumns α η₀)ᴴ = B⁻¹)
    (hq₀ : ∀ i, qform B (η₀ i) = 1) (θ w : ℝ) (hθ : θ ≤ 1) (hWeight : ∀ i, α i ≤ w)
    (Qseq : ℕ → ProductPoint n m) (Q₀ : ProductPoint n m)
    (hQLim : Tendsto Qseq atTop (𝓝 Q₀))
    (hOrbit : Q₀ ∈ contactOrbit a α B (rowProjector (weightedColumns α η₀)))
    (W : ℕ → Fin m → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (hBlocks : ∀ j i, ((W j i).toBlocks₂₂-columnLowerMatrix α θ (Qseq j).2.2 i).PosSemidef) :
    ∀ r : ℝ, 0 < r → ∀ᶠ j in atTop, ∀ i,
      ((W j i).toBlocks₂₂-((((1-θ)*(1-w)-r : ℝ) : ℂ) • B)).PosSemidef := by
  have hηCont : Continuous (fun Q : ProductPoint n m => Q.2.2) :=
    continuous_snd.comp continuous_snd
  have hηLim : Tendsto (fun j => (Qseq j).2.2) atTop (𝓝 Q₀.2.2) :=
    (hηCont.tendsto Q₀).comp hQLim
  have hq := contactOrbit_qform_one a α hα η₀ B hB hGram₀ hq₀ Q₀ hOrbit
  intro r hr
  have hLower := eventually_columnLowerMatrix_lower α θ w (fun j => (Qseq j).2.2)
    Q₀.2.2 B hB hηLim hOrbit.2.1 hq hθ hWeight hr
  filter_upwards [hLower] with j hj
  intro i
  have hh := (hBlocks j i).add (hj i)
  convert hh using 1 <;> abel

end Yau.NodeProofs.E02Aux
