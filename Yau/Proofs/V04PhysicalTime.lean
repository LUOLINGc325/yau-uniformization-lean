import Yau.Blueprint.VariationContracts

/-! Relative time neighborhoods include physical time zero. These equalities
never assume an ordinary derivative through negative physical time. -/

open Filter Set
open scoped Topology
noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint

theorem physicalTime_derivWithin_Icc_eq_Ici (f : ℝ → ℝ) {t T : ℝ} (ht : t < T) :
    derivWithin f (Icc 0 T) t = derivWithin f (Ici 0) t := by
  simpa only [Ici_inter_Iic] using
    (derivWithin_inter (f := f) (s := Ici 0) (t := Iic T) (x := t) (Iic_mem_nhds ht))

theorem physicalTime_derivWithin_extended_interval (f : ℝ → ℝ)
    {t T extendedT : ℝ} (ht : t ∈ Icc 0 T) (hT : T < extendedT) :
    derivWithin f (Icc 0 extendedT) t = derivWithin f (Ici 0) t :=
  physicalTime_derivWithin_Icc_eq_Ici f (ht.2.trans_lt hT)

theorem physicalTime_derivWithin_extended_zero (f : ℝ → ℝ) {extendedT : ℝ}
    (hT : 0 < extendedT) :
    derivWithin f (Icc 0 extendedT) 0 = derivWithin f (Ici 0) 0 :=
  physicalTime_derivWithin_Icc_eq_Ici f hT

end Yau.Blueprint.V04Proof
