/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Topology.Order.Compact

/-!
# Order isomorphism from a strictly monotone continuous map on an interval

A strictly monotone continuous function on a closed real interval `[a, b]` restricts to an order
isomorphism onto its image `[f a, f b]`: Strictness supplies the order embedding, and continuity
together with the intermediate value theorem supplies surjectivity onto the closed interval.

## Main definitions

* `StrictMonoOn.icc_orderIso` — the packaged order isomorphism `Icc a b ≃o Icc (f a) (f b)`.

## Main statements

* `StrictMonoOn.icc_orderIso_apply_coe` — the underlying map of the isomorphism is `f`.

## Tags

order isomorphism, strictly monotone, interval, intermediate value theorem
-/

@[expose] public section

open Set

namespace StrictMonoOn

/-- A strictly monotone continuous function on `[a, b]` packaged as an order isomorphism onto its
image `[f a, f b]`. The strictness gives the order embedding; continuity plus the IVT gives
surjectivity onto the closed interval. -/
noncomputable def icc_orderIso {a b : ℝ} (hab : a ≤ b)
    {f : ℝ → ℝ} (h_mono : StrictMonoOn f (Icc a b))
    (h_cont : ContinuousOn f (Icc a b)) :
    Icc a b ≃o Icc (f a) (f b) :=
  let h_image : f '' Icc a b = Icc (f a) (f b) :=
    h_cont.image_Icc_of_monotoneOn hab h_mono.monotoneOn
  (h_mono.orderIso f (Icc a b)).trans (OrderIso.setCongr _ _ h_image)

@[simp] lemma icc_orderIso_apply_coe {a b : ℝ} (hab : a ≤ b)
    {f : ℝ → ℝ} (h_mono : StrictMonoOn f (Icc a b))
    (h_cont : ContinuousOn f (Icc a b)) (x : Icc a b) :
    ((h_mono.icc_orderIso hab h_cont x : Icc (f a) (f b)) : ℝ) = f (x : ℝ) := rfl

end StrictMonoOn
